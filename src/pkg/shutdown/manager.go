package shutdown

import (
	"context"
	"errors"
	"fmt"
	"os"
	"os/signal"
	"sync"
	"syscall"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// Manager 统一的优雅关闭管理器
// 支持分阶段关闭，确保资源正确释放
type Manager struct {
	mu         sync.Mutex
	shutdowns  []ShutdownFunc
	stages     map[string][]ShutdownFunc
	order      []string // 关闭顺序
	timeout    time.Duration
	tracer     trace.Tracer
	signalChan chan os.Signal
	shutdownCh chan struct{}
	once       sync.Once
}

// ShutdownFunc 关闭函数类型
type ShutdownFunc func(context.Context) error

// NewManager 创建关闭管理器
func NewManager(timeout time.Duration) *Manager {
	return &Manager{
		shutdowns:  make([]ShutdownFunc, 0),
		stages:     make(map[string][]ShutdownFunc),
		order:      make([]string, 0),
		timeout:    timeout,
		tracer:     otel.Tracer("shutdown/manager"),
		signalChan: make(chan os.Signal, 1),
		shutdownCh: make(chan struct{}),
	}
}

// Register 注册关闭函数（LIFO 顺序）
func (m *Manager) Register(fn ShutdownFunc) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.shutdowns = append(m.shutdowns, fn)
}

// RegisterStage 注册分阶段关闭
// 阶段按注册顺序执行，同一阶段内的函数并发执行
func (m *Manager) RegisterStage(stage string, fn ShutdownFunc) {
	m.mu.Lock()
	defer m.mu.Unlock()

	if _, exists := m.stages[stage]; !exists {
		m.order = append(m.order, stage)
		m.stages[stage] = make([]ShutdownFunc, 0)
	}
	m.stages[stage] = append(m.stages[stage], fn)
}

// ListenSignals 监听系统信号
func (m *Manager) ListenSignals(signals ...os.Signal) {
	if len(signals) == 0 {
		// 默认信号
		signals = []os.Signal{
			syscall.SIGINT,  // Ctrl+C
			syscall.SIGTERM, // kill
		}
	}

	signal.Notify(m.signalChan, signals...)

	go func() {
		sig := <-m.signalChan
		fmt.Printf("\nReceived signal: %v, initiating graceful shutdown...\n", sig)
		m.Shutdown()
	}()
}

// Shutdown 执行优雅关闭
func (m *Manager) Shutdown() error {
	var shutdownErr error
	m.once.Do(func() {
		close(m.shutdownCh)

		ctx, cancel := context.WithTimeout(context.Background(), m.timeout)
		defer cancel()

		ctx, span := m.tracer.Start(ctx, "shutdown.execute",
			trace.WithAttributes(
				attribute.Int64("timeout.seconds", int64(m.timeout.Seconds())),
			),
		)
		defer span.End()

		// 分阶段关闭
		if len(m.stages) > 0 {
			shutdownErr = m.shutdownStages(ctx, span)
		} else {
			// 简单 LIFO 关闭
			shutdownErr = m.shutdownSimple(ctx, span)
		}

		if shutdownErr != nil {
			span.RecordError(shutdownErr)
		}
	})
	return shutdownErr
}

// shutdownStages 分阶段关闭
func (m *Manager) shutdownStages(ctx context.Context, parentSpan trace.Span) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	var allErrors []error

	for _, stage := range m.order {
		stageCtx, stageSpan := m.tracer.Start(ctx, fmt.Sprintf("shutdown.stage.%s", stage),
			trace.WithAttributes(
				attribute.String("stage", stage),
				attribute.Int("functions.count", len(m.stages[stage])),
			),
		)

		fmt.Printf("Shutting down stage: %s (%d functions)\n", stage, len(m.stages[stage]))
		parentSpan.AddEvent(fmt.Sprintf("stage.%s.start", stage))

		// 并发执行同一阶段的所有关闭函数
		errCh := make(chan error, len(m.stages[stage]))
		var wg sync.WaitGroup

		for _, fn := range m.stages[stage] {
			wg.Add(1)
			go func(shutdownFn ShutdownFunc) {
				defer wg.Done()
				if err := shutdownFn(stageCtx); err != nil {
					errCh <- err
				}
			}(fn)
		}

		// 等待阶段完成
		doneCh := make(chan struct{})
		go func() {
			wg.Wait()
			close(doneCh)
		}()

		select {
		case <-doneCh:
			stageSpan.AddEvent("stage.completed")
		case <-stageCtx.Done():
			stageSpan.AddEvent("stage.timeout")
			allErrors = append(allErrors, fmt.Errorf("stage %s timeout", stage))
			// 超时也要等待所有 goroutine 完成
			<-doneCh
		}

		close(errCh)
		for err := range errCh {
			stageSpan.RecordError(err)
			allErrors = append(allErrors, err)
		}

		stageSpan.End()
		parentSpan.AddEvent(fmt.Sprintf("stage.%s.end", stage))
	}

	if len(allErrors) > 0 {
		return errors.Join(allErrors...)
	}
	return nil
}

// shutdownSimple 简单 LIFO 关闭
func (m *Manager) shutdownSimple(ctx context.Context, _ trace.Span) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	var allErrors []error

	// LIFO: 反向遍历
	for i := len(m.shutdowns) - 1; i >= 0; i-- {
		shutdownCtx, span := m.tracer.Start(ctx, fmt.Sprintf("shutdown.func.%d", i))

		if err := m.shutdowns[i](shutdownCtx); err != nil {
			span.RecordError(err)
			allErrors = append(allErrors, err)
		}

		span.End()
	}

	if len(allErrors) > 0 {
		return errors.Join(allErrors...)
	}
	return nil
}

// Wait 等待关闭信号
func (m *Manager) Wait() {
	<-m.shutdownCh
}

// Done 返回关闭通道
func (m *Manager) Done() <-chan struct{} {
	return m.shutdownCh
}

// Example: 使用示例
func Example() {
	// 创建管理器，30 秒超时
	manager := NewManager(30 * time.Second)

	// 注册分阶段关闭
	// 阶段 1: 停止接受新请求
	manager.RegisterStage("stop_accepting", func(ctx context.Context) error {
		fmt.Println("Stop accepting new requests...")
		return nil
	})

	// 阶段 2: 等待当前请求完成
	manager.RegisterStage("drain_requests", func(ctx context.Context) error {
		fmt.Println("Draining active requests...")
		time.Sleep(5 * time.Second)
		return nil
	})

	// 阶段 3: 关闭外部连接
	manager.RegisterStage("close_external", func(ctx context.Context) error {
		fmt.Println("Closing database connections...")
		return nil
	})
	manager.RegisterStage("close_external", func(ctx context.Context) error {
		fmt.Println("Closing cache connections...")
		return nil
	})

	// 阶段 4: 关闭 OTLP
	manager.RegisterStage("close_telemetry", func(ctx context.Context) error {
		fmt.Println("Shutting down OpenTelemetry...")
		return nil
	})

	// 监听信号
	manager.ListenSignals()

	// 应用主逻辑
	fmt.Println("Application running... Press Ctrl+C to shutdown")

	// 等待关闭
	manager.Wait()
	fmt.Println("Shutdown complete!")
}
