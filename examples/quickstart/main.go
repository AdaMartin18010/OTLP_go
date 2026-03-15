// quickstart - OTLP Go SDK 快速开始示例
//
// 本示例展示如何使用 OTLP Go SDK 快速集成 OpenTelemetry
// 只需几行代码即可启用分布式追踪和指标收集
//
// 运行方式:
//
//	go run main.go
//
// 环境变量配置:
//
//	OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
//	OTEL_SERVICE_NAME=quickstart-demo
package main

import (
	"context"
	"fmt"
	"log"
	"time"

	"github.com/OTLP_go/pkg/logs"
	"github.com/OTLP_go/pkg/otel"
)

func main() {
	// 创建一个带超时的上下文
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	// ========== 快速设置 OpenTelemetry SDK ==========
	// 使用 QuickSetup 一键初始化，只需提供服务名称
	sdk, err := otel.QuickSetup(ctx, "quickstart-demo")
	if err != nil {
		log.Fatalf("Failed to setup OpenTelemetry: %v", err)
	}

	// 确保优雅关闭
	defer func() {
		shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer shutdownCancel()
		if err := sdk.Shutdown(shutdownCtx); err != nil {
			log.Printf("Shutdown error: %v", err)
		}
	}()

	// 创建日志记录器
	logger := logs.New("quickstart")
	logger.Info("OpenTelemetry SDK initialized successfully")

	// ========== 创建 Tracer 并记录追踪 ==========
	tracer := sdk.Tracer("quickstart-service")

	// 启动一个 Span
	ctx, span := tracer.Start(ctx, "main-operation")
	defer span.End()

	// 记录一些属性
	span.SetAttributes(
		logs.String("environment", "development"),
		logs.Int("version", 1),
	)

	// ========== 执行业务逻辑 ==========
	if err := processUserRequest(ctx, sdk); err != nil {
		span.RecordError(err)
		logger.ErrorContext(ctx, "Request processing failed", logs.Error(err))
		return
	}

	logger.InfoContext(ctx, "Request processed successfully")
	fmt.Println("✅ Quickstart demo completed successfully!")
}

// processUserRequest 模拟处理用户请求
func processUserRequest(ctx context.Context, sdk *otel.SDK) error {
	tracer := sdk.Tracer("quickstart-service")

	// 创建子 Span
	ctx, span := tracer.Start(ctx, "processUserRequest")
	defer span.End()

	// 记录开始时间
	start := time.Now()

	// 模拟一些工作
	time.Sleep(100 * time.Millisecond)

	// 记录持续时间
	duration := time.Since(start)
	span.SetAttributes(logs.Int64("duration_ms", duration.Milliseconds()))

	// 创建 Meter 并记录指标
	meter := sdk.Meter("quickstart-service")

	// 使用计数器
	counter, err := meter.Int64Counter("requests.processed")
	if err != nil {
		return err
	}
	counter.Add(ctx, 1)

	return nil
}
