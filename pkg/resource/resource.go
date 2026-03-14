package resource

import (
	"context"
	"fmt"
	"sync"
	"time"
)

// Resource 资源接口
type Resource interface {
	Initialize(ctx context.Context) error
	Shutdown(ctx context.Context) error
	IsHealthy() bool
	GetName() string
}

// ResourceManager 资源管理器
type ResourceManager struct {
	resources     map[string]Resource
	mutex         sync.RWMutex
	initOrder     []string
	shutdownOrder []string
}

// NewResourceManager 创建资源管理器
func NewResourceManager() *ResourceManager {
	return &ResourceManager{
		resources:     make(map[string]Resource),
		initOrder:     make([]string, 0),
		shutdownOrder: make([]string, 0),
	}
}

// Register 注册资源
func (rm *ResourceManager) Register(name string, resource Resource) {
	rm.mutex.Lock()
	defer rm.mutex.Unlock()

	rm.resources[name] = resource
	rm.initOrder = append(rm.initOrder, name)
	rm.shutdownOrder = append([]string{name}, rm.shutdownOrder...) // 逆序关闭
}

// InitializeAll 初始化所有资源
func (rm *ResourceManager) InitializeAll(ctx context.Context) error {
	rm.mutex.RLock()
	order := make([]string, len(rm.initOrder))
	copy(order, rm.initOrder)
	rm.mutex.RUnlock()

	for _, name := range order {
		rm.mutex.RLock()
		resource, exists := rm.resources[name]
		rm.mutex.RUnlock()

		if !exists {
			continue
		}

		if err := resource.Initialize(ctx); err != nil {
			return &ResourceError{
				Name:      name,
				Operation: "initialize",
				Message:   "Failed to initialize resource",
				Cause:     err,
			}
		}
	}

	return nil
}

// ShutdownAll 关闭所有资源
func (rm *ResourceManager) ShutdownAll(ctx context.Context) error {
	rm.mutex.RLock()
	order := make([]string, len(rm.shutdownOrder))
	copy(order, rm.shutdownOrder)
	rm.mutex.RUnlock()

	var lastErr error
	for _, name := range order {
		rm.mutex.RLock()
		resource, exists := rm.resources[name]
		rm.mutex.RUnlock()

		if !exists {
			continue
		}

		if err := resource.Shutdown(ctx); err != nil {
			lastErr = &ResourceError{
				Name:      name,
				Operation: "shutdown",
				Message:   "Failed to shutdown resource",
				Cause:     err,
			}
		}
	}

	return lastErr
}

// GetResource 获取资源
func (rm *ResourceManager) GetResource(name string) (Resource, bool) {
	rm.mutex.RLock()
	defer rm.mutex.RUnlock()

	resource, exists := rm.resources[name]
	return resource, exists
}

// IsHealthy 检查所有资源是否健康
func (rm *ResourceManager) IsHealthy() bool {
	rm.mutex.RLock()
	defer rm.mutex.RUnlock()

	for _, resource := range rm.resources {
		if !resource.IsHealthy() {
			return false
		}
	}
	return true
}

// GetHealthStatus 获取健康状态
func (rm *ResourceManager) GetHealthStatus() map[string]bool {
	rm.mutex.RLock()
	defer rm.mutex.RUnlock()

	status := make(map[string]bool)
	for name, resource := range rm.resources {
		status[name] = resource.IsHealthy()
	}
	return status
}

// ResourceError 资源错误
type ResourceError struct {
	Name      string
	Operation string
	Message   string
	Cause     error
}

func (e *ResourceError) Error() string {
	if e.Cause != nil {
		return fmt.Sprintf("Resource %s %s failed: %s: %v", e.Name, e.Operation, e.Message, e.Cause)
	}
	return fmt.Sprintf("Resource %s %s failed: %s", e.Name, e.Operation, e.Message)
}

func (e *ResourceError) Unwrap() error {
	return e.Cause
}

// CleanupFunc 清理函数类型
type CleanupFunc func() error

// CleanupManager 清理管理器
type CleanupManager struct {
	cleanups []CleanupFunc
	mutex    sync.Mutex
}

// NewCleanupManager 创建清理管理器
func NewCleanupManager() *CleanupManager {
	return &CleanupManager{
		cleanups: make([]CleanupFunc, 0),
	}
}

// AddCleanup 添加清理函数
func (cm *CleanupManager) AddCleanup(cleanup CleanupFunc) {
	cm.mutex.Lock()
	defer cm.mutex.Unlock()

	cm.cleanups = append(cm.cleanups, cleanup)
}

// ExecuteCleanups 执行所有清理函数
func (cm *CleanupManager) ExecuteCleanups() error {
	cm.mutex.Lock()
	cleanups := make([]CleanupFunc, len(cm.cleanups))
	copy(cleanups, cm.cleanups)
	cm.mutex.Unlock()

	var lastErr error
	// 逆序执行清理函数
	for i := len(cleanups) - 1; i >= 0; i-- {
		if err := cleanups[i](); err != nil {
			lastErr = err
		}
	}

	return lastErr
}

// WithCleanup 带清理的上下文
type WithCleanup struct {
	ctx     context.Context
	cancel  context.CancelFunc
	cleanup CleanupFunc
}

// NewWithCleanup 创建带清理的上下文
func NewWithCleanup(ctx context.Context, cleanup CleanupFunc) *WithCleanup {
	ctx, cancel := context.WithCancel(ctx)
	return &WithCleanup{
		ctx:     ctx,
		cancel:  cancel,
		cleanup: cleanup,
	}
}

// Context 获取上下文
func (wc *WithCleanup) Context() context.Context {
	return wc.ctx
}

// Cancel 取消上下文
func (wc *WithCleanup) Cancel() {
	wc.cancel()
}

// Cleanup 执行清理
func (wc *WithCleanup) Cleanup() error {
	wc.cancel()
	if wc.cleanup != nil {
		return wc.cleanup()
	}
	return nil
}

// ResourcePool 资源池
type ResourcePool struct {
	resources chan Resource
	factory   func() (Resource, error)
	maxSize   int
	mutex     sync.Mutex
}

// NewResourcePool 创建资源池
func NewResourcePool(factory func() (Resource, error), maxSize int) *ResourcePool {
	return &ResourcePool{
		resources: make(chan Resource, maxSize),
		factory:   factory,
		maxSize:   maxSize,
	}
}

// Get 获取资源
func (rp *ResourcePool) Get(ctx context.Context) (Resource, error) {
	select {
	case resource := <-rp.resources:
		return resource, nil
	case <-ctx.Done():
		return nil, ctx.Err()
	default:
		// 池中没有可用资源，创建新的
		return rp.factory()
	}
}

// Put 归还资源
func (rp *ResourcePool) Put(resource Resource) {
	select {
	case rp.resources <- resource:
		// 成功归还
	default:
		// 池已满，关闭资源
		resource.Shutdown(context.Background())
	}
}

// Close 关闭资源池
func (rp *ResourcePool) Close() error {
	close(rp.resources)

	var lastErr error
	for resource := range rp.resources {
		if err := resource.Shutdown(context.Background()); err != nil {
			lastErr = err
		}
	}

	return lastErr
}

// ResourceMonitor 资源监控器
type ResourceMonitor struct {
	resources map[string]Resource
	interval  time.Duration
	stopCh    chan struct{}
	mutex     sync.RWMutex
}

// NewResourceMonitor 创建资源监控器
func NewResourceMonitor(interval time.Duration) *ResourceMonitor {
	return &ResourceMonitor{
		resources: make(map[string]Resource),
		interval:  interval,
		stopCh:    make(chan struct{}),
	}
}

// AddResource 添加资源到监控
func (rm *ResourceMonitor) AddResource(name string, resource Resource) {
	rm.mutex.Lock()
	defer rm.mutex.Unlock()

	rm.resources[name] = resource
}

// RemoveResource 从监控中移除资源
func (rm *ResourceMonitor) RemoveResource(name string) {
	rm.mutex.Lock()
	defer rm.mutex.Unlock()

	delete(rm.resources, name)
}

// Start 开始监控
func (rm *ResourceMonitor) Start() {
	go rm.monitor()
}

// Stop 停止监控
func (rm *ResourceMonitor) Stop() {
	close(rm.stopCh)
}

// monitor 监控循环
func (rm *ResourceMonitor) monitor() {
	ticker := time.NewTicker(rm.interval)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			rm.checkHealth()
		case <-rm.stopCh:
			return
		}
	}
}

// checkHealth 检查健康状态
func (rm *ResourceMonitor) checkHealth() {
	rm.mutex.RLock()
	resources := make(map[string]Resource)
	for name, resource := range rm.resources {
		resources[name] = resource
	}
	rm.mutex.RUnlock()

	for name, resource := range resources {
		if !resource.IsHealthy() {
			// 记录不健康的资源
			// 这里可以添加日志记录或告警逻辑
			_ = name // 避免未使用变量警告
		}
	}
}

// GetHealthReport 获取健康报告
func (rm *ResourceMonitor) GetHealthReport() map[string]bool {
	rm.mutex.RLock()
	defer rm.mutex.RUnlock()

	report := make(map[string]bool)
	for name, resource := range rm.resources {
		report[name] = resource.IsHealthy()
	}

	return report
}
