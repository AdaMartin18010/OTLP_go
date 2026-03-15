// Package monitoring provides comprehensive monitoring and alerting capabilities for OTLP Go applications.
// It includes metrics collection, alert rules, notification systems, and real-time monitoring dashboards.
package monitoring

import (
	"context"
	"fmt"
	"log"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
)

// MetricCollector 指标收集器接口
type MetricCollector interface {
	// Collect 收集指标
	Collect(ctx context.Context) ([]MetricValue, error)
	// GetConfig 获取配置
	GetConfig() MetricConfig
	// Start 启动收集器
	Start(ctx context.Context) error
	// Stop 停止收集器
	Stop() error
}

// SystemMetricCollector 系统指标收集器
type SystemMetricCollector struct {
	config    MetricConfig
	tracer    trace.Tracer
	meter     metric.Meter
	stopCh    chan struct{}
	mu        sync.RWMutex
	metrics   map[string]MetricValue
	collector metric.Float64Counter
}

// NewSystemMetricCollector 创建系统指标收集器
func NewSystemMetricCollector(config MetricConfig) *SystemMetricCollector {
	return &SystemMetricCollector{
		config:  config,
		tracer:  otel.Tracer("system-metrics"),
		meter:   otel.Meter("system-metrics"),
		stopCh:  make(chan struct{}),
		metrics: make(map[string]MetricValue),
	}
}

// Start 启动系统指标收集
func (smc *SystemMetricCollector) Start(ctx context.Context) error {
	ctx, span := smc.tracer.Start(ctx, "SystemMetricCollector.Start")
	defer span.End()

	// 创建计数器
	counter, err := smc.meter.Float64Counter(
		smc.config.Name,
		metric.WithDescription(smc.config.Description),
		metric.WithUnit(smc.config.Unit),
	)
	if err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to create counter: %w", err)
	}

	smc.collector = counter

	// 启动收集协程
	go smc.collectLoop(ctx)

	span.SetAttributes(
		attribute.String("collector.name", smc.config.Name),
		attribute.String("collector.type", string(smc.config.Type)),
	)

	return nil
}

// Stop 停止系统指标收集
func (smc *SystemMetricCollector) Stop() error {
	close(smc.stopCh)
	return nil
}

// collectLoop 收集循环
func (smc *SystemMetricCollector) collectLoop(ctx context.Context) {
	ticker := time.NewTicker(10 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-smc.stopCh:
			return
		case <-ticker.C:
			if err := smc.collectMetrics(ctx); err != nil {
				log.Printf("Failed to collect metrics: %v", err)
			}
		}
	}
}

// collectMetrics 收集指标
func (smc *SystemMetricCollector) collectMetrics(ctx context.Context) error {
	ctx, span := smc.tracer.Start(ctx, "SystemMetricCollector.collectMetrics")
	defer span.End()

	smc.mu.Lock()
	defer smc.mu.Unlock()

	// 收集CPU使用率（模拟）
	cpuUsage := smc.simulateCPUUsage()
	cpuMetric := MetricValue{
		Name:      "cpu_usage_percent",
		Value:     cpuUsage,
		Labels:    map[string]string{"host": "localhost"},
		Timestamp: time.Now(),
		Type:      Gauge,
	}
	smc.metrics["cpu_usage"] = cpuMetric

	// 收集内存使用率（模拟）
	memoryUsage := smc.simulateMemoryUsage()
	memoryMetric := MetricValue{
		Name:      "memory_usage_percent",
		Value:     memoryUsage,
		Labels:    map[string]string{"host": "localhost"},
		Timestamp: time.Now(),
		Type:      Gauge,
	}
	smc.metrics["memory_usage"] = memoryMetric

	// 收集磁盘使用率（模拟）
	diskUsage := smc.simulateDiskUsage()
	diskMetric := MetricValue{
		Name:      "disk_usage_percent",
		Value:     diskUsage,
		Labels:    map[string]string{"host": "localhost", "device": "/dev/sda1"},
		Timestamp: time.Now(),
		Type:      Gauge,
	}
	smc.metrics["disk_usage"] = diskMetric

	// 收集网络流量（模拟）
	networkIn := smc.simulateNetworkIn()
	networkInMetric := MetricValue{
		Name:      "network_bytes_in",
		Value:     networkIn,
		Labels:    map[string]string{"host": "localhost", "interface": "eth0"},
		Timestamp: time.Now(),
		Type:      Counter,
	}
	smc.metrics["network_in"] = networkInMetric

	networkOut := smc.simulateNetworkOut()
	networkOutMetric := MetricValue{
		Name:      "network_bytes_out",
		Value:     networkOut,
		Labels:    map[string]string{"host": "localhost", "interface": "eth0"},
		Timestamp: time.Now(),
		Type:      Counter,
	}
	smc.metrics["network_out"] = networkOutMetric

	// 记录到OpenTelemetry
	if smc.collector != nil {
		smc.collector.Add(ctx, cpuUsage, metric.WithAttributes(
			attribute.String("metric_name", "cpu_usage"),
		))
	}

	span.SetAttributes(
		attribute.Int("metrics_collected", len(smc.metrics)),
		attribute.Float64("cpu_usage", cpuUsage),
		attribute.Float64("memory_usage", memoryUsage),
		attribute.Float64("disk_usage", diskUsage),
	)

	return nil
}

// Collect 收集指标
func (smc *SystemMetricCollector) Collect(ctx context.Context) ([]MetricValue, error) {
	smc.mu.RLock()
	defer smc.mu.RUnlock()

	metrics := make([]MetricValue, 0, len(smc.metrics))
	for _, metric := range smc.metrics {
		metrics = append(metrics, metric)
	}

	return metrics, nil
}

// GetConfig 获取配置
func (smc *SystemMetricCollector) GetConfig() MetricConfig {
	return smc.config
}

// simulateCPUUsage 模拟CPU使用率
func (smc *SystemMetricCollector) simulateCPUUsage() float64 {
	// 模拟CPU使用率在20-80%之间波动
	return 20 + float64(time.Now().UnixNano()%60)
}

// simulateMemoryUsage 模拟内存使用率
func (smc *SystemMetricCollector) simulateMemoryUsage() float64 {
	// 模拟内存使用率在30-70%之间波动
	return 30 + float64(time.Now().UnixNano()%40)
}

// simulateDiskUsage 模拟磁盘使用率
func (smc *SystemMetricCollector) simulateDiskUsage() float64 {
	// 模拟磁盘使用率在40-90%之间波动
	return 40 + float64(time.Now().UnixNano()%50)
}

// simulateNetworkIn 模拟网络入流量
func (smc *SystemMetricCollector) simulateNetworkIn() float64 {
	// 模拟网络入流量
	return float64(time.Now().UnixNano() % 1000000)
}

// simulateNetworkOut 模拟网络出流量
func (smc *SystemMetricCollector) simulateNetworkOut() float64 {
	// 模拟网络出流量
	return float64(time.Now().UnixNano() % 800000)
}

// ApplicationMetricCollector 应用指标收集器
type ApplicationMetricCollector struct {
	config    MetricConfig
	tracer    trace.Tracer
	meter     metric.Meter
	stopCh    chan struct{}
	mu        sync.RWMutex
	metrics   map[string]MetricValue
	counter   metric.Float64Counter
	histogram metric.Float64Histogram
}

// NewApplicationMetricCollector 创建应用指标收集器
func NewApplicationMetricCollector(config MetricConfig) *ApplicationMetricCollector {
	return &ApplicationMetricCollector{
		config:  config,
		tracer:  otel.Tracer("application-metrics"),
		meter:   otel.Meter("application-metrics"),
		stopCh:  make(chan struct{}),
		metrics: make(map[string]MetricValue),
	}
}

// Start 启动应用指标收集
func (amc *ApplicationMetricCollector) Start(ctx context.Context) error {
	ctx, span := amc.tracer.Start(ctx, "ApplicationMetricCollector.Start")
	defer span.End()

	// 创建计数器
	counter, err := amc.meter.Float64Counter(
		"http_requests_total",
		metric.WithDescription("Total number of HTTP requests"),
		metric.WithUnit("1"),
	)
	if err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to create counter: %w", err)
	}
	amc.counter = counter

	// 创建直方图
	histogram, err := amc.meter.Float64Histogram(
		"http_request_duration_seconds",
		metric.WithDescription("HTTP request duration in seconds"),
		metric.WithUnit("s"),
	)
	if err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to create histogram: %w", err)
	}
	amc.histogram = histogram

	// 启动收集协程
	go amc.collectLoop(ctx)

	span.SetAttributes(
		attribute.String("collector.name", amc.config.Name),
		attribute.String("collector.type", string(amc.config.Type)),
	)

	return nil
}

// Stop 停止应用指标收集
func (amc *ApplicationMetricCollector) Stop() error {
	close(amc.stopCh)
	return nil
}

// collectLoop 收集循环
func (amc *ApplicationMetricCollector) collectLoop(ctx context.Context) {
	ticker := time.NewTicker(5 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-amc.stopCh:
			return
		case <-ticker.C:
			if err := amc.collectMetrics(ctx); err != nil {
				log.Printf("Failed to collect application metrics: %v", err)
			}
		}
	}
}

// collectMetrics 收集应用指标
func (amc *ApplicationMetricCollector) collectMetrics(ctx context.Context) error {
	ctx, span := amc.tracer.Start(ctx, "ApplicationMetricCollector.collectMetrics")
	defer span.End()

	amc.mu.Lock()
	defer amc.mu.Unlock()

	// 收集HTTP请求总数
	httpRequests := amc.simulateHTTPRequests()
	httpRequestsMetric := MetricValue{
		Name:      "http_requests_total",
		Value:     httpRequests,
		Labels:    map[string]string{"method": "GET", "status": "200"},
		Timestamp: time.Now(),
		Type:      Counter,
	}
	amc.metrics["http_requests"] = httpRequestsMetric

	// 收集HTTP请求延迟
	httpLatency := amc.simulateHTTPLatency()
	httpLatencyMetric := MetricValue{
		Name:      "http_request_duration_seconds",
		Value:     httpLatency,
		Labels:    map[string]string{"method": "GET", "endpoint": "/api/orders"},
		Timestamp: time.Now(),
		Type:      Histogram,
	}
	amc.metrics["http_latency"] = httpLatencyMetric

	// 收集活跃连接数
	activeConnections := amc.simulateActiveConnections()
	activeConnectionsMetric := MetricValue{
		Name:      "active_connections",
		Value:     activeConnections,
		Labels:    map[string]string{"service": "api-gateway"},
		Timestamp: time.Now(),
		Type:      Gauge,
	}
	amc.metrics["active_connections"] = activeConnectionsMetric

	// 收集错误率
	errorRate := amc.simulateErrorRate()
	errorRateMetric := MetricValue{
		Name:      "error_rate_percent",
		Value:     errorRate,
		Labels:    map[string]string{"service": "api-gateway"},
		Timestamp: time.Now(),
		Type:      Gauge,
	}
	amc.metrics["error_rate"] = errorRateMetric

	// 记录到OpenTelemetry
	if amc.counter != nil {
		amc.counter.Add(ctx, httpRequests, metric.WithAttributes(
			attribute.String("method", "GET"),
			attribute.String("status", "200"),
		))
	}

	if amc.histogram != nil {
		amc.histogram.Record(ctx, httpLatency, metric.WithAttributes(
			attribute.String("method", "GET"),
			attribute.String("endpoint", "/api/orders"),
		))
	}

	span.SetAttributes(
		attribute.Int("metrics_collected", len(amc.metrics)),
		attribute.Float64("http_requests", httpRequests),
		attribute.Float64("http_latency", httpLatency),
		attribute.Float64("active_connections", activeConnections),
		attribute.Float64("error_rate", errorRate),
	)

	return nil
}

// Collect 收集指标
func (amc *ApplicationMetricCollector) Collect(ctx context.Context) ([]MetricValue, error) {
	amc.mu.RLock()
	defer amc.mu.RUnlock()

	metrics := make([]MetricValue, 0, len(amc.metrics))
	for _, metric := range amc.metrics {
		metrics = append(metrics, metric)
	}

	return metrics, nil
}

// GetConfig 获取配置
func (amc *ApplicationMetricCollector) GetConfig() MetricConfig {
	return amc.config
}

// simulateHTTPRequests 模拟HTTP请求数
func (amc *ApplicationMetricCollector) simulateHTTPRequests() float64 {
	return float64(time.Now().UnixNano() % 1000)
}

// simulateHTTPLatency 模拟HTTP延迟
func (amc *ApplicationMetricCollector) simulateHTTPLatency() float64 {
	return float64(time.Now().UnixNano()%1000) / 1000.0
}

// simulateActiveConnections 模拟活跃连接数
func (amc *ApplicationMetricCollector) simulateActiveConnections() float64 {
	return float64(time.Now().UnixNano() % 100)
}

// simulateErrorRate 模拟错误率
func (amc *ApplicationMetricCollector) simulateErrorRate() float64 {
	return float64(time.Now().UnixNano()%10) / 10.0
}

// MetricManager 指标管理器
type MetricManager struct {
	collectors map[string]MetricCollector
	tracer     trace.Tracer
	meter      metric.Meter
	mu         sync.RWMutex
}

// NewMetricManager 创建指标管理器
func NewMetricManager() *MetricManager {
	return &MetricManager{
		collectors: make(map[string]MetricCollector),
		tracer:     otel.Tracer("metric-manager"),
		meter:      otel.Meter("metric-manager"),
	}
}

// AddCollector 添加收集器
func (mm *MetricManager) AddCollector(name string, collector MetricCollector) {
	mm.mu.Lock()
	defer mm.mu.Unlock()
	mm.collectors[name] = collector
}

// StartCollector 启动收集器
func (mm *MetricManager) StartCollector(ctx context.Context, name string) error {
	mm.mu.RLock()
	collector, exists := mm.collectors[name]
	mm.mu.RUnlock()

	if !exists {
		return fmt.Errorf("collector %s not found", name)
	}

	return collector.Start(ctx)
}

// StopCollector 停止收集器
func (mm *MetricManager) StopCollector(name string) error {
	mm.mu.RLock()
	collector, exists := mm.collectors[name]
	mm.mu.RUnlock()

	if !exists {
		return fmt.Errorf("collector %s not found", name)
	}

	return collector.Stop()
}

// CollectAllMetrics 收集所有指标
func (mm *MetricManager) CollectAllMetrics(ctx context.Context) (map[string][]MetricValue, error) {
	ctx, span := mm.tracer.Start(ctx, "MetricManager.CollectAllMetrics")
	defer span.End()

	mm.mu.RLock()
	defer mm.mu.RUnlock()

	allMetrics := make(map[string][]MetricValue)

	for name, collector := range mm.collectors {
		metrics, err := collector.Collect(ctx)
		if err != nil {
			span.RecordError(err)
			log.Printf("Failed to collect metrics from %s: %v", name, err)
			continue
		}
		allMetrics[name] = metrics
	}

	span.SetAttributes(attribute.Int("collectors_count", len(mm.collectors)))

	return allMetrics, nil
}

// GetCollectorStats 获取收集器统计信息
func (mm *MetricManager) GetCollectorStats() map[string]interface{} {
	mm.mu.RLock()
	defer mm.mu.RUnlock()

	stats := make(map[string]interface{})
	for name, collector := range mm.collectors {
		config := collector.GetConfig()
		stats[name] = map[string]interface{}{
			"name":        config.Name,
			"type":        config.Type,
			"description": config.Description,
			"enabled":     config.Enabled,
		}
	}

	return stats
}

// 全局指标管理器实例
var (
	globalMetricManager *MetricManager
	metricManagerOnce   sync.Once
)

// InitGlobalMetricManager 初始化全局指标管理器
func InitGlobalMetricManager() *MetricManager {
	metricManagerOnce.Do(func() {
		globalMetricManager = NewMetricManager()
	})
	return globalMetricManager
}

// GetGlobalMetricManager 获取全局指标管理器
func GetGlobalMetricManager() *MetricManager {
	if globalMetricManager == nil {
		return InitGlobalMetricManager()
	}
	return globalMetricManager
}
