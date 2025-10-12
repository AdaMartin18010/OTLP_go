// Package monitoring provides a comprehensive monitoring and alerting manager for OTLP Go applications.
// It coordinates metrics collection, alerting, and dashboard functionality.
package monitoring

import (
	"context"
	"fmt"
	"log"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// MonitoringManager 监控管理器
type MonitoringManager struct {
	config    MonitoringConfig
	tracer    trace.Tracer
	metricMgr *MetricManager
	alertMgr  *AlertManager
	dashboard *Dashboard
	stopCh    chan struct{}
	mu        sync.RWMutex
	started   bool
	stats     MonitoringStats
}

// NewMonitoringManager 创建监控管理器
func NewMonitoringManager(config MonitoringConfig) *MonitoringManager {
	return &MonitoringManager{
		config:    config,
		tracer:    otel.Tracer("monitoring-manager"),
		metricMgr: NewMetricManager(),
		alertMgr:  NewAlertManager(),
		stopCh:    make(chan struct{}),
		stats: MonitoringStats{
			StartTime: time.Now(),
		},
	}
}

// Start 启动监控管理器
func (mm *MonitoringManager) Start(ctx context.Context) error {
	ctx, span := mm.tracer.Start(ctx, "MonitoringManager.Start")
	defer span.End()

	if !mm.config.Enabled {
		span.SetAttributes(attribute.Bool("monitoring.enabled", false))
		return nil
	}

	mm.mu.Lock()
	defer mm.mu.Unlock()

	if mm.started {
		return fmt.Errorf("monitoring manager already started")
	}

	// 初始化收集器
	if err := mm.initializeCollectors(ctx); err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to initialize collectors: %w", err)
	}

	// 初始化告警规则
	if err := mm.initializeAlertRules(ctx); err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to initialize alert rules: %w", err)
	}

	// 初始化仪表板
	if err := mm.initializeDashboard(ctx); err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to initialize dashboard: %w", err)
	}

	// 启动监控循环
	go mm.monitoringLoop(ctx)

	mm.started = true
	mm.stats.StartTime = time.Now()

	span.SetAttributes(
		attribute.Bool("monitoring.enabled", mm.config.Enabled),
		attribute.Int("collectors.count", len(mm.config.Collectors)),
		attribute.Int("alert_rules.count", len(mm.config.AlertRules)),
		attribute.String("dashboard.port", fmt.Sprintf("%d", mm.config.Dashboard.Port)),
	)

	log.Printf("Monitoring manager started successfully")
	return nil
}

// Stop 停止监控管理器
func (mm *MonitoringManager) Stop() error {
	mm.mu.Lock()
	defer mm.mu.Unlock()

	if !mm.started {
		return nil
	}

	close(mm.stopCh)

	// 停止仪表板
	if mm.dashboard != nil {
		if err := mm.dashboard.Stop(); err != nil {
			log.Printf("Failed to stop dashboard: %v", err)
		}
	}

	// 停止收集器
	for name := range mm.metricMgr.GetCollectorStats() {
		if err := mm.metricMgr.StopCollector(name); err != nil {
			log.Printf("Failed to stop collector %s: %v", name, err)
		}
	}

	mm.started = false
	log.Printf("Monitoring manager stopped")
	return nil
}

// initializeCollectors 初始化收集器
func (mm *MonitoringManager) initializeCollectors(ctx context.Context) error {
	ctx, span := mm.tracer.Start(ctx, "MonitoringManager.initializeCollectors")
	defer span.End()

	for _, config := range mm.config.Collectors {
		if !config.Enabled {
			continue
		}

		var collector MetricCollector
		switch config.Type {
		case "system":
			collector = NewSystemMetricCollector(config)
		case "application":
			collector = NewApplicationMetricCollector(config)
		default:
			log.Printf("Unknown collector type: %s", config.Type)
			continue
		}

		mm.metricMgr.AddCollector(config.Name, collector)

		if err := mm.metricMgr.StartCollector(ctx, config.Name); err != nil {
			span.RecordError(err)
			log.Printf("Failed to start collector %s: %v", config.Name, err)
			continue
		}

		log.Printf("Started collector: %s (%s)", config.Name, config.Type)
	}

	span.SetAttributes(attribute.Int("collectors.initialized", len(mm.config.Collectors)))
	return nil
}

// initializeAlertRules 初始化告警规则
func (mm *MonitoringManager) initializeAlertRules(ctx context.Context) error {
	ctx, span := mm.tracer.Start(ctx, "MonitoringManager.initializeAlertRules")
	defer span.End()

	for _, rule := range mm.config.AlertRules {
		if !rule.Enabled {
			continue
		}

		if err := mm.alertMgr.rules.AddRule(&rule); err != nil {
			span.RecordError(err)
			log.Printf("Failed to add alert rule %s: %v", rule.ID, err)
			continue
		}

		log.Printf("Added alert rule: %s", rule.Name)
	}

	span.SetAttributes(attribute.Int("alert_rules.initialized", len(mm.config.AlertRules)))
	return nil
}

// initializeDashboard 初始化仪表板
func (mm *MonitoringManager) initializeDashboard(ctx context.Context) error {
	ctx, span := mm.tracer.Start(ctx, "MonitoringManager.initializeDashboard")
	defer span.End()

	if !mm.config.Dashboard.Enabled {
		span.SetAttributes(attribute.Bool("dashboard.enabled", false))
		return nil
	}

	mm.dashboard = NewDashboard(mm.config.Dashboard, mm.metricMgr, mm.alertMgr)

	if err := mm.dashboard.Start(ctx); err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to start dashboard: %w", err)
	}

	span.SetAttributes(
		attribute.Bool("dashboard.enabled", true),
		attribute.Int("dashboard.port", mm.config.Dashboard.Port),
	)

	log.Printf("Dashboard started on port %d", mm.config.Dashboard.Port)
	return nil
}

// monitoringLoop 监控循环
func (mm *MonitoringManager) monitoringLoop(ctx context.Context) {
	ticker := time.NewTicker(mm.config.Interval)
	defer ticker.Stop()

	for {
		select {
		case <-mm.stopCh:
			return
		case <-ticker.C:
			if err := mm.collectAndProcess(ctx); err != nil {
				mm.stats.ErrorsCount++
				log.Printf("Failed to collect and process metrics: %v", err)
			}
		}
	}
}

// collectAndProcess 收集和处理指标
func (mm *MonitoringManager) collectAndProcess(ctx context.Context) error {
	ctx, span := mm.tracer.Start(ctx, "MonitoringManager.collectAndProcess")
	defer span.End()

	// 收集指标
	metrics, err := mm.metricMgr.CollectAllMetrics(ctx)
	if err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to collect metrics: %w", err)
	}

	// 处理告警
	if err := mm.alertMgr.ProcessAlerts(ctx, metrics); err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to process alerts: %w", err)
	}

	// 更新统计信息
	mm.mu.Lock()
	mm.stats.LastUpdateTime = time.Now()
	mm.stats.MetricsCollected += int64(mm.calculateTotalMetrics(metrics))
	mm.stats.Uptime = time.Since(mm.stats.StartTime)
	mm.mu.Unlock()

	span.SetAttributes(
		attribute.Int("metrics.collected", len(metrics)),
		attribute.Int64("total_metrics", mm.calculateTotalMetrics(metrics)),
	)

	return nil
}

// calculateTotalMetrics 计算总指标数
func (mm *MonitoringManager) calculateTotalMetrics(metrics map[string][]MetricValue) int64 {
	total := int64(0)
	for _, metricList := range metrics {
		total += int64(len(metricList))
	}
	return total
}

// GetStats 获取统计信息
func (mm *MonitoringManager) GetStats() MonitoringStats {
	mm.mu.RLock()
	defer mm.mu.RUnlock()

	stats := mm.stats
	stats.Uptime = time.Since(stats.StartTime)
	return stats
}

// GetMetrics 获取指标数据
func (mm *MonitoringManager) GetMetrics(ctx context.Context) (map[string][]MetricValue, error) {
	return mm.metricMgr.CollectAllMetrics(ctx)
}

// GetAlerts 获取告警数据
func (mm *MonitoringManager) GetAlerts() []*Alert {
	return mm.alertMgr.GetAlerts()
}

// GetActiveAlerts 获取活跃告警
func (mm *MonitoringManager) GetActiveAlerts() []*Alert {
	return mm.alertMgr.GetActiveAlerts()
}

// ResolveAlert 解决告警
func (mm *MonitoringManager) ResolveAlert(alertID string) error {
	err := mm.alertMgr.ResolveAlert(alertID)
	if err == nil {
		mm.mu.Lock()
		mm.stats.AlertsResolved++
		mm.mu.Unlock()
	}
	return err
}

// AddAlertRule 添加告警规则
func (mm *MonitoringManager) AddAlertRule(rule *AlertRule) error {
	err := mm.alertMgr.rules.AddRule(rule)
	if err == nil {
		mm.mu.Lock()
		mm.config.AlertRules = append(mm.config.AlertRules, *rule)
		mm.mu.Unlock()
	}
	return err
}

// RemoveAlertRule 删除告警规则
func (mm *MonitoringManager) RemoveAlertRule(ruleID string) error {
	err := mm.alertMgr.rules.RemoveRule(ruleID)
	if err == nil {
		mm.mu.Lock()
		// 从配置中移除规则
		for i, rule := range mm.config.AlertRules {
			if rule.ID == ruleID {
				mm.config.AlertRules = append(mm.config.AlertRules[:i], mm.config.AlertRules[i+1:]...)
				break
			}
		}
		mm.mu.Unlock()
	}
	return err
}

// GetDashboardURL 获取仪表板URL
func (mm *MonitoringManager) GetDashboardURL() string {
	if mm.dashboard == nil || !mm.config.Dashboard.Enabled {
		return ""
	}
	return fmt.Sprintf("http://localhost:%d", mm.config.Dashboard.Port)
}

// IsHealthy 检查监控系统健康状态
func (mm *MonitoringManager) IsHealthy() bool {
	mm.mu.RLock()
	defer mm.mu.RUnlock()

	if !mm.started {
		return false
	}

	// 检查最后更新时间
	if time.Since(mm.stats.LastUpdateTime) > mm.config.Interval*2 {
		return false
	}

	// 检查错误率
	if mm.stats.ErrorsCount > 0 && mm.stats.MetricsCollected > 0 {
		errorRate := float64(mm.stats.ErrorsCount) / float64(mm.stats.MetricsCollected)
		if errorRate > 0.1 { // 错误率超过10%
			return false
		}
	}

	return true
}

// GetHealthStatus 获取健康状态
func (mm *MonitoringManager) GetHealthStatus() map[string]interface{} {
	stats := mm.GetStats()

	status := map[string]interface{}{
		"healthy":           mm.IsHealthy(),
		"started":           mm.started,
		"uptime":            stats.Uptime.String(),
		"last_update":       stats.LastUpdateTime.Format(time.RFC3339),
		"metrics_collected": stats.MetricsCollected,
		"alerts_generated":  stats.AlertsGenerated,
		"alerts_resolved":   stats.AlertsResolved,
		"errors_count":      stats.ErrorsCount,
		"dashboard_url":     mm.GetDashboardURL(),
	}

	return status
}

// 全局监控管理器实例
var (
	globalMonitoringManager *MonitoringManager
	monitoringManagerOnce   sync.Once
)

// InitGlobalMonitoringManager 初始化全局监控管理器
func InitGlobalMonitoringManager(config MonitoringConfig) *MonitoringManager {
	monitoringManagerOnce.Do(func() {
		globalMonitoringManager = NewMonitoringManager(config)
	})
	return globalMonitoringManager
}

// GetGlobalMonitoringManager 获取全局监控管理器
func GetGlobalMonitoringManager() *MonitoringManager {
	if globalMonitoringManager == nil {
		// 使用默认配置
		config := MonitoringConfig{
			Enabled:  true,
			Interval: 30 * time.Second,
			Dashboard: DashboardConfig{
				Port:        8080,
				Title:       "OTLP Go Monitoring Dashboard",
				Description: "Real-time monitoring and alerting dashboard",
				RefreshRate: 30 * time.Second,
				Enabled:     true,
			},
			Collectors: []MetricConfig{
				{
					Name:        "system-metrics",
					Type:        "system",
					Description: "System metrics collector",
					Enabled:     true,
				},
				{
					Name:        "application-metrics",
					Type:        "application",
					Description: "Application metrics collector",
					Enabled:     true,
				},
			},
			AlertRules: []AlertRule{
				{
					ID:          "high-cpu-usage",
					Name:        "High CPU Usage",
					Description: "CPU usage is above 80%",
					Metric:      "cpu_usage_percent",
					Condition:   "gt",
					Threshold:   80.0,
					Duration:    5 * time.Minute,
					Severity:    Warning,
					Enabled:     true,
				},
				{
					ID:          "high-memory-usage",
					Name:        "High Memory Usage",
					Description: "Memory usage is above 90%",
					Metric:      "memory_usage_percent",
					Condition:   "gt",
					Threshold:   90.0,
					Duration:    5 * time.Minute,
					Severity:    Critical,
					Enabled:     true,
				},
			},
			Retention: 24 * time.Hour,
		}
		globalMonitoringManager = NewMonitoringManager(config)
	}
	return globalMonitoringManager
}
