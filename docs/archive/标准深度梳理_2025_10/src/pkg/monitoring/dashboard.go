// Package monitoring provides comprehensive dashboard capabilities for OTLP Go applications.
// It includes real-time monitoring dashboards, metric visualization, and alert management interfaces.
package monitoring

import (
	"context"
	"encoding/json"
	"fmt"
	"html/template"
	"log"
	"net/http"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// Dashboard 仪表板
type Dashboard struct {
	config    DashboardConfig
	tracer    trace.Tracer
	metricMgr *MetricManager
	alertMgr  *AlertManager
	mu        sync.RWMutex
	data      *DashboardData
	templates *template.Template
	server    *http.Server
	stopCh    chan struct{}
}

// NewDashboard 创建仪表板
func NewDashboard(config DashboardConfig, metricMgr *MetricManager, alertMgr *AlertManager) *Dashboard {
	return &Dashboard{
		config:    config,
		tracer:    otel.Tracer("dashboard"),
		metricMgr: metricMgr,
		alertMgr:  alertMgr,
		data:      &DashboardData{},
		stopCh:    make(chan struct{}),
	}
}

// Start 启动仪表板
func (d *Dashboard) Start(ctx context.Context) error {
	ctx, span := d.tracer.Start(ctx, "Dashboard.Start")
	defer span.End()

	if !d.config.Enabled {
		span.SetAttributes(attribute.Bool("dashboard.enabled", false))
		return nil
	}

	// 加载模板
	if err := d.loadTemplates(); err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to load templates: %w", err)
	}

	// 设置路由
	mux := http.NewServeMux()
	d.setupRoutes(mux)

	// 创建服务器
	d.server = &http.Server{
		Addr:    fmt.Sprintf(":%d", d.config.Port),
		Handler: mux,
	}

	// 启动数据更新协程
	go d.updateDataLoop(ctx)

	// 启动服务器
	go func() {
		if err := d.server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Printf("Dashboard server error: %v", err)
		}
	}()

	span.SetAttributes(
		attribute.Int("dashboard.port", d.config.Port),
		attribute.String("dashboard.title", d.config.Title),
		attribute.Bool("dashboard.enabled", d.config.Enabled),
	)

	log.Printf("Dashboard started on port %d", d.config.Port)
	return nil
}

// Stop 停止仪表板
func (d *Dashboard) Stop() error {
	close(d.stopCh)

	if d.server != nil {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		return d.server.Shutdown(ctx)
	}

	return nil
}

// loadTemplates 加载模板
func (d *Dashboard) loadTemplates() error {
	tmpl := `
<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{{.Title}}</title>
    <style>
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            margin: 0;
            padding: 20px;
            background-color: #f5f5f5;
        }
        .header {
            background: white;
            padding: 20px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            margin-bottom: 20px;
        }
        .widget {
            background: white;
            padding: 20px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            margin-bottom: 20px;
        }
        .metric-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
            gap: 20px;
        }
        .metric-card {
            background: white;
            padding: 15px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        .alert-critical {
            border-left: 4px solid #dc3545;
        }
        .alert-warning {
            border-left: 4px solid #ffc107;
        }
        .alert-info {
            border-left: 4px solid #17a2b8;
        }
        .status-indicator {
            display: inline-block;
            width: 10px;
            height: 10px;
            border-radius: 50%;
            margin-right: 8px;
        }
        .status-healthy {
            background-color: #28a745;
        }
        .status-warning {
            background-color: #ffc107;
        }
        .status-critical {
            background-color: #dc3545;
        }
    </style>
</head>
<body>
    <div class="header">
        <h1>{{.Title}}</h1>
        <p>{{.Description}}</p>
        <p>最后更新: {{.Timestamp.Format "2006-01-02 15:04:05"}}</p>
    </div>

    <div class="widget">
        <h2>系统概览</h2>
        <div class="metric-grid">
            <div class="metric-card">
                <h3>总指标数</h3>
                <p>{{.Stats.TotalMetrics}}</p>
            </div>
            <div class="metric-card">
                <h3>活跃告警</h3>
                <p>{{.Stats.ActiveAlerts}}</p>
            </div>
            <div class="metric-card">
                <h3>总告警数</h3>
                <p>{{.Stats.TotalAlerts}}</p>
            </div>
            <div class="metric-card">
                <h3>组件数量</h3>
                <p>{{.Stats.WidgetsCount}}</p>
            </div>
        </div>
    </div>

    <div class="widget">
        <h2>活跃告警</h2>
        {{range .Alerts}}
        {{if eq .Status "firing"}}
        <div class="metric-card alert-{{.Severity}}">
            <h4>{{.Name}}</h4>
            <p>{{.Description}}</p>
            <p>当前值: {{.Value}} | 阈值: {{.Threshold}}</p>
            <p>开始时间: {{.StartedAt.Format "2006-01-02 15:04:05"}}</p>
        </div>
        {{end}}
        {{end}}
    </div>

    <div class="widget">
        <h2>指标数据</h2>
        {{range $name, $metrics := .Metrics}}
        <div class="metric-card">
            <h3>{{$name}}</h3>
            {{range $metrics}}
            <p>{{.Name}}: {{.Value}} {{.Type}} ({{.Timestamp.Format "15:04:05"}})</p>
            {{end}}
        </div>
        {{end}}
    </div>

    <script>
        // 自动刷新页面
        setTimeout(function() {
            location.reload();
        }, {{.RefreshRate}});
    </script>
</body>
</html>
`

	d.templates = template.Must(template.New("dashboard").Parse(tmpl))
	return nil
}

// setupRoutes 设置路由
func (d *Dashboard) setupRoutes(mux *http.ServeMux) {
	// 主页
	mux.HandleFunc("/", d.handleDashboard)

	// API路由
	mux.HandleFunc("/api/metrics", d.handleMetricsAPI)
	mux.HandleFunc("/api/alerts", d.handleAlertsAPI)
	mux.HandleFunc("/api/stats", d.handleStatsAPI)
	mux.HandleFunc("/api/data", d.handleDataAPI)

	// 静态文件
	mux.HandleFunc("/static/", d.handleStatic)
}

// handleDashboard 处理仪表板主页
func (d *Dashboard) handleDashboard(w http.ResponseWriter, r *http.Request) {
	_, span := d.tracer.Start(r.Context(), "Dashboard.handleDashboard")
	defer span.End()

	d.mu.RLock()
	data := d.data
	d.mu.RUnlock()

	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	if err := d.templates.Execute(w, data); err != nil {
		span.RecordError(err)
		log.Printf("Failed to execute template: %v", err)
		http.Error(w, "Internal Server Error", http.StatusInternalServerError)
		return
	}

	span.SetAttributes(attribute.String("request.path", r.URL.Path))
}

// handleMetricsAPI 处理指标API
func (d *Dashboard) handleMetricsAPI(w http.ResponseWriter, r *http.Request) {
	_, span := d.tracer.Start(r.Context(), "Dashboard.handleMetricsAPI")
	defer span.End()

	d.mu.RLock()
	metrics := d.data.Metrics
	d.mu.RUnlock()

	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(metrics); err != nil {
		span.RecordError(err)
		log.Printf("Failed to encode metrics: %v", err)
		http.Error(w, "Internal Server Error", http.StatusInternalServerError)
		return
	}

	span.SetAttributes(attribute.Int("metrics.count", len(metrics)))
}

// handleAlertsAPI 处理告警API
func (d *Dashboard) handleAlertsAPI(w http.ResponseWriter, r *http.Request) {
	_, span := d.tracer.Start(r.Context(), "Dashboard.handleAlertsAPI")
	defer span.End()

	d.mu.RLock()
	alerts := d.data.Alerts
	d.mu.RUnlock()

	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(alerts); err != nil {
		span.RecordError(err)
		log.Printf("Failed to encode alerts: %v", err)
		http.Error(w, "Internal Server Error", http.StatusInternalServerError)
		return
	}

	span.SetAttributes(attribute.Int("alerts.count", len(alerts)))
}

// handleStatsAPI 处理统计API
func (d *Dashboard) handleStatsAPI(w http.ResponseWriter, r *http.Request) {
	_, span := d.tracer.Start(r.Context(), "Dashboard.handleStatsAPI")
	defer span.End()

	d.mu.RLock()
	stats := d.data.Stats
	d.mu.RUnlock()

	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(stats); err != nil {
		span.RecordError(err)
		log.Printf("Failed to encode stats: %v", err)
		http.Error(w, "Internal Server Error", http.StatusInternalServerError)
		return
	}

	span.SetAttributes(attribute.Int("stats.total_metrics", stats.TotalMetrics))
}

// handleDataAPI 处理数据API
func (d *Dashboard) handleDataAPI(w http.ResponseWriter, r *http.Request) {
	_, span := d.tracer.Start(r.Context(), "Dashboard.handleDataAPI")
	defer span.End()

	d.mu.RLock()
	data := d.data
	d.mu.RUnlock()

	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(data); err != nil {
		span.RecordError(err)
		log.Printf("Failed to encode data: %v", err)
		http.Error(w, "Internal Server Error", http.StatusInternalServerError)
		return
	}

	span.SetAttributes(attribute.String("data.timestamp", data.Timestamp.Format(time.RFC3339)))
}

// handleStatic 处理静态文件
func (d *Dashboard) handleStatic(w http.ResponseWriter, r *http.Request) {
	http.Error(w, "Not Found", http.StatusNotFound)
}

// updateDataLoop 更新数据循环
func (d *Dashboard) updateDataLoop(ctx context.Context) {
	ticker := time.NewTicker(d.config.RefreshRate)
	defer ticker.Stop()

	for {
		select {
		case <-d.stopCh:
			return
		case <-ticker.C:
			if err := d.updateData(ctx); err != nil {
				log.Printf("Failed to update dashboard data: %v", err)
			}
		}
	}
}

// updateData 更新数据
func (d *Dashboard) updateData(ctx context.Context) error {
	ctx, span := d.tracer.Start(ctx, "Dashboard.updateData")
	defer span.End()

	// 收集指标数据
	metrics, err := d.metricMgr.CollectAllMetrics(ctx)
	if err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to collect metrics: %w", err)
	}

	// 获取告警数据
	alerts := d.alertMgr.GetAlerts()

	// 计算统计信息
	stats := DashboardStats{
		TotalMetrics:   d.calculateTotalMetrics(metrics),
		ActiveAlerts:   len(d.alertMgr.GetActiveAlerts()),
		TotalAlerts:    len(alerts),
		WidgetsCount:   len(d.config.Widgets),
		LastUpdateTime: time.Now(),
	}

	// 更新数据
	d.mu.Lock()
	d.data = &DashboardData{
		Title:       d.config.Title,
		Description: d.config.Description,
		Timestamp:   time.Now(),
		Metrics:     metrics,
		Alerts:      alerts,
		Widgets:     d.generateWidgetData(metrics, alerts),
		Stats:       stats,
	}
	d.mu.Unlock()

	span.SetAttributes(
		attribute.Int("metrics.count", len(metrics)),
		attribute.Int("alerts.count", len(alerts)),
		attribute.Int("widgets.count", len(d.config.Widgets)),
	)

	return nil
}

// calculateTotalMetrics 计算总指标数
func (d *Dashboard) calculateTotalMetrics(metrics map[string][]MetricValue) int {
	total := 0
	for _, metricList := range metrics {
		total += len(metricList)
	}
	return total
}

// generateWidgetData 生成组件数据
func (d *Dashboard) generateWidgetData(metrics map[string][]MetricValue, alerts []*Alert) []WidgetData {
	var widgets []WidgetData

	for _, widgetConfig := range d.config.Widgets {
		if !widgetConfig.Enabled {
			continue
		}

		widget := WidgetData{
			ID:          widgetConfig.ID,
			Type:        widgetConfig.Type,
			Title:       widgetConfig.Title,
			Data:        make(map[string]interface{}),
			LastUpdated: time.Now(),
			Status:      "healthy",
		}

		// 根据组件类型生成数据
		switch widgetConfig.Type {
		case "metric":
			widget.Data["metrics"] = metrics
		case "alert":
			widget.Data["alerts"] = alerts
		case "chart":
			widget.Data["chart_data"] = d.generateChartData(metrics)
		}

		widgets = append(widgets, widget)
	}

	return widgets
}

// generateChartData 生成图表数据
func (d *Dashboard) generateChartData(metrics map[string][]MetricValue) map[string]interface{} {
	chartData := make(map[string]interface{})

	for name, metricList := range metrics {
		var values []float64
		var timestamps []string

		for _, metric := range metricList {
			values = append(values, metric.Value)
			timestamps = append(timestamps, metric.Timestamp.Format("15:04:05"))
		}

		chartData[name] = map[string]interface{}{
			"values":     values,
			"timestamps": timestamps,
		}
	}

	return chartData
}

// 全局仪表板实例
var (
	globalDashboard *Dashboard
	dashboardOnce   sync.Once
)

// InitGlobalDashboard 初始化全局仪表板
func InitGlobalDashboard(config DashboardConfig, metricMgr *MetricManager, alertMgr *AlertManager) *Dashboard {
	dashboardOnce.Do(func() {
		globalDashboard = NewDashboard(config, metricMgr, alertMgr)
	})
	return globalDashboard
}

// GetGlobalDashboard 获取全局仪表板
func GetGlobalDashboard() *Dashboard {
	return globalDashboard
}
