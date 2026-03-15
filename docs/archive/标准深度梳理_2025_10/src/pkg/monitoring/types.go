// Package monitoring provides common types and interfaces for monitoring and alerting.
package monitoring

import "time"

// MetricType 定义指标类型
type MetricType string

const (
	Counter   MetricType = "counter"
	Gauge     MetricType = "gauge"
	Histogram MetricType = "histogram"
	Summary   MetricType = "summary"
)

// AlertSeverity 告警严重程度
type AlertSeverity string

const (
	Critical AlertSeverity = "critical"
	Warning  AlertSeverity = "warning"
	Info     AlertSeverity = "info"
)

// AlertStatus 告警状态
type AlertStatus string

const (
	Firing   AlertStatus = "firing"
	Resolved AlertStatus = "resolved"
	Pending  AlertStatus = "pending"
)

// MetricConfig 指标配置
type MetricConfig struct {
	Name        string            `json:"name"`        // 指标名称
	Type        MetricType        `json:"type"`        // 指标类型
	Description string            `json:"description"` // 指标描述
	Labels      map[string]string `json:"labels"`      // 标签
	Unit        string            `json:"unit"`        // 单位
	Enabled     bool              `json:"enabled"`     // 是否启用
}

// MetricValue 指标值
type MetricValue struct {
	Name      string            `json:"name"`      // 指标名称
	Value     float64           `json:"value"`     // 指标值
	Labels    map[string]string `json:"labels"`    // 标签
	Timestamp time.Time         `json:"timestamp"` // 时间戳
	Type      MetricType        `json:"type"`      // 指标类型
}

// AlertRule 告警规则
type AlertRule struct {
	ID          string            `json:"id"`          // 规则ID
	Name        string            `json:"name"`        // 规则名称
	Description string            `json:"description"` // 规则描述
	Metric      string            `json:"metric"`      // 指标名称
	Condition   string            `json:"condition"`   // 条件表达式
	Threshold   float64           `json:"threshold"`   // 阈值
	Duration    time.Duration     `json:"duration"`    // 持续时间
	Severity    AlertSeverity     `json:"severity"`    // 严重程度
	Labels      map[string]string `json:"labels"`      // 标签
	Enabled     bool              `json:"enabled"`     // 是否启用
	CreatedAt   time.Time         `json:"created_at"`  // 创建时间
	UpdatedAt   time.Time         `json:"updated_at"`  // 更新时间
}

// Alert 告警
type Alert struct {
	ID          string            `json:"id"`          // 告警ID
	RuleID      string            `json:"rule_id"`     // 规则ID
	Name        string            `json:"name"`        // 告警名称
	Description string            `json:"description"` // 告警描述
	Severity    AlertSeverity     `json:"severity"`    // 严重程度
	Status      AlertStatus       `json:"status"`      // 状态
	Labels      map[string]string `json:"labels"`      // 标签
	Annotations map[string]string `json:"annotations"` // 注释
	Value       float64           `json:"value"`       // 当前值
	Threshold   float64           `json:"threshold"`   // 阈值
	StartedAt   time.Time         `json:"started_at"`  // 开始时间
	UpdatedAt   time.Time         `json:"updated_at"`  // 更新时间
	ResolvedAt  *time.Time        `json:"resolved_at"` // 解决时间
}

// DashboardConfig 仪表板配置
type DashboardConfig struct {
	Port        int               `json:"port"`        // 端口
	Title       string            `json:"title"`       // 标题
	Description string            `json:"description"` // 描述
	RefreshRate time.Duration     `json:"refresh_rate"` // 刷新率
	Theme       string            `json:"theme"`       // 主题
	Layout      string            `json:"layout"`      // 布局
	Widgets     []WidgetConfig    `json:"widgets"`     // 组件配置
	Enabled     bool              `json:"enabled"`     // 是否启用
	Auth        DashboardAuth     `json:"auth"`        // 认证配置
}

// DashboardAuth 仪表板认证配置
type DashboardAuth struct {
	Enabled  bool   `json:"enabled"`  // 是否启用认证
	Username string `json:"username"` // 用户名
	Password string `json:"password"` // 密码
}

// WidgetConfig 组件配置
type WidgetConfig struct {
	ID          string            `json:"id"`          // 组件ID
	Type        string            `json:"type"`        // 组件类型
	Title       string            `json:"title"`       // 标题
	Description string            `json:"description"` // 描述
	Position    WidgetPosition    `json:"position"`    // 位置
	Size        WidgetSize        `json:"size"`        // 大小
	Config      map[string]interface{} `json:"config"`  // 配置
	Enabled     bool              `json:"enabled"`     // 是否启用
}

// WidgetPosition 组件位置
type WidgetPosition struct {
	X int `json:"x"` // X坐标
	Y int `json:"y"` // Y坐标
}

// WidgetSize 组件大小
type WidgetSize struct {
	Width  int `json:"width"`  // 宽度
	Height int `json:"height"` // 高度
}

// DashboardData 仪表板数据
type DashboardData struct {
	Title       string                 `json:"title"`       // 标题
	Description string                 `json:"description"` // 描述
	Timestamp   time.Time              `json:"timestamp"`   // 时间戳
	Metrics     map[string][]MetricValue `json:"metrics"`   // 指标数据
	Alerts      []*Alert               `json:"alerts"`      // 告警数据
	Widgets     []WidgetData           `json:"widgets"`     // 组件数据
	Stats       DashboardStats         `json:"stats"`       // 统计信息
}

// WidgetData 组件数据
type WidgetData struct {
	ID          string                 `json:"id"`          // 组件ID
	Type        string                 `json:"type"`        // 组件类型
	Title       string                 `json:"title"`       // 标题
	Data        map[string]interface{} `json:"data"`       // 数据
	LastUpdated time.Time              `json:"last_updated"` // 最后更新时间
	Status      string                 `json:"status"`      // 状态
}

// DashboardStats 仪表板统计信息
type DashboardStats struct {
	TotalMetrics    int `json:"total_metrics"`    // 总指标数
	ActiveAlerts    int `json:"active_alerts"`    // 活跃告警数
	TotalAlerts     int `json:"total_alerts"`     // 总告警数
	WidgetsCount    int `json:"widgets_count"`    // 组件数量
	LastUpdateTime  time.Time `json:"last_update_time"` // 最后更新时间
}

// MonitoringConfig 监控配置
type MonitoringConfig struct {
	Enabled     bool              `json:"enabled"`     // 是否启用监控
	Interval    time.Duration     `json:"interval"`    // 收集间隔
	Dashboard   DashboardConfig   `json:"dashboard"`   // 仪表板配置
	Collectors  []MetricConfig   `json:"collectors"`  // 收集器配置
	AlertRules  []AlertRule       `json:"alert_rules"` // 告警规则配置
	Retention   time.Duration     `json:"retention"`   // 数据保留时间
	Labels      map[string]string `json:"labels"`      // 全局标签
}

// MonitoringStats 监控统计信息
type MonitoringStats struct {
	StartTime        time.Time `json:"start_time"`        // 启动时间
	LastUpdateTime   time.Time `json:"last_update_time"`  // 最后更新时间
	MetricsCollected int64     `json:"metrics_collected"` // 收集的指标数
	AlertsGenerated  int64     `json:"alerts_generated"` // 生成的告警数
	AlertsResolved   int64     `json:"alerts_resolved"`  // 解决的告警数
	ErrorsCount      int64     `json:"errors_count"`      // 错误数
	Uptime           time.Duration `json:"uptime"`       // 运行时间
}
