// Package monitoring provides comprehensive alerting capabilities for OTLP Go applications.
// It includes alert rules, notification systems, and real-time alert management.
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

// AlertCondition 告警条件接口
type AlertCondition interface {
	// Evaluate 评估条件
	Evaluate(value float64, threshold float64) bool
	// GetDescription 获取描述
	GetDescription() string
}

// GreaterThanCondition 大于条件
type GreaterThanCondition struct{}

func (gtc *GreaterThanCondition) Evaluate(value float64, threshold float64) bool {
	return value > threshold
}

func (gtc *GreaterThanCondition) GetDescription() string {
	return "greater than"
}

// LessThanCondition 小于条件
type LessThanCondition struct{}

func (ltc *LessThanCondition) Evaluate(value float64, threshold float64) bool {
	return value < threshold
}

func (ltc *LessThanCondition) GetDescription() string {
	return "less than"
}

// EqualCondition 等于条件
type EqualCondition struct{}

func (ec *EqualCondition) Evaluate(value float64, threshold float64) bool {
	return value == threshold
}

func (ec *EqualCondition) GetDescription() string {
	return "equal to"
}

// NotEqualCondition 不等于条件
type NotEqualCondition struct{}

func (nec *NotEqualCondition) Evaluate(value float64, threshold float64) bool {
	return value != threshold
}

func (nec *NotEqualCondition) GetDescription() string {
	return "not equal to"
}

// AlertRuleEngine 告警规则引擎
type AlertRuleEngine struct {
	rules      map[string]*AlertRule
	conditions map[string]AlertCondition
	tracer     trace.Tracer
	mu         sync.RWMutex
}

// NewAlertRuleEngine 创建告警规则引擎
func NewAlertRuleEngine() *AlertRuleEngine {
	engine := &AlertRuleEngine{
		rules:      make(map[string]*AlertRule),
		conditions: make(map[string]AlertCondition),
		tracer:     otel.Tracer("alert-rule-engine"),
	}

	// 注册默认条件
	engine.RegisterCondition("gt", &GreaterThanCondition{})
	engine.RegisterCondition("lt", &LessThanCondition{})
	engine.RegisterCondition("eq", &EqualCondition{})
	engine.RegisterCondition("ne", &NotEqualCondition{})

	return engine
}

// RegisterCondition 注册条件
func (are *AlertRuleEngine) RegisterCondition(name string, condition AlertCondition) {
	are.mu.Lock()
	defer are.mu.Unlock()
	are.conditions[name] = condition
}

// AddRule 添加规则
func (are *AlertRuleEngine) AddRule(rule *AlertRule) error {
	are.mu.Lock()
	defer are.mu.Unlock()

	if rule.ID == "" {
		return fmt.Errorf("rule ID cannot be empty")
	}

	if _, exists := are.rules[rule.ID]; exists {
		return fmt.Errorf("rule %s already exists", rule.ID)
	}

	rule.CreatedAt = time.Now()
	rule.UpdatedAt = time.Now()
	are.rules[rule.ID] = rule

	return nil
}

// UpdateRule 更新规则
func (are *AlertRuleEngine) UpdateRule(rule *AlertRule) error {
	are.mu.Lock()
	defer are.mu.Unlock()

	if _, exists := are.rules[rule.ID]; !exists {
		return fmt.Errorf("rule %s not found", rule.ID)
	}

	rule.UpdatedAt = time.Now()
	are.rules[rule.ID] = rule

	return nil
}

// RemoveRule 删除规则
func (are *AlertRuleEngine) RemoveRule(ruleID string) error {
	are.mu.Lock()
	defer are.mu.Unlock()

	if _, exists := are.rules[ruleID]; !exists {
		return fmt.Errorf("rule %s not found", ruleID)
	}

	delete(are.rules, ruleID)
	return nil
}

// GetRule 获取规则
func (are *AlertRuleEngine) GetRule(ruleID string) (*AlertRule, error) {
	are.mu.RLock()
	defer are.mu.RUnlock()

	rule, exists := are.rules[ruleID]
	if !exists {
		return nil, fmt.Errorf("rule %s not found", ruleID)
	}

	return rule, nil
}

// ListRules 列出所有规则
func (are *AlertRuleEngine) ListRules() []*AlertRule {
	are.mu.RLock()
	defer are.mu.RUnlock()

	rules := make([]*AlertRule, 0, len(are.rules))
	for _, rule := range are.rules {
		rules = append(rules, rule)
	}

	return rules
}

// EvaluateRules 评估规则
func (are *AlertRuleEngine) EvaluateRules(ctx context.Context, metrics map[string][]MetricValue) ([]*Alert, error) {
	ctx, span := are.tracer.Start(ctx, "AlertRuleEngine.EvaluateRules")
	defer span.End()

	are.mu.RLock()
	defer are.mu.RUnlock()

	var alerts []*Alert

	for _, rule := range are.rules {
		if !rule.Enabled {
			continue
		}

		// 查找对应的指标
		metricValues, exists := metrics[rule.Metric]
		if !exists {
			continue
		}

		// 评估每个指标值
		for _, metricValue := range metricValues {
			condition, exists := are.conditions[rule.Condition]
			if !exists {
				log.Printf("Unknown condition: %s", rule.Condition)
				continue
			}

			if condition.Evaluate(metricValue.Value, rule.Threshold) {
				alert := &Alert{
					ID:          fmt.Sprintf("alert-%d", time.Now().UnixNano()),
					RuleID:      rule.ID,
					Name:        rule.Name,
					Description: rule.Description,
					Severity:    rule.Severity,
					Status:      Firing,
					Labels:      make(map[string]string),
					Annotations: make(map[string]string),
					Value:       metricValue.Value,
					Threshold:   rule.Threshold,
					StartedAt:   time.Now(),
					UpdatedAt:   time.Now(),
				}

				// 复制规则标签
				for k, v := range rule.Labels {
					alert.Labels[k] = v
				}

				// 复制指标标签
				for k, v := range metricValue.Labels {
					alert.Labels[k] = v
				}

				// 添加注释
				alert.Annotations["condition"] = condition.GetDescription()
				alert.Annotations["threshold"] = fmt.Sprintf("%.2f", rule.Threshold)
				alert.Annotations["current_value"] = fmt.Sprintf("%.2f", metricValue.Value)

				alerts = append(alerts, alert)
			}
		}
	}

	span.SetAttributes(
		attribute.Int("rules_evaluated", len(are.rules)),
		attribute.Int("alerts_generated", len(alerts)),
	)

	return alerts, nil
}

// AlertManager 告警管理器
type AlertManager struct {
	alerts    map[string]*Alert
	rules     *AlertRuleEngine
	tracer    trace.Tracer
	mu        sync.RWMutex
	notifiers []AlertNotifier
}

// NewAlertManager 创建告警管理器
func NewAlertManager() *AlertManager {
	return &AlertManager{
		alerts:    make(map[string]*Alert),
		rules:     NewAlertRuleEngine(),
		tracer:    otel.Tracer("alert-manager"),
		notifiers: make([]AlertNotifier, 0),
	}
}

// AddNotifier 添加通知器
func (am *AlertManager) AddNotifier(notifier AlertNotifier) {
	am.mu.Lock()
	defer am.mu.Unlock()
	am.notifiers = append(am.notifiers, notifier)
}

// ProcessAlerts 处理告警
func (am *AlertManager) ProcessAlerts(ctx context.Context, metrics map[string][]MetricValue) error {
	ctx, span := am.tracer.Start(ctx, "AlertManager.ProcessAlerts")
	defer span.End()

	// 评估规则
	newAlerts, err := am.rules.EvaluateRules(ctx, metrics)
	if err != nil {
		span.RecordError(err)
		return fmt.Errorf("failed to evaluate rules: %w", err)
	}

	// 处理新告警
	for _, alert := range newAlerts {
		if err := am.handleAlert(ctx, alert); err != nil {
			span.RecordError(err)
			log.Printf("Failed to handle alert %s: %v", alert.ID, err)
		}
	}

	// 检查已解决的告警
	am.checkResolvedAlerts(ctx)

	span.SetAttributes(attribute.Int("alerts_processed", len(newAlerts)))

	return nil
}

// handleAlert 处理单个告警
func (am *AlertManager) handleAlert(ctx context.Context, alert *Alert) error {
	ctx, span := am.tracer.Start(ctx, "AlertManager.handleAlert")
	defer span.End()

	am.mu.Lock()
	defer am.mu.Unlock()

	// 检查是否已存在相同告警
	existingAlert, exists := am.alerts[alert.ID]
	if exists {
		// 更新现有告警
		existingAlert.UpdatedAt = time.Now()
		existingAlert.Value = alert.Value
		existingAlert.Status = Firing
	} else {
		// 添加新告警
		am.alerts[alert.ID] = alert
		existingAlert = alert
	}

	// 发送通知
	for _, notifier := range am.notifiers {
		if err := notifier.SendAlert(ctx, existingAlert); err != nil {
			span.RecordError(err)
			log.Printf("Failed to send alert notification: %v", err)
		}
	}

	span.SetAttributes(
		attribute.String("alert.id", alert.ID),
		attribute.String("alert.name", alert.Name),
		attribute.String("alert.severity", string(alert.Severity)),
		attribute.String("alert.status", string(alert.Status)),
	)

	return nil
}

// checkResolvedAlerts 检查已解决的告警
func (am *AlertManager) checkResolvedAlerts(ctx context.Context) {
	ctx, span := am.tracer.Start(ctx, "AlertManager.checkResolvedAlerts")
	defer span.End()

	am.mu.Lock()
	defer am.mu.Unlock()

	for _, alert := range am.alerts {
		if alert.Status == Firing {
			// 检查告警是否应该被解决
			// 这里可以添加更复杂的逻辑来判断告警是否已解决
			// 例如：检查指标值是否回到正常范围
		}
	}

	span.SetAttributes(attribute.Int("alerts_checked", len(am.alerts)))
}

// GetAlerts 获取告警列表
func (am *AlertManager) GetAlerts() []*Alert {
	am.mu.RLock()
	defer am.mu.RUnlock()

	alerts := make([]*Alert, 0, len(am.alerts))
	for _, alert := range am.alerts {
		alerts = append(alerts, alert)
	}

	return alerts
}

// GetActiveAlerts 获取活跃告警
func (am *AlertManager) GetActiveAlerts() []*Alert {
	am.mu.RLock()
	defer am.mu.RUnlock()

	var activeAlerts []*Alert
	for _, alert := range am.alerts {
		if alert.Status == Firing {
			activeAlerts = append(activeAlerts, alert)
		}
	}

	return activeAlerts
}

// ResolveAlert 解决告警
func (am *AlertManager) ResolveAlert(alertID string) error {
	am.mu.Lock()
	defer am.mu.Unlock()

	alert, exists := am.alerts[alertID]
	if !exists {
		return fmt.Errorf("alert %s not found", alertID)
	}

	alert.Status = Resolved
	alert.UpdatedAt = time.Now()
	now := time.Now()
	alert.ResolvedAt = &now

	return nil
}

// AlertNotifier 告警通知器接口
type AlertNotifier interface {
	// SendAlert 发送告警
	SendAlert(ctx context.Context, alert *Alert) error
	// GetName 获取名称
	GetName() string
}

// ConsoleAlertNotifier 控制台告警通知器
type ConsoleAlertNotifier struct {
	name string
}

// NewConsoleAlertNotifier 创建控制台告警通知器
func NewConsoleAlertNotifier() *ConsoleAlertNotifier {
	return &ConsoleAlertNotifier{
		name: "console",
	}
}

// SendAlert 发送告警到控制台
func (can *ConsoleAlertNotifier) SendAlert(ctx context.Context, alert *Alert) error {
	log.Printf("[ALERT] %s - %s: %s (Value: %.2f, Threshold: %.2f)",
		alert.Severity,
		alert.Name,
		alert.Description,
		alert.Value,
		alert.Threshold,
	)
	return nil
}

// GetName 获取名称
func (can *ConsoleAlertNotifier) GetName() string {
	return can.name
}

// FileAlertNotifier 文件告警通知器
type FileAlertNotifier struct {
	name     string
	filename string
}

// NewFileAlertNotifier 创建文件告警通知器
func NewFileAlertNotifier(filename string) *FileAlertNotifier {
	return &FileAlertNotifier{
		name:     "file",
		filename: filename,
	}
}

// SendAlert 发送告警到文件
func (fan *FileAlertNotifier) SendAlert(ctx context.Context, alert *Alert) error {
	// 这里可以实现将告警写入文件的逻辑
	log.Printf("[FILE ALERT] Writing alert %s to file %s", alert.ID, fan.filename)
	return nil
}

// GetName 获取名称
func (fan *FileAlertNotifier) GetName() string {
	return fan.name
}

// 全局告警管理器实例
var (
	globalAlertManager *AlertManager
	alertManagerOnce   sync.Once
)

// InitGlobalAlertManager 初始化全局告警管理器
func InitGlobalAlertManager() *AlertManager {
	alertManagerOnce.Do(func() {
		globalAlertManager = NewAlertManager()

		// 添加默认通知器
		globalAlertManager.AddNotifier(NewConsoleAlertNotifier())
		globalAlertManager.AddNotifier(NewFileAlertNotifier("alerts.log"))
	})
	return globalAlertManager
}

// GetGlobalAlertManager 获取全局告警管理器
func GetGlobalAlertManager() *AlertManager {
	if globalAlertManager == nil {
		return InitGlobalAlertManager()
	}
	return globalAlertManager
}
