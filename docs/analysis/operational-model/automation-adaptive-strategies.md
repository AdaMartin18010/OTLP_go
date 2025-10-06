# OTLP 运维自动化与自适应策略

## 目录

- [OTLP 运维自动化与自适应策略](#otlp-运维自动化与自适应策略)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. 自动化运维架构](#2-自动化运维架构)
  - [3. 自适应采样策略](#3-自适应采样策略)
  - [4. 自动伸缩策略](#4-自动伸缩策略)
  - [5. 自愈机制](#5-自愈机制)
  - [6. 智能告警](#6-智能告警)
  - [7. 配置自动化](#7-配置自动化)
  - [8. 容量规划](#8-容量规划)
  - [9. 成本优化](#9-成本优化)
  - [10. 参考文献](#10-参考文献)

## 1. 概述

本文档聚焦于 OTLP 系统的**自动化运维**和**自适应策略**,实现"无人值守"的智能运维。

**核心目标**:

1. 自动化: 减少人工干预
2. 自适应: 根据负载动态调整
3. 自愈: 自动检测和修复故障
4. 智能化: 基于 ML 的预测和优化

## 2. 自动化运维架构

**AIOps 架构**:

```text
┌─────────────────────────────────────────────────────────┐
│                   Data Collection                       │
│  Traces │ Metrics │ Logs │ Events │ Topology            │
└────────────────────┬────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────┐
│                 Data Processing                         │
│  • Aggregation  • Correlation  • Feature Extraction     │
└────────────────────┬────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────┐
│                 AI/ML Engine                            │
│  • Anomaly Detection  • Root Cause Analysis             │
│  • Prediction  • Optimization                           │
└────────────────────┬────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────┐
│              Decision & Automation                      │
│  • Auto-scaling  • Auto-remediation  • Auto-tuning      │
└────────────────────┬────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────┐
│                 Execution Layer                         │
│  Kubernetes │ OPAMP │ Configuration Management          │
└─────────────────────────────────────────────────────────┘
```

**实现**:

```go
type AIOpsEngine struct {
    collector    DataCollector
    processor    DataProcessor
    mlEngine     MLEngine
    executor     AutomationExecutor
    knowledge    KnowledgeBase
}

func (aiops *AIOpsEngine) Run(ctx context.Context) {
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            // 1. 收集数据
            data := aiops.collector.Collect()
            
            // 2. 处理数据
            features := aiops.processor.Process(data)
            
            // 3. AI 分析
            insights := aiops.mlEngine.Analyze(features)
            
            // 4. 决策
            actions := aiops.decide(insights)
            
            // 5. 执行
            for _, action := range actions {
                if err := aiops.executor.Execute(action); err != nil {
                    log.Errorf("Failed to execute action: %v", err)
                } else {
                    // 6. 更新知识库
                    aiops.knowledge.Update(insights, action)
                }
            }
            
        case <-ctx.Done():
            return
        }
    }
}
```

## 3. 自适应采样策略

**多维度自适应采样**:

```go
type AdaptiveSampler struct {
    // 基础配置
    baseRate      float64
    minRate       float64
    maxRate       float64
    
    // 动态因子
    loadFactor    float64
    errorFactor   float64
    latencyFactor float64
    
    // 历史统计
    history       *SamplingHistory
    
    // ML 模型
    predictor     *SamplingPredictor
}

func (as *AdaptiveSampler) ShouldSample(span Span) bool {
    // 1. 计算基础采样率
    rate := as.baseRate
    
    // 2. 根据系统负载调整
    load := getSystemLoad()
    if load > 0.8 {
        rate *= as.loadFactor  // 高负载降低采样率
    }
    
    // 3. 错误 Span 提高采样率
    if span.Status == "ERROR" {
        rate *= as.errorFactor
    }
    
    // 4. 慢请求提高采样率
    if span.Duration() > getP95Latency() {
        rate *= as.latencyFactor
    }
    
    // 5. 重要服务提高采样率
    if as.isCriticalService(span.ServiceName) {
        rate *= 2.0
    }
    
    // 6. ML 预测调整
    if as.predictor != nil {
        mlRate := as.predictor.PredictSamplingRate(span)
        rate = 0.7*rate + 0.3*mlRate  // 加权平均
    }
    
    // 7. 限制范围
    rate = math.Max(as.minRate, math.Min(as.maxRate, rate))
    
    // 8. 采样决策
    return rand.Float64() < rate
}

// ML 采样率预测器
type SamplingPredictor struct {
    model *NeuralNetwork
}

func (sp *SamplingPredictor) PredictSamplingRate(span Span) float64 {
    features := []float64{
        float64(span.Duration().Milliseconds()),
        float64(len(span.Attributes)),
        sp.serviceImportance(span.ServiceName),
        sp.timeOfDay(),
        sp.dayOfWeek(),
    }
    
    return sp.model.Predict(features)[0]
}
```

**采样率动态调整**:

```go
type SamplingController struct {
    pid        *PIDController
    targetCPU  float64
    targetMem  float64
    currentRate atomic.Value
}

func (sc *SamplingController) AdjustRate() {
    ticker := time.NewTicker(10 * time.Second)
    defer ticker.Stop()
    
    for range ticker.C {
        // 1. 获取当前资源使用率
        cpuUsage := getCPUUsage()
        memUsage := getMemoryUsage()
        
        // 2. PID 控制器计算调整量
        cpuAdjust := sc.pid.Update(cpuUsage)
        memAdjust := sc.pid.Update(memUsage)
        
        // 3. 综合调整
        adjustment := (cpuAdjust + memAdjust) / 2
        
        // 4. 应用新采样率
        currentRate := sc.currentRate.Load().(float64)
        newRate := currentRate + adjustment
        newRate = math.Max(0.01, math.Min(1.0, newRate))
        
        sc.currentRate.Store(newRate)
        
        log.Infof("Adjusted sampling rate: %.2f%% -> %.2f%%",
            currentRate*100, newRate*100)
    }
}
```

## 4. 自动伸缩策略

**基于预测的自动伸缩**:

```go
type PredictiveAutoscaler struct {
    predictor    *LoadPredictor
    scaler       *K8sScaler
    minReplicas  int
    maxReplicas  int
    lookAhead    time.Duration
}

func (pa *PredictiveAutoscaler) Scale() {
    // 1. 预测未来负载
    futureLoad := pa.predictor.PredictLoad(pa.lookAhead)
    
    // 2. 计算所需副本数
    requiredReplicas := pa.calculateReplicas(futureLoad)
    
    // 3. 获取当前副本数
    currentReplicas := pa.scaler.GetReplicas()
    
    // 4. 决策
    if requiredReplicas > currentReplicas {
        // 提前扩容
        pa.scaler.ScaleTo(requiredReplicas)
        log.Infof("Proactive scale up: %d -> %d", currentReplicas, requiredReplicas)
    } else if requiredReplicas < currentReplicas {
        // 延迟缩容 (避免频繁抖动)
        time.Sleep(5 * time.Minute)
        if pa.predictor.PredictLoad(pa.lookAhead) < currentLoad() {
            pa.scaler.ScaleTo(requiredReplicas)
            log.Infof("Scale down: %d -> %d", currentReplicas, requiredReplicas)
        }
    }
}

// 负载预测器 (LSTM)
type LoadPredictor struct {
    model *LSTMModel
    history []float64
}

func (lp *LoadPredictor) PredictLoad(horizon time.Duration) float64 {
    // 使用 LSTM 预测未来负载
    steps := int(horizon.Minutes())
    predictions := lp.model.Forecast(lp.history, steps)
    
    // 返回预测的峰值
    return max(predictions...)
}
```

**多维度伸缩策略**:

```go
type MultiDimensionalScaler struct {
    cpuScaler    *CPUBasedScaler
    memoryScaler *MemoryBasedScaler
    queueScaler  *QueueBasedScaler
    customScaler *CustomMetricScaler
}

func (mds *MultiDimensionalScaler) Decide() int {
    // 1. 各维度独立计算所需副本数
    cpuReplicas := mds.cpuScaler.CalculateReplicas()
    memReplicas := mds.memoryScaler.CalculateReplicas()
    queueReplicas := mds.queueScaler.CalculateReplicas()
    customReplicas := mds.customScaler.CalculateReplicas()
    
    // 2. 取最大值 (保守策略)
    return max(cpuReplicas, memReplicas, queueReplicas, customReplicas)
}

// 基于队列长度的伸缩
type QueueBasedScaler struct {
    targetQueueLength int
    processingRate    float64
}

func (qbs *QueueBasedScaler) CalculateReplicas() int {
    currentQueueLength := getQueueLength()
    
    // 计算处理完队列所需的副本数
    requiredReplicas := int(math.Ceil(
        float64(currentQueueLength) / (qbs.processingRate * 60),
    ))
    
    return requiredReplicas
}
```

## 5. 自愈机制

**自动故障检测与恢复**:

```go
type SelfHealingSystem struct {
    detectors []FaultDetector
    healers   map[FaultType]Healer
    history   *HealingHistory
}

type FaultDetector interface {
    Detect() (FaultType, Severity, error)
}

type Healer interface {
    Heal(fault Fault) error
    Verify() bool
}

func (shs *SelfHealingSystem) Run(ctx context.Context) {
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            // 1. 检测故障
            for _, detector := range shs.detectors {
                faultType, severity, err := detector.Detect()
                if err != nil {
                    continue
                }
                
                fault := Fault{
                    Type:      faultType,
                    Severity:  severity,
                    DetectedAt: time.Now(),
                }
                
                // 2. 查找对应的修复器
                healer, ok := shs.healers[faultType]
                if !ok {
                    log.Warnf("No healer for fault type: %v", faultType)
                    continue
                }
                
                // 3. 执行修复
                if err := healer.Heal(fault); err != nil {
                    log.Errorf("Failed to heal fault: %v", err)
                    shs.escalate(fault)
                    continue
                }
                
                // 4. 验证修复
                if !healer.Verify() {
                    log.Warnf("Healing verification failed")
                    shs.escalate(fault)
                    continue
                }
                
                // 5. 记录成功修复
                shs.history.Record(fault, "healed")
                log.Infof("Successfully healed fault: %v", faultType)
            }
            
        case <-ctx.Done():
            return
        }
    }
}

// 内存泄漏检测器
type MemoryLeakDetector struct {
    threshold float64
    window    time.Duration
}

func (mld *MemoryLeakDetector) Detect() (FaultType, Severity, error) {
    memUsage := getMemoryUsageHistory(mld.window)
    
    // 计算内存增长趋势
    trend := calculateTrend(memUsage)
    
    if trend > mld.threshold {
        return MemoryLeak, High, nil
    }
    
    return NoFault, Low, nil
}

// 重启修复器
type RestartHealer struct {
    k8sClient kubernetes.Interface
}

func (rh *RestartHealer) Heal(fault Fault) error {
    podName := fault.Metadata["pod_name"]
    namespace := fault.Metadata["namespace"]
    
    // 删除 Pod (由 Deployment 自动重建)
    return rh.k8sClient.CoreV1().Pods(namespace).Delete(
        context.Background(),
        podName,
        metav1.DeleteOptions{},
    )
}

func (rh *RestartHealer) Verify() bool {
    // 等待 Pod 重启
    time.Sleep(30 * time.Second)
    
    // 检查 Pod 状态
    pod := getPod(fault.Metadata["pod_name"])
    return pod.Status.Phase == "Running"
}
```

## 6. 智能告警

**基于 ML 的异常检测告警**:

```go
type IntelligentAlerting struct {
    detector     *AnomalyDetector
    correlator   *AlertCorrelator
    deduplicator *AlertDeduplicator
    prioritizer  *AlertPrioritizer
}

func (ia *IntelligentAlerting) ProcessMetrics(metrics []MetricPoint) []Alert {
    var alerts []Alert
    
    // 1. 异常检测
    for _, metric := range metrics {
        if ia.detector.IsAnomaly(metric) {
            alert := Alert{
                Metric:    metric.Name,
                Value:     metric.Value,
                Timestamp: metric.Timestamp,
            }
            alerts = append(alerts, alert)
        }
    }
    
    // 2. 告警关联
    alerts = ia.correlator.Correlate(alerts)
    
    // 3. 去重
    alerts = ia.deduplicator.Deduplicate(alerts)
    
    // 4. 优先级排序
    alerts = ia.prioritizer.Prioritize(alerts)
    
    return alerts
}

// 基于 Isolation Forest 的异常检测
type IsolationForestDetector struct {
    model *IsolationForest
    threshold float64
}

func (ifd *IsolationForestDetector) IsAnomaly(metric MetricPoint) bool {
    features := []float64{
        metric.Value,
        metric.Rate(),
        metric.Variance(),
        metric.Trend(),
    }
    
    score := ifd.model.AnomalyScore(features)
    return score > ifd.threshold
}

// 告警关联器
type AlertCorrelator struct {
    graph *CausalGraph
}

func (ac *AlertCorrelator) Correlate(alerts []Alert) []Alert {
    var correlated []Alert
    
    // 构建告警图
    alertGraph := ac.buildAlertGraph(alerts)
    
    // 查找根因告警
    rootAlerts := alertGraph.FindRoots()
    
    // 只保留根因告警
    for _, alert := range alerts {
        if contains(rootAlerts, alert) {
            correlated = append(correlated, alert)
        }
    }
    
    return correlated
}
```

**告警疲劳缓解**:

```go
type AlertFatigueReducer struct {
    silencer    *AlertSilencer
    aggregator  *AlertAggregator
    throttler   *AlertThrottler
}

// 告警静默
type AlertSilencer struct {
    rules []SilenceRule
}

type SilenceRule struct {
    Pattern   string
    StartTime time.Time
    EndTime   time.Time
    Reason    string
}

func (as *AlertSilencer) ShouldSilence(alert Alert) bool {
    for _, rule := range as.rules {
        if matchPattern(alert, rule.Pattern) {
            now := time.Now()
            if now.After(rule.StartTime) && now.Before(rule.EndTime) {
                return true
            }
        }
    }
    return false
}

// 告警聚合
type AlertAggregator struct {
    window time.Duration
}

func (aa *AlertAggregator) Aggregate(alerts []Alert) []Alert {
    grouped := make(map[string][]Alert)
    
    // 按服务分组
    for _, alert := range alerts {
        service := alert.Labels["service"]
        grouped[service] = append(grouped[service], alert)
    }
    
    // 聚合同服务的告警
    var aggregated []Alert
    for service, group := range grouped {
        if len(group) > 5 {
            // 多个告警聚合为一个
            aggregated = append(aggregated, Alert{
                Summary: fmt.Sprintf("%d alerts for service %s", len(group), service),
                Count:   len(group),
            })
        } else {
            aggregated = append(aggregated, group...)
        }
    }
    
    return aggregated
}

// 告警限流
type AlertThrottler struct {
    rateLimiter *rate.Limiter
}

func (at *AlertThrottler) ShouldSend(alert Alert) bool {
    return at.rateLimiter.Allow()
}
```

## 7. 配置自动化

**GitOps 配置管理**:

```go
type GitOpsController struct {
    gitRepo      *GitRepository
    k8sClient    kubernetes.Interface
    opampClient  *OPAMPClient
    reconciler   *Reconciler
}

func (gc *GitOpsController) Reconcile(ctx context.Context) {
    ticker := time.NewTicker(1 * time.Minute)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            // 1. 拉取最新配置
            latestCommit := gc.gitRepo.GetLatestCommit()
            
            // 2. 对比当前配置
            currentConfig := gc.getCurrentConfig()
            desiredConfig := gc.parseConfig(latestCommit)
            
            // 3. 计算差异
            diff := gc.reconciler.Diff(currentConfig, desiredConfig)
            
            if len(diff) == 0 {
                continue
            }
            
            // 4. 应用变更
            for _, change := range diff {
                if err := gc.applyChange(change); err != nil {
                    log.Errorf("Failed to apply change: %v", err)
                    gc.rollback(change)
                }
            }
            
            // 5. 验证
            if !gc.validate() {
                gc.rollbackToCommit(currentConfig.Commit)
            }
            
        case <-ctx.Done():
            return
        }
    }
}

// 配置验证
type ConfigValidator struct {
    rules []ValidationRule
}

func (cv *ConfigValidator) Validate(config *Config) error {
    for _, rule := range cv.rules {
        if err := rule.Validate(config); err != nil {
            return fmt.Errorf("validation failed: %w", err)
        }
    }
    return nil
}

// 示例验证规则
var ValidationRules = []ValidationRule{
    {
        Name: "sampling_rate_range",
        Validate: func(config *Config) error {
            if config.SamplingRate < 0 || config.SamplingRate > 1 {
                return errors.New("sampling rate must be between 0 and 1")
            }
            return nil
        },
    },
    {
        Name: "required_fields",
        Validate: func(config *Config) error {
            if config.ServiceName == "" {
                return errors.New("service name is required")
            }
            return nil
        },
    },
}
```

**A/B 测试配置**:

```go
type ABTestingController struct {
    variants map[string]*Config
    splitter *TrafficSplitter
}

func (abt *ABTestingController) GetConfig(userID string) *Config {
    // 根据用户 ID 分配配置变体
    variant := abt.splitter.Assign(userID)
    return abt.variants[variant]
}

type TrafficSplitter struct {
    variants map[string]float64  // variant -> percentage
}

func (ts *TrafficSplitter) Assign(userID string) string {
    // 一致性哈希确保同一用户总是分配到同一变体
    hash := crc32.ChecksumIEEE([]byte(userID))
    percentage := float64(hash%100) / 100.0
    
    cumulative := 0.0
    for variant, weight := range ts.variants {
        cumulative += weight
        if percentage < cumulative {
            return variant
        }
    }
    
    return "default"
}

// 示例: 50% 用户使用新配置
var ABTest = ABTestingController{
    variants: map[string]*Config{
        "control": {SamplingRate: 0.1},
        "treatment": {SamplingRate: 0.2},
    },
    splitter: &TrafficSplitter{
        variants: map[string]float64{
            "control":   0.5,
            "treatment": 0.5,
        },
    },
}
```

## 8. 容量规划

**基于历史数据的容量预测**:

```go
type CapacityPlanner struct {
    predictor *TimeSeriesPredictor
    history   *HistoricalData
}

func (cp *CapacityPlanner) PlanCapacity(horizon time.Duration) CapacityPlan {
    // 1. 预测未来负载
    futureLoad := cp.predictor.Forecast(cp.history.Load, horizon)
    
    // 2. 计算所需资源
    requiredCPU := cp.calculateCPU(futureLoad)
    requiredMemory := cp.calculateMemory(futureLoad)
    requiredStorage := cp.calculateStorage(futureLoad)
    
    // 3. 添加安全余量 (20%)
    requiredCPU *= 1.2
    requiredMemory *= 1.2
    requiredStorage *= 1.2
    
    // 4. 生成容量计划
    return CapacityPlan{
        Horizon:         horizon,
        RequiredCPU:     requiredCPU,
        RequiredMemory:  requiredMemory,
        RequiredStorage: requiredStorage,
        EstimatedCost:   cp.calculateCost(requiredCPU, requiredMemory, requiredStorage),
    }
}

// 季节性分析
type SeasonalityAnalyzer struct {
    period time.Duration
}

func (sa *SeasonalityAnalyzer) Analyze(data []float64) SeasonalPattern {
    // 使用 STL (Seasonal and Trend decomposition using Loess)
    trend, seasonal, residual := stlDecompose(data, sa.period)
    
    return SeasonalPattern{
        Trend:    trend,
        Seasonal: seasonal,
        Residual: residual,
    }
}

// 容量优化建议
func (cp *CapacityPlanner) OptimizationRecommendations() []Recommendation {
    var recommendations []Recommendation
    
    // 1. 识别过度配置
    utilization := cp.calculateUtilization()
    if utilization < 0.5 {
        recommendations = append(recommendations, Recommendation{
            Type:        "DOWNSIZE",
            Description: "Resource utilization is low, consider downsizing",
            Impact:      "Cost savings: $X/month",
        })
    }
    
    // 2. 识别瓶颈
    bottlenecks := cp.identifyBottlenecks()
    for _, bottleneck := range bottlenecks {
        recommendations = append(recommendations, Recommendation{
            Type:        "SCALE_UP",
            Description: fmt.Sprintf("Bottleneck detected in %s", bottleneck),
            Impact:      "Improved performance",
        })
    }
    
    // 3. 成本优化
    if cp.canUseSpotInstances() {
        recommendations = append(recommendations, Recommendation{
            Type:        "USE_SPOT",
            Description: "Use spot instances for non-critical workloads",
            Impact:      "Cost savings: 70%",
        })
    }
    
    return recommendations
}
```

## 9. 成本优化

**智能资源调度**:

```go
type CostOptimizer struct {
    scheduler *ResourceScheduler
    pricer    *CloudPricer
}

func (co *CostOptimizer) OptimizeScheduling() {
    // 1. 获取当前工作负载
    workloads := co.getWorkloads()
    
    // 2. 分类工作负载
    critical := []Workload{}
    normal := []Workload{}
    batch := []Workload{}
    
    for _, wl := range workloads {
        switch wl.Priority {
        case "critical":
            critical = append(critical, wl)
        case "normal":
            normal = append(normal, wl)
        case "batch":
            batch = append(batch, wl)
        }
    }
    
    // 3. 优化调度
    // 关键工作负载 -> On-Demand 实例
    co.scheduler.Schedule(critical, "on-demand")
    
    // 普通工作负载 -> Reserved 实例
    co.scheduler.Schedule(normal, "reserved")
    
    // 批处理工作负载 -> Spot 实例
    co.scheduler.Schedule(batch, "spot")
}

// 成本分析
type CostAnalyzer struct {
    billing *BillingData
}

func (ca *CostAnalyzer) Analyze() CostReport {
    // 1. 按服务分组
    byService := ca.groupByService()
    
    // 2. 按资源类型分组
    byResource := ca.groupByResource()
    
    // 3. 识别成本异常
    anomalies := ca.detectAnomalies()
    
    // 4. 生成优化建议
    recommendations := ca.generateRecommendations()
    
    return CostReport{
        TotalCost:       ca.billing.Total,
        ByService:       byService,
        ByResource:      byResource,
        Anomalies:       anomalies,
        Recommendations: recommendations,
    }
}

// 示例优化策略
var CostOptimizationStrategies = []Strategy{
    {
        Name: "Right-sizing",
        Description: "Adjust instance sizes based on actual usage",
        Savings: "15-30%",
    },
    {
        Name: "Spot Instances",
        Description: "Use spot instances for fault-tolerant workloads",
        Savings: "60-70%",
    },
    {
        Name: "Reserved Instances",
        Description: "Commit to 1-3 year terms for predictable workloads",
        Savings: "30-50%",
    },
    {
        Name: "Auto-scaling",
        Description: "Scale down during off-peak hours",
        Savings: "20-40%",
    },
}
```

**数据生命周期管理**:

```go
type DataLifecycleManager struct {
    policies []RetentionPolicy
}

type RetentionPolicy struct {
    DataType  string
    HotTier   time.Duration  // SSD
    WarmTier  time.Duration  // HDD
    ColdTier  time.Duration  // Object Storage
    Archive   time.Duration  // Glacier
}

func (dlm *DataLifecycleManager) ApplyPolicies() {
    for _, policy := range dlm.policies {
        // 1. 查找过期数据
        hotExpired := dlm.findExpiredData(policy.DataType, policy.HotTier)
        warmExpired := dlm.findExpiredData(policy.DataType, policy.WarmTier)
        coldExpired := dlm.findExpiredData(policy.DataType, policy.ColdTier)
        
        // 2. 迁移数据
        dlm.moveToWarm(hotExpired)
        dlm.moveToCold(warmExpired)
        dlm.moveToArchive(coldExpired)
        
        // 3. 删除归档过期数据
        archiveExpired := dlm.findExpiredData(policy.DataType, policy.Archive)
        dlm.delete(archiveExpired)
    }
}

// 示例策略
var DefaultRetentionPolicies = []RetentionPolicy{
    {
        DataType: "traces",
        HotTier:  7 * 24 * time.Hour,   // 7 天 SSD
        WarmTier: 30 * 24 * time.Hour,  // 30 天 HDD
        ColdTier: 90 * 24 * time.Hour,  // 90 天对象存储
        Archive:  365 * 24 * time.Hour, // 1 年归档
    },
    {
        DataType: "metrics",
        HotTier:  30 * 24 * time.Hour,
        WarmTier: 90 * 24 * time.Hour,
        ColdTier: 365 * 24 * time.Hour,
        Archive:  0,  // 不归档,直接删除
    },
}
```

## 10. 参考文献

1. **AIOps**:
   - Dang, Y., et al. "AIOps: Real-World Challenges and Research Innovations" (ICSE 2019)
   - Soldani, J., & Brogi, A. "Anomaly Detection and Failure Root Cause Analysis in (Micro) Service-Based Cloud Applications" (2020)

2. **自动化运维**:
   - Beyer, B., et al. "The Site Reliability Workbook" (Google SRE, 2018)
   - Limoncelli, T., et al. "The Practice of Cloud System Administration" (2014)

3. **机器学习**:
   - Goodfellow, I., et al. "Deep Learning" (2016)
   - Géron, A. "Hands-On Machine Learning with Scikit-Learn, Keras, and TensorFlow" (2019)

4. **成本优化**:
   - AWS Well-Architected Framework - Cost Optimization Pillar
   - FinOps Foundation. "Cloud FinOps" (O'Reilly, 2021)

5. **相关文档**:
   - `docs/analysis/operational-model/fault-tolerance-debugging-monitoring.md` - 容错/排错/监测
   - `docs/analysis/computational-model/distributed-systems-theory.md` - 分布式系统理论
   - `docs/opamp/overview.md` - OPAMP 控制平面
