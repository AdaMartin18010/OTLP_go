# SeverityNumber (严重性级别)

## 📋 目录

- [SeverityNumber (严重性级别)](#severitynumber-严重性级别)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 SeverityNumber](#什么是-severitynumber)
    - [为什么需要标准化严重性](#为什么需要标准化严重性)
  - [SeverityNumber 定义](#severitynumber-定义)
    - [1. 完整级别表](#1-完整级别表)
    - [2. 级别分组](#2-级别分组)
    - [3. Protocol Buffers 定义](#3-protocol-buffers-定义)
  - [与其他日志系统的映射](#与其他日志系统的映射)
    - [1. syslog 映射](#1-syslog-映射)
    - [2. Go slog 映射](#2-go-slog-映射)
    - [3. Log4j 映射](#3-log4j-映射)
    - [4. Python logging 映射](#4-python-logging-映射)
    - [5. .NET 映射](#5-net-映射)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. 基本类型定义](#1-基本类型定义)
    - [2. slog Level 转换](#2-slog-level-转换)
    - [3. 字符串转换](#3-字符串转换)
    - [4. 级别比较](#4-级别比较)
  - [动态级别调整](#动态级别调整)
    - [1. 运行时调整](#1-运行时调整)
    - [2. 基于上下文的级别](#2-基于上下文的级别)
    - [3. 采样和过滤](#3-采样和过滤)
  - [级别使用指南](#级别使用指南)
    - [1. TRACE (1-4)](#1-trace-1-4)
    - [2. DEBUG (5-8)](#2-debug-5-8)
    - [3. INFO (9-12)](#3-info-9-12)
    - [4. WARN (13-16)](#4-warn-13-16)
    - [5. ERROR (17-20)](#5-error-17-20)
    - [6. FATAL (21-24)](#6-fatal-21-24)
  - [级别选择最佳实践](#级别选择最佳实践)
    - [1. 级别选择决策树](#1-级别选择决策树)
    - [2. 生产环境配置](#2-生产环境配置)
    - [3. 开发环境配置](#3-开发环境配置)
  - [性能优化](#性能优化)
    - [1. 快速级别检查](#1-快速级别检查)
    - [2. 级别过滤](#2-级别过滤)
    - [3. 采样策略](#3-采样策略)
  - [常见问题](#常见问题)
    - [Q1: 为什么 SeverityNumber 有 24 个级别？](#q1-为什么-severitynumber-有-24-个级别)
    - [Q2: SeverityNumber 和 SeverityText 的关系？](#q2-severitynumber-和-severitytext-的关系)
    - [Q3: 如何选择合适的严重性级别？](#q3-如何选择合适的严重性级别)
    - [Q4: 如何处理自定义级别？](#q4-如何处理自定义级别)
    - [Q5: 如何动态调整日志级别？](#q5-如何动态调整日志级别)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 SeverityNumber

**SeverityNumber** 是 OpenTelemetry Logs 的标准化严重性级别，用数值 (1-24) 表示日志的重要程度。

```text
SeverityNumber: 1 → 24
             低 ←-------→ 高
           TRACE      FATAL
```

### 为什么需要标准化严重性

```text
问题：不同日志系统使用不同的级别名称和数量
❌ syslog:    8 个级别 (EMERG, ALERT, CRIT, ERR, WARNING, NOTICE, INFO, DEBUG)
❌ Log4j:     6 个级别 (TRACE, DEBUG, INFO, WARN, ERROR, FATAL)
❌ Python:    5 个级别 (DEBUG, INFO, WARNING, ERROR, CRITICAL)
❌ slog:      4 个级别 (DEBUG, INFO, WARN, ERROR)

OpenTelemetry 解决方案:
✅ 统一的数值表示 (1-24)
✅ 兼容所有主流日志系统
✅ 精细的级别粒度
✅ 易于比较和过滤
```

---

## SeverityNumber 定义

### 1. 完整级别表

| 数值 | 名称 | 说明 | 使用场景 |
|------|------|------|----------|
| 0 | UNSPECIFIED | 未指定 | 默认值，不应使用 |
| 1 | TRACE | 最详细的追踪 | 极细粒度的调试信息 |
| 2 | TRACE2 | 追踪级别 2 | |
| 3 | TRACE3 | 追踪级别 3 | |
| 4 | TRACE4 | 追踪级别 4 | |
| 5 | DEBUG | 调试信息 | 开发和调试用 |
| 6 | DEBUG2 | 调试级别 2 | |
| 7 | DEBUG3 | 调试级别 3 | |
| 8 | DEBUG4 | 调试级别 4 | |
| 9 | INFO | 正常信息 | 常规操作信息 |
| 10 | INFO2 | 信息级别 2 | |
| 11 | INFO3 | 信息级别 3 | |
| 12 | INFO4 | 信息级别 4 | |
| 13 | WARN | 警告 | 潜在问题 |
| 14 | WARN2 | 警告级别 2 | |
| 15 | WARN3 | 警告级别 3 | |
| 16 | WARN4 | 警告级别 4 | |
| 17 | ERROR | 错误 | 需要处理的错误 |
| 18 | ERROR2 | 错误级别 2 | |
| 19 | ERROR3 | 错误级别 3 | |
| 20 | ERROR4 | 错误级别 4 | |
| 21 | FATAL | 致命错误 | 导致应用崩溃 |
| 22 | FATAL2 | 致命级别 2 | |
| 23 | FATAL3 | 致命级别 3 | |
| 24 | FATAL4 | 致命级别 4 | |

### 2. 级别分组

```text
TRACE (1-4):   极度详细的追踪信息
  ├─ 1: 最细粒度的追踪
  ├─ 2-3: 中等追踪
  └─ 4: 粗粒度追踪

DEBUG (5-8):   开发和调试信息
  ├─ 5: 标准调试
  ├─ 6-7: 详细调试
  └─ 8: 简要调试

INFO (9-12):   正常操作信息
  ├─ 9: 标准信息
  ├─ 10-11: 详细信息
  └─ 12: 简要信息

WARN (13-16):  警告信息
  ├─ 13: 标准警告
  ├─ 14-15: 重要警告
  └─ 16: 关键警告

ERROR (17-20): 错误信息
  ├─ 17: 标准错误
  ├─ 18-19: 严重错误
  └─ 20: 关键错误

FATAL (21-24): 致命错误
  ├─ 21: 标准致命
  ├─ 22-23: 严重致命
  └─ 24: 最高严重性
```

### 3. Protocol Buffers 定义

```protobuf
enum SeverityNumber {
  SEVERITY_NUMBER_UNSPECIFIED = 0;
  
  // TRACE
  SEVERITY_NUMBER_TRACE = 1;
  SEVERITY_NUMBER_TRACE2 = 2;
  SEVERITY_NUMBER_TRACE3 = 3;
  SEVERITY_NUMBER_TRACE4 = 4;
  
  // DEBUG
  SEVERITY_NUMBER_DEBUG = 5;
  SEVERITY_NUMBER_DEBUG2 = 6;
  SEVERITY_NUMBER_DEBUG3 = 7;
  SEVERITY_NUMBER_DEBUG4 = 8;
  
  // INFO
  SEVERITY_NUMBER_INFO = 9;
  SEVERITY_NUMBER_INFO2 = 10;
  SEVERITY_NUMBER_INFO3 = 11;
  SEVERITY_NUMBER_INFO4 = 12;
  
  // WARN
  SEVERITY_NUMBER_WARN = 13;
  SEVERITY_NUMBER_WARN2 = 14;
  SEVERITY_NUMBER_WARN3 = 15;
  SEVERITY_NUMBER_WARN4 = 16;
  
  // ERROR
  SEVERITY_NUMBER_ERROR = 17;
  SEVERITY_NUMBER_ERROR2 = 18;
  SEVERITY_NUMBER_ERROR3 = 19;
  SEVERITY_NUMBER_ERROR4 = 20;
  
  // FATAL
  SEVERITY_NUMBER_FATAL = 21;
  SEVERITY_NUMBER_FATAL2 = 22;
  SEVERITY_NUMBER_FATAL3 = 23;
  SEVERITY_NUMBER_FATAL4 = 24;
}
```

---

## 与其他日志系统的映射

### 1. syslog 映射

| syslog | 数值 | OpenTelemetry | 说明 |
|--------|------|---------------|------|
| DEBUG | 7 | TRACE (1-4) | 最详细 |
| INFO | 6 | DEBUG (5-8) | 调试信息 |
| NOTICE | 5 | INFO (9-12) | 正常信息 |
| WARNING | 4 | WARN (13-16) | 警告 |
| ERR | 3 | ERROR (17-20) | 错误 |
| CRIT | 2 | FATAL (21-22) | 关键 |
| ALERT | 1 | FATAL (23) | 警报 |
| EMERG | 0 | FATAL (24) | 紧急 |

**Go 实现**:

```go
func SyslogToSeverity(level int) SeverityNumber {
    switch level {
    case 7: // DEBUG
        return SeverityNumberTrace
    case 6: // INFO
        return SeverityNumberDebug
    case 5: // NOTICE
        return SeverityNumberInfo
    case 4: // WARNING
        return SeverityNumberWarn
    case 3: // ERR
        return SeverityNumberError
    case 2: // CRIT
        return SeverityNumberFatal
    case 1: // ALERT
        return SeverityNumberFatal3
    case 0: // EMERG
        return SeverityNumberFatal4
    default:
        return SeverityNumberUnspecified
    }
}
```

### 2. Go slog 映射

| slog.Level | OpenTelemetry | 说明 |
|------------|---------------|------|
| LevelDebug (-4) | DEBUG (5) | 调试 |
| LevelInfo (0) | INFO (9) | 信息 |
| LevelWarn (4) | WARN (13) | 警告 |
| LevelError (8) | ERROR (17) | 错误 |

**Go 实现**:

```go
import "log/slog"

func SlogLevelToSeverity(level slog.Level) SeverityNumber {
    switch {
    case level < slog.LevelDebug:
        return SeverityNumberTrace
    case level < slog.LevelInfo:
        return SeverityNumberDebug
    case level < slog.LevelWarn:
        return SeverityNumberInfo
    case level < slog.LevelError:
        return SeverityNumberWarn
    default:
        return SeverityNumberError
    }
}

func SeverityToSlogLevel(sev SeverityNumber) slog.Level {
    switch {
    case sev >= SeverityNumberFatal:
        return slog.LevelError + 4 // FATAL
    case sev >= SeverityNumberError:
        return slog.LevelError
    case sev >= SeverityNumberWarn:
        return slog.LevelWarn
    case sev >= SeverityNumberInfo:
        return slog.LevelInfo
    case sev >= SeverityNumberDebug:
        return slog.LevelDebug
    case sev >= SeverityNumberTrace:
        return slog.LevelDebug - 4 // TRACE
    default:
        return slog.LevelInfo
    }
}
```

### 3. Log4j 映射

| Log4j | OpenTelemetry | 说明 |
|-------|---------------|------|
| TRACE | TRACE (1) | 追踪 |
| DEBUG | DEBUG (5) | 调试 |
| INFO | INFO (9) | 信息 |
| WARN | WARN (13) | 警告 |
| ERROR | ERROR (17) | 错误 |
| FATAL | FATAL (21) | 致命 |

**Go 实现**:

```go
func Log4jToSeverity(level string) SeverityNumber {
    switch strings.ToUpper(level) {
    case "TRACE":
        return SeverityNumberTrace
    case "DEBUG":
        return SeverityNumberDebug
    case "INFO":
        return SeverityNumberInfo
    case "WARN":
        return SeverityNumberWarn
    case "ERROR":
        return SeverityNumberError
    case "FATAL":
        return SeverityNumberFatal
    default:
        return SeverityNumberUnspecified
    }
}
```

### 4. Python logging 映射

| Python | 数值 | OpenTelemetry | 说明 |
|--------|------|---------------|------|
| NOTSET | 0 | UNSPECIFIED (0) | 未设置 |
| DEBUG | 10 | DEBUG (5) | 调试 |
| INFO | 20 | INFO (9) | 信息 |
| WARNING | 30 | WARN (13) | 警告 |
| ERROR | 40 | ERROR (17) | 错误 |
| CRITICAL | 50 | FATAL (21) | 严重 |

**Go 实现**:

```go
func PythonLevelToSeverity(level int) SeverityNumber {
    switch {
    case level >= 50:
        return SeverityNumberFatal
    case level >= 40:
        return SeverityNumberError
    case level >= 30:
        return SeverityNumberWarn
    case level >= 20:
        return SeverityNumberInfo
    case level >= 10:
        return SeverityNumberDebug
    default:
        return SeverityNumberUnspecified
    }
}
```

### 5. .NET 映射

| .NET LogLevel | OpenTelemetry | 说明 |
|---------------|---------------|------|
| Trace | TRACE (1) | 追踪 |
| Debug | DEBUG (5) | 调试 |
| Information | INFO (9) | 信息 |
| Warning | WARN (13) | 警告 |
| Error | ERROR (17) | 错误 |
| Critical | FATAL (21) | 严重 |

---

## Go 1.25.1 实现

### 1. 基本类型定义

```go
package severity

// SeverityNumber 严重性数值 (1-24)
type SeverityNumber int32

const (
    SeverityNumberUnspecified SeverityNumber = 0
    
    // TRACE (1-4)
    SeverityNumberTrace  SeverityNumber = 1
    SeverityNumberTrace2 SeverityNumber = 2
    SeverityNumberTrace3 SeverityNumber = 3
    SeverityNumberTrace4 SeverityNumber = 4
    
    // DEBUG (5-8)
    SeverityNumberDebug  SeverityNumber = 5
    SeverityNumberDebug2 SeverityNumber = 6
    SeverityNumberDebug3 SeverityNumber = 7
    SeverityNumberDebug4 SeverityNumber = 8
    
    // INFO (9-12)
    SeverityNumberInfo  SeverityNumber = 9
    SeverityNumberInfo2 SeverityNumber = 10
    SeverityNumberInfo3 SeverityNumber = 11
    SeverityNumberInfo4 SeverityNumber = 12
    
    // WARN (13-16)
    SeverityNumberWarn  SeverityNumber = 13
    SeverityNumberWarn2 SeverityNumber = 14
    SeverityNumberWarn3 SeverityNumber = 15
    SeverityNumberWarn4 SeverityNumber = 16
    
    // ERROR (17-20)
    SeverityNumberError  SeverityNumber = 17
    SeverityNumberError2 SeverityNumber = 18
    SeverityNumberError3 SeverityNumber = 19
    SeverityNumberError4 SeverityNumber = 20
    
    // FATAL (21-24)
    SeverityNumberFatal  SeverityNumber = 21
    SeverityNumberFatal2 SeverityNumber = 22
    SeverityNumberFatal3 SeverityNumber = 23
    SeverityNumberFatal4 SeverityNumber = 24
)

// String 返回严重性的字符串表示
func (s SeverityNumber) String() string {
    switch {
    case s >= SeverityNumberFatal:
        return "FATAL"
    case s >= SeverityNumberError:
        return "ERROR"
    case s >= SeverityNumberWarn:
        return "WARN"
    case s >= SeverityNumberInfo:
        return "INFO"
    case s >= SeverityNumberDebug:
        return "DEBUG"
    case s >= SeverityNumberTrace:
        return "TRACE"
    default:
        return "UNSPECIFIED"
    }
}
```

### 2. slog Level 转换

```go
import "log/slog"

// FromSlogLevel 从 slog.Level 转换
func FromSlogLevel(level slog.Level) SeverityNumber {
    const (
        // slog 默认级别
        LevelTrace = slog.LevelDebug - 4 // -8
        LevelFatal = slog.LevelError + 4 // +12
    )
    
    switch {
    case level >= LevelFatal:
        return SeverityNumberFatal
    case level >= slog.LevelError:
        return SeverityNumberError
    case level >= slog.LevelWarn:
        return SeverityNumberWarn
    case level >= slog.LevelInfo:
        return SeverityNumberInfo
    case level >= slog.LevelDebug:
        return SeverityNumberDebug
    case level >= LevelTrace:
        return SeverityNumberTrace
    default:
        return SeverityNumberTrace
    }
}

// ToSlogLevel 转换为 slog.Level
func (s SeverityNumber) ToSlogLevel() slog.Level {
    switch {
    case s >= SeverityNumberFatal:
        return slog.LevelError + 4
    case s >= SeverityNumberError:
        return slog.LevelError
    case s >= SeverityNumberWarn:
        return slog.LevelWarn
    case s >= SeverityNumberInfo:
        return slog.LevelInfo
    case s >= SeverityNumberDebug:
        return slog.LevelDebug
    case s >= SeverityNumberTrace:
        return slog.LevelDebug - 4
    default:
        return slog.LevelInfo
    }
}
```

### 3. 字符串转换

```go
// ParseSeverity 从字符串解析
func ParseSeverity(text string) SeverityNumber {
    switch strings.ToUpper(text) {
    case "TRACE":
        return SeverityNumberTrace
    case "DEBUG":
        return SeverityNumberDebug
    case "INFO":
        return SeverityNumberInfo
    case "WARN", "WARNING":
        return SeverityNumberWarn
    case "ERROR":
        return SeverityNumberError
    case "FATAL", "CRITICAL":
        return SeverityNumberFatal
    default:
        return SeverityNumberUnspecified
    }
}

// MarshalText 实现 encoding.TextMarshaler
func (s SeverityNumber) MarshalText() ([]byte, error) {
    return []byte(s.String()), nil
}

// UnmarshalText 实现 encoding.TextUnmarshaler
func (s *SeverityNumber) UnmarshalText(text []byte) error {
    *s = ParseSeverity(string(text))
    return nil
}
```

### 4. 级别比较

```go
// IsEnabled 检查级别是否启用
func (s SeverityNumber) IsEnabled(minLevel SeverityNumber) bool {
    return s >= minLevel
}

// IsTrace 是否为 TRACE 级别
func (s SeverityNumber) IsTrace() bool {
    return s >= SeverityNumberTrace && s < SeverityNumberDebug
}

// IsDebug 是否为 DEBUG 级别
func (s SeverityNumber) IsDebug() bool {
    return s >= SeverityNumberDebug && s < SeverityNumberInfo
}

// IsInfo 是否为 INFO 级别
func (s SeverityNumber) IsInfo() bool {
    return s >= SeverityNumberInfo && s < SeverityNumberWarn
}

// IsWarn 是否为 WARN 级别
func (s SeverityNumber) IsWarn() bool {
    return s >= SeverityNumberWarn && s < SeverityNumberError
}

// IsError 是否为 ERROR 级别
func (s SeverityNumber) IsError() bool {
    return s >= SeverityNumberError && s < SeverityNumberFatal
}

// IsFatal 是否为 FATAL 级别
func (s SeverityNumber) IsFatal() bool {
    return s >= SeverityNumberFatal
}
```

---

## 动态级别调整

### 1. 运行时调整

```go
// LevelConfig 级别配置
type LevelConfig struct {
    minLevel atomic.Int32
}

// NewLevelConfig 创建级别配置
func NewLevelConfig(level SeverityNumber) *LevelConfig {
    cfg := &LevelConfig{}
    cfg.minLevel.Store(int32(level))
    return cfg
}

// SetLevel 设置最小级别
func (c *LevelConfig) SetLevel(level SeverityNumber) {
    c.minLevel.Store(int32(level))
}

// GetLevel 获取最小级别
func (c *LevelConfig) GetLevel() SeverityNumber {
    return SeverityNumber(c.minLevel.Load())
}

// Enabled 检查级别是否启用
func (c *LevelConfig) Enabled(level SeverityNumber) bool {
    return level >= c.GetLevel()
}

// 使用示例
config := NewLevelConfig(SeverityNumberInfo)

// 运行时调整为 DEBUG
config.SetLevel(SeverityNumberDebug)

// 检查是否启用
if config.Enabled(SeverityNumberDebug) {
    // 记录 DEBUG 日志
}
```

### 2. 基于上下文的级别

```go
// ContextKey 上下文键
type contextKey string

const logLevelKey contextKey = "log.level"

// WithLevel 在 Context 中设置级别
func WithLevel(ctx context.Context, level SeverityNumber) context.Context {
    return context.WithValue(ctx, logLevelKey, level)
}

// LevelFromContext 从 Context 获取级别
func LevelFromContext(ctx context.Context) (SeverityNumber, bool) {
    level, ok := ctx.Value(logLevelKey).(SeverityNumber)
    return level, ok
}

// 使用示例
ctx := WithLevel(context.Background(), SeverityNumberDebug)

if level, ok := LevelFromContext(ctx); ok {
    fmt.Printf("Current level: %s\n", level)
}
```

### 3. 采样和过滤

```go
// LevelSampler 级别采样器
type LevelSampler struct {
    rates map[SeverityNumber]float64
    rand  *rand.Rand
    mu    sync.Mutex
}

// NewLevelSampler 创建采样器
func NewLevelSampler() *LevelSampler {
    return &LevelSampler{
        rates: map[SeverityNumber]float64{
            SeverityNumberTrace: 0.01,  // 1% 采样
            SeverityNumberDebug: 0.1,   // 10% 采样
            SeverityNumberInfo:  1.0,   // 100% 采样
            SeverityNumberWarn:  1.0,   // 100% 采样
            SeverityNumberError: 1.0,   // 100% 采样
            SeverityNumberFatal: 1.0,   // 100% 采样
        },
        rand: rand.New(rand.NewSource(time.Now().UnixNano())),
    }
}

// ShouldSample 是否应该采样
func (s *LevelSampler) ShouldSample(level SeverityNumber) bool {
    s.mu.Lock()
    defer s.mu.Unlock()
    
    // 找到对应的基础级别
    baseLevel := s.getBaseLevel(level)
    rate, ok := s.rates[baseLevel]
    if !ok {
        rate = 1.0 // 默认全采样
    }
    
    return s.rand.Float64() < rate
}

func (s *LevelSampler) getBaseLevel(level SeverityNumber) SeverityNumber {
    switch {
    case level >= SeverityNumberFatal:
        return SeverityNumberFatal
    case level >= SeverityNumberError:
        return SeverityNumberError
    case level >= SeverityNumberWarn:
        return SeverityNumberWarn
    case level >= SeverityNumberInfo:
        return SeverityNumberInfo
    case level >= SeverityNumberDebug:
        return SeverityNumberDebug
    case level >= SeverityNumberTrace:
        return SeverityNumberTrace
    default:
        return SeverityNumberUnspecified
    }
}

// SetRate 设置采样率
func (s *LevelSampler) SetRate(level SeverityNumber, rate float64) {
    s.mu.Lock()
    defer s.mu.Unlock()
    s.rates[level] = rate
}
```

---

## 级别使用指南

### 1. TRACE (1-4)

**用途**: 极度详细的追踪信息

**使用场景**:

```go
// ✅ 函数入口/出口追踪
log.Trace(ctx, "Entering ProcessOrder", "order_id", orderID)
defer log.Trace(ctx, "Exiting ProcessOrder", "order_id", orderID)

// ✅ 循环内部追踪
for i, item := range items {
    log.Trace(ctx, "Processing item", "index", i, "item", item)
}

// ✅ 变量值追踪
log.Trace(ctx, "Variable values", "x", x, "y", y, "z", z)
```

**注意事项**:

- 仅用于开发和深度调试
- 生产环境应禁用或高度采样
- 避免记录敏感信息

### 2. DEBUG (5-8)

**用途**: 开发和调试信息

**使用场景**:

```go
// ✅ 中间计算结果
log.Debug(ctx, "Calculated total", "amount", total, "tax", tax)

// ✅ 函数参数
log.Debug(ctx, "CreateUser called", "username", username, "email", email)

// ✅ SQL 查询
log.Debug(ctx, "Executing query", "sql", query, "params", params)

// ✅ 算法步骤
log.Debug(ctx, "Sorting complete", "method", "quicksort", "duration", dur)
```

**注意事项**:

- 帮助开发者理解程序流程
- 生产环境可选择性启用
- 采样率可设置为 10-50%

### 3. INFO (9-12)

**用途**: 正常操作信息

**使用场景**:

```go
// ✅ 重要业务事件
log.Info(ctx, "User logged in", "user_id", userID, "ip", ip)

// ✅ 系统启动/关闭
log.Info(ctx, "Server started", "port", port, "version", version)

// ✅ 配置加载
log.Info(ctx, "Configuration loaded", "file", configFile)

// ✅ 定时任务
log.Info(ctx, "Scheduled job completed", "job", jobName, "duration", dur)
```

**注意事项**:

- 生产环境的默认级别
- 记录关键业务流程
- 避免过于频繁 (< 10 条/秒)

### 4. WARN (13-16)

**用途**: 警告信息，潜在问题

**使用场景**:

```go
// ✅ 可恢复的错误
log.Warn(ctx, "Failed to send email, will retry", "recipient", email, "error", err)

// ✅ 性能问题
log.Warn(ctx, "Slow query detected", "duration", dur, "threshold", threshold)

// ✅ 资源不足
log.Warn(ctx, "High memory usage", "usage", usage, "limit", limit)

// ✅ 配置问题
log.Warn(ctx, "Using default value", "key", key, "default", defaultValue)
```

**注意事项**:

- 需要关注但不紧急
- 可能需要后续处理
- 建议设置告警阈值

### 5. ERROR (17-20)

**用途**: 错误信息，需要处理

**使用场景**:

```go
// ✅ 请求失败
log.Error(ctx, "Failed to process request", "error", err, "request_id", reqID)

// ✅ 数据库错误
log.Error(ctx, "Database query failed", "error", err, "query", query)

// ✅ 外部服务失败
log.Error(ctx, "API call failed", "service", serviceName, "error", err)

// ✅ 验证失败
log.Error(ctx, "Invalid input", "field", field, "value", value, "error", err)
```

**注意事项**:

- 影响用户体验
- 需要立即关注
- 应包含足够的上下文信息
- 建议关联 Trace ID

### 6. FATAL (21-24)

**用途**: 致命错误，导致程序退出

**使用场景**:

```go
// ✅ 系统级错误
log.Fatal(ctx, "Failed to connect to database", "error", err)
os.Exit(1)

// ✅ 关键资源不可用
log.Fatal(ctx, "Required configuration missing", "key", key)
os.Exit(1)

// ✅ 无法恢复的错误
log.Fatal(ctx, "Panic recovered", "panic", r, "stack", stack)
os.Exit(1)
```

**注意事项**:

- 仅用于无法恢复的错误
- 记录后应退出程序
- 包含完整的错误信息和堆栈
- 触发 PagerDuty 等紧急告警

---

## 级别选择最佳实践

### 1. 级别选择决策树

```text
                    开始
                     |
                  发生错误？
                   /   \
                 是     否
                 |       |
            可恢复？   重要吗？
             /   \      /   \
           是     否   是     否
           |      |    |      |
         WARN  FATAL INFO  DEBUG/TRACE
```

### 2. 生产环境配置

```go
// 生产环境级别配置
type ProductionConfig struct {
    DefaultLevel SeverityNumber
    Sampling     map[SeverityNumber]float64
}

var prodConfig = ProductionConfig{
    DefaultLevel: SeverityNumberInfo,
    Sampling: map[SeverityNumber]float64{
        SeverityNumberTrace: 0.001,  // 0.1% 采样
        SeverityNumberDebug: 0.01,   // 1% 采样
        SeverityNumberInfo:  1.0,    // 100% 采样
        SeverityNumberWarn:  1.0,    // 100% 采样
        SeverityNumberError: 1.0,    // 100% 采样
        SeverityNumberFatal: 1.0,    // 100% 采样
    },
}
```

### 3. 开发环境配置

```go
// 开发环境级别配置
type DevelopmentConfig struct {
    DefaultLevel SeverityNumber
    Sampling     map[SeverityNumber]float64
}

var devConfig = DevelopmentConfig{
    DefaultLevel: SeverityNumberDebug,
    Sampling: map[SeverityNumber]float64{
        SeverityNumberTrace: 0.1,    // 10% 采样
        SeverityNumberDebug: 1.0,    // 100% 采样
        SeverityNumberInfo:  1.0,    // 100% 采样
        SeverityNumberWarn:  1.0,    // 100% 采样
        SeverityNumberError: 1.0,    // 100% 采样
        SeverityNumberFatal: 1.0,    // 100% 采样
    },
}
```

---

## 性能优化

### 1. 快速级别检查

```go
// 快速检查避免不必要的日志构建
if !logger.Enabled(SeverityNumberDebug) {
    return // 快速返回，避免构建日志
}

// 仅在启用时才构建日志
logger.Debug(ctx, "Expensive debug info", 
    "data", expensiveFunc()) // expensiveFunc() 不会被调用
```

### 2. 级别过滤

```go
// LevelFilter 级别过滤器
type LevelFilter struct {
    minLevel SeverityNumber
    next     Processor
}

func (f *LevelFilter) Process(record *LogRecord) error {
    if record.SeverityNumber < f.minLevel {
        return nil // 过滤掉
    }
    return f.next.Process(record)
}
```

### 3. 采样策略

```go
// AdaptiveSampler 自适应采样器
type AdaptiveSampler struct {
    sampler     *LevelSampler
    rateLimiter map[SeverityNumber]*rate.Limiter
}

func NewAdaptiveSampler() *AdaptiveSampler {
    return &AdaptiveSampler{
        sampler: NewLevelSampler(),
        rateLimiter: map[SeverityNumber]*rate.Limiter{
            SeverityNumberDebug: rate.NewLimiter(100, 100), // 100/s
            SeverityNumberInfo:  rate.NewLimiter(1000, 1000), // 1000/s
        },
    }
}

func (s *AdaptiveSampler) ShouldLog(level SeverityNumber) bool {
    // 高优先级总是记录
    if level >= SeverityNumberError {
        return true
    }
    
    // 速率限制
    if limiter, ok := s.rateLimiter[level]; ok {
        if !limiter.Allow() {
            return false
        }
    }
    
    // 采样
    return s.sampler.ShouldSample(level)
}
```

---

## 常见问题

### Q1: 为什么 SeverityNumber 有 24 个级别？

**A**:

```text
设计原因:
1. 兼容性: 支持所有主流日志系统的级别
2. 精细度: 提供细粒度的级别区分
3. 扩展性: 预留未来扩展空间
4. 映射: 每个主级别包含 4 个子级别

实际使用:
✅ 大多数情况使用 6 个主级别 (TRACE, DEBUG, INFO, WARN, ERROR, FATAL)
✅ 子级别用于特殊场景 (如 ERROR2 表示严重错误)
```

### Q2: SeverityNumber 和 SeverityText 的关系？

**A**:

```go
// SeverityNumber: 标准化数值 (1-24)
record.SeverityNumber = SeverityNumberInfo // 9

// SeverityText: 原始文本 (可自定义)
record.SeverityText = "INFO" // 或 "info", "Information" 等

// 关系:
// - SeverityNumber 用于过滤和比较
// - SeverityText 保留原始级别名称，方便人类阅读

// 建议: 同时设置两者
record.SeverityNumber = SeverityNumberError
record.SeverityText = record.SeverityNumber.String() // "ERROR"
```

### Q3: 如何选择合适的严重性级别？

**A**:

```text
决策流程:
1. 是否是错误? → 是 → ERROR/FATAL
2. 是否需要关注? → 是 → WARN
3. 是否是重要操作? → 是 → INFO
4. 是否用于调试? → 是 → DEBUG
5. 是否极度详细? → 是 → TRACE

示例:
✅ 用户登录成功        → INFO
✅ 数据库查询慢        → WARN
✅ API 请求失败        → ERROR
✅ 内存不足，退出      → FATAL
✅ 函数入口追踪        → TRACE
✅ 变量值调试          → DEBUG
```

### Q4: 如何处理自定义级别？

**A**:

```go
// 方案 1: 映射到标准级别
func CustomLevelToSeverity(level string) SeverityNumber {
    switch strings.ToUpper(level) {
    case "CRITICAL":
        return SeverityNumberFatal
    case "NOTICE":
        return SeverityNumberInfo2
    case "VERBOSE":
        return SeverityNumberDebug2
    default:
        return ParseSeverity(level) // 回退到标准解析
    }
}

// 方案 2: 保留在 SeverityText 中
record.SeverityNumber = SeverityNumberWarn // 标准级别
record.SeverityText = "CRITICAL"           // 自定义文本
```

### Q5: 如何动态调整日志级别？

**A**:

```go
// 1. 通过 HTTP API
http.HandleFunc("/admin/log-level", func(w http.ResponseWriter, r *http.Request) {
    if r.Method == "POST" {
        level := r.URL.Query().Get("level")
        sev := ParseSeverity(level)
        config.SetLevel(sev)
        fmt.Fprintf(w, "Log level set to %s", sev)
    }
})

// 2. 通过环境变量
func UpdateFromEnv() {
    if level := os.Getenv("LOG_LEVEL"); level != "" {
        config.SetLevel(ParseSeverity(level))
    }
}

// 3. 通过配置文件热重载
func WatchConfig(path string) {
    watcher, _ := fsnotify.NewWatcher()
    watcher.Add(path)
    
    for {
        select {
        case event := <-watcher.Events:
            if event.Op&fsnotify.Write == fsnotify.Write {
                config := loadConfig(path)
                levelConfig.SetLevel(config.LogLevel)
            }
        }
    }
}
```

---

## 参考资源

- [OpenTelemetry Logs Data Model - Severity](https://opentelemetry.io/docs/specs/otel/logs/data-model/#field-severitynumber)
- [syslog RFC 5424](https://tools.ietf.org/html/rfc5424)
- [Go slog Package](https://pkg.go.dev/log/slog)
- [01_LogRecord结构.md](./01_LogRecord结构.md)
- [03_Body与Attributes.md](./03_Body与Attributes.md)

---

**🎉 恭喜！你已经掌握了 SeverityNumber 的完整知识！**

现在你可以：

- ✅ 理解 24 个严重性级别
- ✅ 映射不同日志系统的级别
- ✅ 动态调整日志级别
- ✅ 实现采样和过滤
- ✅ 选择合适的级别
