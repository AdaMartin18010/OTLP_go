# Collector Processor 配置详解

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月8日

---

## 目录

- [Collector Processor 配置详解](#collector-processor-配置详解)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. Batch Processor](#2-batch-processor)
    - [2.1 配置参数](#21-配置参数)
    - [2.2 参数说明](#22-参数说明)
    - [2.3 使用示例](#23-使用示例)
    - [2.4 最佳实践](#24-最佳实践)
  - [3. Memory Limiter Processor](#3-memory-limiter-processor)
    - [3.1 配置示例](#31-配置示例)
    - [3.2 参数说明](#32-参数说明)
    - [3.3 配置计算](#33-配置计算)
    - [3.4 最佳实践](#34-最佳实践)
  - [4. Attributes Processor](#4-attributes-processor)
    - [4.1 配置示例](#41-配置示例)
    - [4.2 Action类型](#42-action类型)
    - [4.3 高级配置](#43-高级配置)
  - [5. Resource Processor](#5-resource-processor)
    - [5.1 配置示例](#51-配置示例)
    - [5.2 与Attributes Processor对比](#52-与attributes-processor对比)
  - [6. Filter Processor](#6-filter-processor)
    - [6.1 配置示例](#61-配置示例)
    - [6.2 过滤条件语法](#62-过滤条件语法)
    - [6.3 实用过滤场景](#63-实用过滤场景)
  - [7. Transform Processor](#7-transform-processor)
    - [7.1 配置示例](#71-配置示例)
    - [7.2 OTTL函数](#72-ottl函数)
    - [7.3 高级转换](#73-高级转换)
  - [8. Tail Sampling Processor](#8-tail-sampling-processor)
    - [8.1 配置示例](#81-配置示例)
    - [8.2 策略类型](#82-策略类型)
    - [8.3 完整策略配置](#83-完整策略配置)
  - [9. Processor最佳实践](#9-processor最佳实践)
    - [9.1 Pipeline顺序](#91-pipeline顺序)
    - [9.2 性能优化](#92-性能优化)
    - [9.3 配置检查清单](#93-配置检查清单)
  - [10. 完整配置示例](#10-完整配置示例)
    - [10.1 生产环境配置](#101-生产环境配置)
    - [10.2 开发环境配置](#102-开发环境配置)
  - [11. 参考资源](#11-参考资源)
    - [官方文档](#官方文档)
    - [核心Processor文档](#核心processor文档)

---

## 1. 概述

**Processor**是Collector Pipeline中的数据处理组件，位于Receiver和Exporter之间。

**处理流程**：

```text
Receiver → Processor(s) → Exporter
```

**核心Processor类型**：

```text
✅ batch:           批处理
✅ memory_limiter:  内存限制
✅ attributes:      属性操作
✅ resource:        资源属性操作
✅ filter:          数据过滤
✅ transform:       数据转换
✅ tail_sampling:   尾部采样
```

---

## 2. Batch Processor

**用途**: 批量处理数据以提高性能和降低网络开销。

### 2.1 配置参数

```yaml
processors:
  batch:
    # 批次超时时间
    timeout: 10s
    
    # 每批最大Span数（针对traces）
    send_batch_size: 8192
    
    # 批次队列最大大小
    send_batch_max_size: 16384
```

### 2.2 参数说明

| 参数 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| `timeout` | duration | 200ms | 批次等待超时 |
| `send_batch_size` | int | 8192 | 达到此大小立即发送 |
| `send_batch_max_size` | int | 0 | 最大批次大小（0=无限制） |

### 2.3 使用示例

**高吞吐量配置**：

```yaml
processors:
  batch:
    timeout: 10s
    send_batch_size: 10000
    send_batch_max_size: 20000
```

**低延迟配置**：

```yaml
processors:
  batch:
    timeout: 100ms
    send_batch_size: 100
    send_batch_max_size: 500
```

### 2.4 最佳实践

```text
✅ 生产环境必须使用batch processor
✅ timeout设置为1-10s之间
✅ send_batch_size根据流量调整（8192-10000）
✅ 配合memory_limiter使用防止OOM
```

---

## 3. Memory Limiter Processor

**用途**: 防止Collector内存溢出。

### 3.1 配置示例

```yaml
processors:
  memory_limiter:
    # 检查间隔
    check_interval: 1s
    
    # 内存限制（软限制）
    limit_mib: 512
    
    # 内存峰值限制（硬限制）
    spike_limit_mib: 128
    
    # 达到限制时的行为
    # - percentage: 按百分比拒绝
    # - refuse_data: 拒绝所有新数据
    limit_percentage: 80
    spike_limit_percentage: 25
```

### 3.2 参数说明

| 参数 | 说明 |
|------|------|
| `limit_mib` | 软限制，达到后开始拒绝数据 |
| `spike_limit_mib` | 硬限制，超过后立即拒绝 |
| `check_interval` | 内存检查频率 |

### 3.3 配置计算

```text
总内存限制 = limit_mib + spike_limit_mib

示例：
  limit_mib: 512
  spike_limit_mib: 128
  总限制: 640 MiB
```

### 3.4 最佳实践

```yaml
# 推荐配置
processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 1024      # 容器内存的70%
    spike_limit_mib: 256  # 容器内存的20%
```

**部署建议**：

```text
✅ 必须放在pipeline第一位
✅ limit_mib设置为容器内存的60-70%
✅ spike_limit_mib设置为容器内存的20-30%
✅ K8s中设置memory limits略高于总限制
```

---

## 4. Attributes Processor

**用途**: 添加、修改、删除Span/Log/Metric的属性。

### 4.1 配置示例

```yaml
processors:
  attributes:
    actions:
      # 添加属性
      - key: environment
        value: production
        action: insert
      
      # 更新属性
      - key: http.url
        action: update
        value: "redacted"
      
      # 删除属性
      - key: http.user_agent
        action: delete
      
      # 从其他属性提取
      - key: region
        from_attribute: cloud.region
        action: extract
        pattern: ^([^-]+)
      
      # 哈希敏感信息
      - key: user.email
        action: hash
```

### 4.2 Action类型

| Action | 说明 | 示例 |
|--------|------|------|
| `insert` | 插入新属性（不存在时） | 添加environment标签 |
| `update` | 更新已存在属性 | 修改URL |
| `upsert` | 插入或更新 | 确保属性存在 |
| `delete` | 删除属性 | 删除敏感信息 |
| `extract` | 正则提取 | 从URL提取域名 |
| `hash` | SHA256哈希 | 哈希PII数据 |

### 4.3 高级配置

**条件属性操作**：

```yaml
processors:
  attributes:
    include:
      match_type: regexp
      services:
        - api-.*
    actions:
      - key: service.tier
        value: api
        action: insert
```

**多属性操作**：

```yaml
processors:
  attributes/production:
    actions:
      - key: environment
        value: production
        action: insert
      - key: team
        value: platform
        action: insert
      - key: http.url
        pattern: "(password|token)=([^&]+)"
        replacement: "$1=***"
        action: update
```

---

## 5. Resource Processor

**用途**: 操作Resource级别的属性（应用于所有遥测数据）。

### 5.1 配置示例

```yaml
processors:
  resource:
    attributes:
      # 添加资源属性
      - key: cloud.provider
        value: aws
        action: insert
      
      # 从环境变量获取
      - key: deployment.environment
        value: ${ENVIRONMENT}
        action: insert
      
      # 删除资源属性
      - key: host.name
        action: delete
```

### 5.2 与Attributes Processor对比

| 特性 | Resource Processor | Attributes Processor |
|------|-------------------|---------------------|
| 作用范围 | Resource级别 | Span/Log/Metric级别 |
| 性能 | 更高（只处理一次） | 较低（每条数据） |
| 适用场景 | 服务级元数据 | 数据级属性 |

---

## 6. Filter Processor

**用途**: 根据条件过滤遥测数据。

### 6.1 配置示例

```yaml
processors:
  # 过滤健康检查
  filter/healthcheck:
    traces:
      span:
        - 'attributes["http.url"] == "/health"'
        - 'attributes["http.url"] == "/ready"'
  
  # 过滤DEBUG日志
  filter/debug_logs:
    logs:
      - 'severity_number < SEVERITY_NUMBER_INFO'
  
  # 过滤特定Metric
  filter/internal_metrics:
    metrics:
      metric:
        - 'name == "internal.metric"'
```

### 6.2 过滤条件语法

**Span过滤**：

```yaml
processors:
  filter:
    traces:
      span:
        # 按属性过滤
        - 'attributes["http.method"] == "GET"'
        
        # 按Span name过滤
        - 'name == "health_check"'
        
        # 按Resource过滤
        - 'resource.attributes["service.name"] == "test-service"'
        
        # 复杂条件
        - 'attributes["http.status_code"] >= 500 and attributes["http.status_code"] < 600'
```

**Log过滤**：

```yaml
processors:
  filter:
    logs:
      # 按严重性过滤
      - 'severity_number < SEVERITY_NUMBER_WARN'
      
      # 按Body内容过滤
      - 'body matches "^DEBUG:"'
      
      # 按属性过滤
      - 'attributes["service.name"] == "test-service"'
```

### 6.3 实用过滤场景

**1. 过滤健康检查**：

```yaml
processors:
  filter/healthcheck:
    traces:
      span:
        - 'attributes["http.target"] == "/health"'
        - 'attributes["http.target"] == "/ready"'
        - 'attributes["http.target"] == "/live"'
```

**2. 只保留错误**：

```yaml
processors:
  filter/errors_only:
    traces:
      span:
        - 'status.code != STATUS_CODE_ERROR'
```

**3. 过滤低价值日志**：

```yaml
processors:
  filter/verbose_logs:
    logs:
      - 'severity_number <= SEVERITY_NUMBER_DEBUG'
      - 'body matches "^(Entering|Exiting)"'
```

---

## 7. Transform Processor

**用途**: 使用OTTL (OpenTelemetry Transformation Language) 进行复杂数据转换。

### 7.1 配置示例

```yaml
processors:
  transform:
    trace_statements:
      - context: span
        statements:
          # 重命名属性
          - set(attributes["http.method"], attributes["method"])
          - delete_key(attributes, "method")
          
          # 标准化状态码
          - set(attributes["http.status_code"], Int(attributes["http.status_code"]))
          
          # 添加计算属性
          - set(attributes["is_error"], attributes["http.status_code"] >= 400)
```

### 7.2 OTTL函数

**常用函数**：

```text
set():        设置值
delete_key(): 删除键
Int():        转换为整数
String():     转换为字符串
concat():     连接字符串
truncate():   截断字符串
replace():    替换字符串
```

### 7.3 高级转换

**从URL提取路径**：

```yaml
processors:
  transform:
    trace_statements:
      - context: span
        statements:
          - set(attributes["http.path"], ExtractPatterns(attributes["http.url"], "^https?://[^/]+(/[^?]*)"))
```

**生成唯一标识**：

```yaml
processors:
  transform:
    trace_statements:
      - context: span
        statements:
          - set(attributes["span.uid"], concat([resource.attributes["service.name"], ":", name]))
```

---

## 8. Tail Sampling Processor

**用途**: 基于完整Trace进行智能采样。

### 8.1 配置示例

```yaml
processors:
  tail_sampling:
    decision_wait: 10s
    num_traces: 100000
    expected_new_traces_per_sec: 10000
    policies:
      # 保留所有错误
      - name: errors
        type: status_code
        status_code:
          status_codes: [ERROR]
      
      # 保留慢请求
      - name: slow_requests
        type: latency
        latency:
          threshold_ms: 1000
      
      # 按比例采样正常请求
      - name: normal_requests
        type: probabilistic
        probabilistic:
          sampling_percentage: 10
```

### 8.2 策略类型

| 策略 | 说明 | 配置 |
|------|------|------|
| `always_sample` | 总是采样 | - |
| `status_code` | 按状态码 | status_codes: [ERROR] |
| `latency` | 按延迟 | threshold_ms: 1000 |
| `probabilistic` | 概率采样 | sampling_percentage: 10 |
| `rate_limiting` | 速率限制 | spans_per_second: 100 |
| `string_attribute` | 按字符串属性 | key, values |
| `numeric_attribute` | 按数值属性 | key, min, max |

### 8.3 完整策略配置

```yaml
processors:
  tail_sampling:
    decision_wait: 10s
    num_traces: 100000
    expected_new_traces_per_sec: 10000
    policies:
      # 1. 保留所有错误（最高优先级）
      - name: errors
        type: status_code
        status_code:
          status_codes: [ERROR]
      
      # 2. 保留慢请求
      - name: slow_requests
        type: latency
        latency:
          threshold_ms: 500
      
      # 3. 保留特定用户
      - name: premium_users
        type: string_attribute
        string_attribute:
          key: user.tier
          values: [premium, enterprise]
      
      # 4. 限速采样
      - name: rate_limit
        type: rate_limiting
        rate_limiting:
          spans_per_second: 1000
      
      # 5. 兜底概率采样
      - name: probabilistic
        type: probabilistic
        probabilistic:
          sampling_percentage: 5
```

---

## 9. Processor最佳实践

### 9.1 Pipeline顺序

**推荐顺序**：

```yaml
processors:
  # 1. 内存保护（必须第一）
  - memory_limiter
  
  # 2. 采样决策
  - tail_sampling
  
  # 3. 数据过滤
  - filter/healthcheck
  
  # 4. 数据转换
  - attributes
  - resource
  - transform
  
  # 5. 批处理（必须最后）
  - batch
```

### 9.2 性能优化

```yaml
# ✅ 好的配置
processors:
  memory_limiter:    # 第一位
    limit_mib: 1024
  filter:            # 早期过滤
    ...
  batch:             # 最后
    timeout: 10s

# ❌ 不好的配置
processors:
  batch:             # 不应该第一位
    ...
  memory_limiter:    # 太晚了
    ...
```

### 9.3 配置检查清单

```text
✅ memory_limiter在第一位
✅ batch在最后一位
✅ filter在transform之前（减少处理量）
✅ tail_sampling在early filter之后
✅ 敏感信息已hash或redact
✅ 测试过滤规则不会误删重要数据
✅ 监控processor处理延迟
```

---

## 10. 完整配置示例

### 10.1 生产环境配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  # 1. 内存保护
  memory_limiter:
    check_interval: 1s
    limit_mib: 1024
    spike_limit_mib: 256
  
  # 2. 过滤健康检查
  filter/healthcheck:
    traces:
      span:
        - 'attributes["http.target"] == "/health"'
        - 'attributes["http.target"] == "/ready"'
  
  # 3. 尾部采样
  tail_sampling:
    decision_wait: 10s
    num_traces: 100000
    expected_new_traces_per_sec: 10000
    policies:
      - name: errors
        type: status_code
        status_code:
          status_codes: [ERROR]
      - name: slow
        type: latency
        latency:
          threshold_ms: 1000
      - name: normal
        type: probabilistic
        probabilistic:
          sampling_percentage: 10
  
  # 4. 添加环境标签
  resource:
    attributes:
      - key: deployment.environment
        value: production
        action: insert
      - key: cloud.provider
        value: aws
        action: insert
  
  # 5. 属性处理
  attributes:
    actions:
      # 哈希敏感信息
      - key: user.email
        action: hash
      # 删除PII
      - key: user.phone
        action: delete
      # Redact密码
      - key: http.url
        pattern: "(password|token)=([^&]+)"
        replacement: "$1=***"
        action: update
  
  # 6. 批处理
  batch:
    timeout: 10s
    send_batch_size: 8192
    send_batch_max_size: 16384

exporters:
  otlp:
    endpoint: otel-collector:4317
    tls:
      insecure: false

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors:
        - memory_limiter
        - filter/healthcheck
        - tail_sampling
        - resource
        - attributes
        - batch
      exporters: [otlp]
```

### 10.2 开发环境配置

```yaml
processors:
  # 简化配置，无采样
  batch:
    timeout: 1s
    send_batch_size: 100

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp]
```

---

## 11. 参考资源

### 官方文档

- **Processor Overview**: <https://opentelemetry.io/docs/collector/configuration/#processors>
- **Processor Repository**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor>

### 核心Processor文档

- **Batch Processor**: <https://github.com/open-telemetry/opentelemetry-collector/tree/main/processor/batchprocessor>
- **Memory Limiter**: <https://github.com/open-telemetry/opentelemetry-collector/tree/main/processor/memorylimiterprocessor>
- **Attributes Processor**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor/attributesprocessor>
- **Filter Processor**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor/filterprocessor>
- **Transform Processor**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor/transformprocessor>
- **Tail Sampling**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor/tailsamplingprocessor>

---

**文档维护**: OTLP深度梳理项目组  
**最后更新**: 2025年10月8日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐
