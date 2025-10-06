# OTTL 示例与最佳实践

## 目录

- [OTTL 示例与最佳实践](#ottl-示例与最佳实践)
  - [目录](#目录)
  - [1. OTTL 简介](#1-ottl-简介)
    - [1.1 什么是 OTTL](#11-什么是-ottl)
    - [1.2 核心概念](#12-核心概念)
  - [2. 基础语法](#2-基础语法)
    - [2.1 数据路径访问](#21-数据路径访问)
    - [2.2 条件表达式](#22-条件表达式)
    - [2.3 函数调用](#23-函数调用)
  - [3. Traces 转换示例](#3-traces-转换示例)
    - [3.1 属性操作](#31-属性操作)
    - [3.2 数据脱敏](#32-数据脱敏)
    - [3.3 状态标记](#33-状态标记)
    - [3.4 时间处理](#34-时间处理)
  - [4. Metrics 转换示例](#4-metrics-转换示例)
    - [4.1 降维聚合](#41-降维聚合)
    - [4.2 单位转换](#42-单位转换)
    - [4.3 标签规范化](#43-标签规范化)
  - [5. Logs 转换示例](#5-logs-转换示例)
    - [5.1 日志脱敏](#51-日志脱敏)
    - [5.2 结构化提取](#52-结构化提取)
    - [5.3 严重级别映射](#53-严重级别映射)
  - [6. 高级用法](#6-高级用法)
    - [6.1 动态路由](#61-动态路由)
    - [6.2 数据富化](#62-数据富化)
    - [6.3 采样标记](#63-采样标记)
  - [7. 性能优化](#7-性能优化)
    - [7.1 规则顺序](#71-规则顺序)
    - [7.2 避免重复计算](#72-避免重复计算)
    - [7.3 错误处理](#73-错误处理)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 命名规范](#81-命名规范)
    - [8.2 安全考虑](#82-安全考虑)
    - [8.3 测试验证](#83-测试验证)
  - [9. 常见模式](#9-常见模式)
    - [9.1 PII 数据处理](#91-pii-数据处理)
    - [9.2 多租户隔离](#92-多租户隔离)
    - [9.3 成本优化](#93-成本优化)
  - [10. 生产环境实战案例](#10-生产环境实战案例)
    - [10.1 电商平台订单追踪](#101-电商平台订单追踪)
    - [10.2 金融系统合规处理](#102-金融系统合规处理)
    - [10.3 微服务调用链优化](#103-微服务调用链优化)
    - [10.4 Kubernetes 环境增强](#104-kubernetes-环境增强)
    - [10.5 实时告警触发](#105-实时告警触发)
    - [10.6 多云环境统一](#106-多云环境统一)
  - [11. Go Collector 集成示例](#11-go-collector-集成示例)
    - [11.1 在 Go 应用中使用 OTTL](#111-在-go-应用中使用-ottl)
  - [12. 参考资料](#12-参考资料)

## 1. OTTL 简介

### 1.1 什么是 OTTL

**OTTL**（OpenTelemetry Transformation Language）是 OpenTelemetry Collector 的声明式数据转换语言，用于在数据管道中对遥测数据进行灵活的转换、过滤和富化。

**核心优势**：

- **声明式**：描述"做什么"而非"怎么做"
- **类型安全**：编译时类型检查
- **高性能**：字节码优化，单核可达 300k span/s
- **可组合**：支持复杂的条件和函数链

### 1.2 核心概念

**上下文（Context）**：

- `resource.attributes` - 资源属性
- `attributes` - 信号级别属性
- `instrumentation_scope` - 插桩范围
- `span_id`, `trace_id` - 追踪标识符

**数据类型**：

- `String` - 字符串
- `Int` - 整数
- `Double` - 浮点数
- `Bool` - 布尔值
- `Bytes` - 字节数组
- `Map` - 键值对
- `Slice` - 数组

## 2. 基础语法

### 2.1 数据路径访问

```yaml
# 访问资源属性
resource.attributes["service.name"]

# 访问 Span 属性
attributes["http.method"]

# 访问嵌套属性
attributes["http.request.header.user-agent"]

# 访问 Span 字段
name
status.code
duration
start_time_unix_nano
```

### 2.2 条件表达式

```yaml
# 等于
where attributes["http.status_code"] == 200

# 不等于
where attributes["env"] != "test"

# 比较
where duration > Duration("1s")
where attributes["retry_count"] < 3

# 逻辑运算
where attributes["env"] == "prod" and attributes["tier"] == "critical"
where status.code == STATUS_CODE_ERROR or duration > Duration("5s")

# 正则匹配
where IsMatch(attributes["http.target"], "^/api/.*")

# 存在性检查
where attributes["user.id"] != nil
```

### 2.3 函数调用

```yaml
# 字符串函数
set(attributes["service"], Substring(resource.attributes["service.name"], 0, 10))
set(attributes["upper_method"], Uppercase(attributes["http.method"]))
set(attributes["lower_path"], Lowercase(attributes["http.target"]))

# 数学函数
set(attributes["duration_ms"], duration / 1000000)
set(attributes["rounded"], Round(attributes["value"], 2))

# 哈希函数
set(attributes["user_hash"], SHA256(attributes["user.id"]))
set(attributes["md5"], MD5(attributes["email"]))

# 时间函数
set(attributes["hour"], Hour(start_time_unix_nano))
set(attributes["day_of_week"], DayOfWeek(start_time_unix_nano))
```

## 3. Traces 转换示例

### 3.1 属性操作

**添加属性**：

```yaml
processors:
  transform:
    error_mode: ignore
    trace_statements:
      # 添加环境标签
      - set(attributes["env"], "production")
      
      # 添加区域信息
      - set(attributes["region"], resource.attributes["cloud.region"])
      
      # 添加计算属性
      - set(attributes["is_slow"], duration > Duration("1s"))
```

**删除属性**：

```yaml
processors:
  transform:
    trace_statements:
      # 删除敏感 HTTP 头
      - delete_key(attributes, "http.request.header.authorization")
      - delete_key(attributes, "http.request.header.cookie")
      - delete_key(attributes, "http.request.header.x-api-key")
      
      # 删除调试信息
      - delete_key(attributes, "debug.stack_trace") 
        where resource.attributes["env"] == "prod"
```

**修改属性**：

```yaml
processors:
  transform:
    trace_statements:
      # 规范化 HTTP 方法
      - set(attributes["http.method"], Uppercase(attributes["http.method"]))
      
      # 截断长字符串
      - set(attributes["http.target"], 
          Substring(attributes["http.target"], 0, 100))
        where Len(attributes["http.target"]) > 100
      
      # 替换值
      - replace_pattern(attributes["http.target"], "/user/\\d+", "/user/{id}")
```

### 3.2 数据脱敏

**PII 数据哈希**：

```yaml
processors:
  transform:
    trace_statements:
      # 用户 ID 哈希
      - set(attributes["user.id"], SHA256(attributes["user.id"])) 
        where resource.attributes["env"] == "prod"
      
      # 邮箱脱敏
      - set(attributes["user.email"], 
          Concat(Substring(attributes["user.email"], 0, 3), "***@***.com"))
        where attributes["user.email"] != nil
      
      # IP 地址脱敏（保留前两段）
      - replace_pattern(attributes["client.address"], 
          "(\\d+\\.\\d+)\\.\\d+\\.\\d+", "$1.*.*)
```

**敏感字段移除**：

```yaml
processors:
  transform:
    trace_statements:
      # 移除所有包含 "password" 的属性
      - delete_matching_keys(attributes, ".*password.*")
      
      # 移除所有包含 "secret" 的属性
      - delete_matching_keys(attributes, ".*secret.*")
      
      # 移除所有包含 "token" 的属性
      - delete_matching_keys(attributes, ".*token.*")
```

### 3.3 状态标记

**错误标记**：

```yaml
processors:
  transform:
    trace_statements:
      # 超时标记
      - set(status.code, STATUS_CODE_ERROR)
        where duration > Duration("30s")
      - set(status.message, "Request timeout exceeded")
        where duration > Duration("30s")
      
      # HTTP 错误状态
      - set(status.code, STATUS_CODE_ERROR)
        where attributes["http.status_code"] >= 500
      - set(status.message, "Server error")
        where attributes["http.status_code"] >= 500
      
      # 数据库错误
      - set(status.code, STATUS_CODE_ERROR)
        where attributes["db.operation"] == "query" and 
              attributes["db.error"] != nil
```

**业务标记**：

```yaml
processors:
  transform:
    trace_statements:
      # 标记慢查询
      - set(attributes["is_slow_query"], true)
        where attributes["db.operation"] != nil and 
              duration > Duration("1s")
      
      # 标记重试请求
      - set(attributes["is_retry"], true)
        where attributes["http.retry_count"] > 0
      
      # 标记关键路径
      - set(attributes["is_critical"], true)
        where IsMatch(attributes["http.target"], "^/api/(payment|order)")
```

### 3.4 时间处理

**时间转换**：

```yaml
processors:
  transform:
    trace_statements:
      # 添加时间戳（毫秒）
      - set(attributes["timestamp_ms"], start_time_unix_nano / 1000000)
      
      # 添加小时标签（用于分区）
      - set(attributes["hour"], Hour(start_time_unix_nano))
      
      # 添加日期标签
      - set(attributes["date"], Format(start_time_unix_nano, "2006-01-02"))
      
      # 计算持续时间（毫秒）
      - set(attributes["duration_ms"], duration / 1000000)
```

## 4. Metrics 转换示例

### 4.1 降维聚合

**保留关键标签**：

```yaml
processors:
  transform:
    metric_statements:
      # 仅保留核心维度（降低基数）
      - keep_keys(attributes, ["cluster", "namespace", "pod"])
      
      # 移除高基数标签
      - delete_key(attributes, "instance_id")
      - delete_key(attributes, "request_id")
      - delete_key(attributes, "trace_id")
```

**标签聚合**：

```yaml
processors:
  transform:
    metric_statements:
      # 将 pod 名称聚合到 deployment
      - replace_pattern(attributes["pod"], 
          "^([a-z-]+)-[a-z0-9]+-[a-z0-9]+$", "$1")
        where IsMatch(attributes["pod"], "^[a-z-]+-[a-z0-9]+-[a-z0-9]+$")
      
      # 将 HTTP 路径聚合到路由模式
      - replace_pattern(attributes["http.target"], 
          "/user/\\d+", "/user/{id}")
      - replace_pattern(attributes["http.target"], 
          "/order/[a-f0-9-]+", "/order/{uuid}")
```

### 4.2 单位转换

**时间单位**：

```yaml
processors:
  transform:
    metric_statements:
      # 纳秒转毫秒
      - set(value, value / 1000000)
        where name == "http.server.duration" and unit == "ns"
      - set(unit, "ms")
        where name == "http.server.duration" and unit == "ns"
      
      # 秒转毫秒
      - set(value, value * 1000)
        where name == "http.client.duration" and unit == "s"
      - set(unit, "ms")
        where name == "http.client.duration" and unit == "s"
```

**存储单位**：

```yaml
processors:
  transform:
    metric_statements:
      # 字节转 MB
      - set(value, value / 1048576)
        where name == "process.memory.usage" and unit == "By"
      - set(unit, "MiBy")
        where name == "process.memory.usage" and unit == "By"
      
      # KB 转 MB
      - set(value, value / 1024)
        where name == "disk.usage" and unit == "KiBy"
      - set(unit, "MiBy")
        where name == "disk.usage" and unit == "KiBy"
```

### 4.3 标签规范化

**命名规范化**：

```yaml
processors:
  transform:
    metric_statements:
      # 统一服务名称格式
      - set(resource.attributes["service.name"], 
          Lowercase(resource.attributes["service.name"]))
      
      # 规范化环境标签
      - set(attributes["env"], "production")
        where attributes["environment"] == "prod"
      - set(attributes["env"], "staging")
        where attributes["environment"] == "stage"
      - delete_key(attributes, "environment")
```

## 5. Logs 转换示例

### 5.1 日志脱敏

**敏感信息脱敏**：

```yaml
processors:
  transform:
    log_statements:
      # 邮箱脱敏
      - replace_pattern(body, 
          "[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}", 
          "***@***.***")
      
      # 手机号脱敏
      - replace_pattern(body, 
          "\\d{3}-\\d{4}-\\d{4}", 
          "***-****-****")
      
      # 信用卡号脱敏
      - replace_pattern(body, 
          "\\d{4}-\\d{4}-\\d{4}-\\d{4}", 
          "****-****-****-****")
      
      # IP 地址脱敏
      - replace_pattern(body, 
          "\\d{1,3}\\.\\d{1,3}\\.\\d{1,3}\\.\\d{1,3}", 
          "***.***.***.***")
```

### 5.2 结构化提取

**从日志体提取字段**：

```yaml
processors:
  transform:
    log_statements:
      # 提取 HTTP 状态码
      - set(attributes["http.status_code"], 
          ExtractPattern(body, "status=(\\d+)"))
        where IsMatch(body, "status=\\d+")
      
      # 提取用户 ID
      - set(attributes["user.id"], 
          ExtractPattern(body, "user_id=([a-zA-Z0-9]+)"))
        where IsMatch(body, "user_id=")
      
      # 提取持续时间
      - set(attributes["duration_ms"], 
          Int(ExtractPattern(body, "duration=(\\d+)ms")))
        where IsMatch(body, "duration=\\d+ms")
```

### 5.3 严重级别映射

**日志级别规范化**：

```yaml
processors:
  transform:
    log_statements:
      # 映射自定义级别到标准级别
      - set(severity_number, SEVERITY_NUMBER_ERROR)
        where severity_text == "CRITICAL" or severity_text == "FATAL"
      
      - set(severity_number, SEVERITY_NUMBER_WARN)
        where severity_text == "WARNING"
      
      - set(severity_number, SEVERITY_NUMBER_INFO)
        where severity_text == "NOTICE"
      
      # 根据内容推断级别
      - set(severity_number, SEVERITY_NUMBER_ERROR)
        where IsMatch(body, "(?i)(error|exception|failed)")
      
      - set(severity_number, SEVERITY_NUMBER_WARN)
        where IsMatch(body, "(?i)(warn|deprecated)")
```

## 6. 高级用法

### 6.1 动态路由

**基于租户路由**：

```yaml
processors:
  transform:
    trace_statements:
      # 为不同租户添加路由标签
      - set(attributes["route.target"], "tenant-a-backend")
        where resource.attributes["tenant"] == "tenant-a"
      
      - set(attributes["route.target"], "tenant-b-backend")
        where resource.attributes["tenant"] == "tenant-b"
      
      # 默认路由
      - set(attributes["route.target"], "default-backend")
        where attributes["route.target"] == nil

# 配合 routing processor 使用
  routing:
    from_attribute: route.target
    table:
      - value: tenant-a-backend
        exporters: [otlp/tenant-a]
      - value: tenant-b-backend
        exporters: [otlp/tenant-b]
    default_exporters: [otlp/default]
```

### 6.2 数据富化

**添加上下文信息**：

```yaml
processors:
  transform:
    trace_statements:
      # 添加区域信息
      - set(attributes["region"], "us-west")
        where resource.attributes["cloud.availability_zone"] == "us-west-1a"
      
      # 添加租户信息
      - set(attributes["tenant"], "premium")
        where resource.attributes["service.name"] == "premium-api"
      
      # 添加成本中心
      - set(attributes["cost_center"], "engineering")
        where resource.attributes["team"] == "platform"
      
      # 添加 SLA 等级
      - set(attributes["sla_tier"], "gold")
        where attributes["customer_tier"] == "enterprise"
```

### 6.3 采样标记

**为 Tail Sampling 添加标记**：

```yaml
processors:
  transform:
    trace_statements:
      # 标记错误（高优先级采样）
      - set(attributes["sampling.priority"], "high")
        where status.code == STATUS_CODE_ERROR
      
      # 标记慢请求（高优先级采样）
      - set(attributes["sampling.priority"], "high")
        where duration > Duration("5s")
      
      # 标记关键业务（中优先级采样）
      - set(attributes["sampling.priority"], "medium")
        where IsMatch(attributes["http.target"], "^/api/(payment|checkout)")
      
      # 其他请求（低优先级采样）
      - set(attributes["sampling.priority"], "low")
        where attributes["sampling.priority"] == nil

# 配合 tail_sampling processor
  tail_sampling:
    policies:
      - name: high_priority
        type: string_attribute
        string_attribute:
          key: sampling.priority
          values: ["high"]
      - name: medium_priority
        type: string_attribute
        string_attribute:
          key: sampling.priority
          values: ["medium"]
        probabilistic:
          sampling_percentage: 50
      - name: low_priority
        type: probabilistic
        probabilistic:
          sampling_percentage: 10
```

## 7. 性能优化

### 7.1 规则顺序

**优化执行顺序**：

```yaml
processors:
  transform:
    trace_statements:
      # 1. 先执行过滤（减少后续处理量）
      - drop()
        where attributes["http.target"] == "/health"
      
      # 2. 再执行简单操作
      - set(attributes["env"], "prod")
      
      # 3. 最后执行复杂操作
      - set(attributes["user_hash"], SHA256(attributes["user.id"]))
        where attributes["user.id"] != nil
```

### 7.2 避免重复计算

**缓存计算结果**：

```yaml
processors:
  transform:
    trace_statements:
      # 不好的做法（重复计算）
      # - set(attributes["is_slow"], duration > Duration("1s"))
      # - set(attributes["is_very_slow"], duration > Duration("5s"))
      
      # 好的做法（计算一次）
      - set(attributes["duration_ms"], duration / 1000000)
      - set(attributes["is_slow"], attributes["duration_ms"] > 1000)
      - set(attributes["is_very_slow"], attributes["duration_ms"] > 5000)
```

### 7.3 错误处理

**错误模式配置**：

```yaml
processors:
  transform:
    # ignore: 忽略错误，继续处理（推荐生产环境）
    error_mode: ignore
    
    # propagate: 传播错误，停止处理
    # error_mode: propagate
    
    trace_statements:
      # 使用条件避免错误
      - set(attributes["user_hash"], SHA256(attributes["user.id"]))
        where attributes["user.id"] != nil
      
      # 使用默认值
      - set(attributes["status_code"], 
          Coalesce(attributes["http.status_code"], 0))
```

## 8. 最佳实践

### 8.1 命名规范

**属性命名**：

```yaml
processors:
  transform:
    trace_statements:
      # 使用语义约定命名
      - set(attributes["http.request.method"], attributes["method"])
      - delete_key(attributes, "method")
      
      # 使用点分隔的层次结构
      - set(attributes["app.feature.name"], "checkout")
      - set(attributes["app.feature.version"], "v2")
      
      # 避免使用特殊字符
      - replace_pattern(attributes["custom.field"], "[^a-zA-Z0-9._-]", "_")
```

### 8.2 安全考虑

**敏感数据处理**：

```yaml
processors:
  transform:
    trace_statements:
      # 生产环境强制脱敏
      - set(attributes["user.id"], SHA256(attributes["user.id"]))
        where resource.attributes["env"] == "prod" and 
              attributes["user.id"] != nil
      
      # 删除所有敏感字段
      - delete_matching_keys(attributes, ".*password.*")
      - delete_matching_keys(attributes, ".*secret.*")
      - delete_matching_keys(attributes, ".*token.*")
      - delete_matching_keys(attributes, ".*key.*")
      
      # 审计日志
      - set(attributes["pii.processed"], true)
        where attributes["user.id"] != nil
```

### 8.3 测试验证

**配置验证**：

```bash
# 使用 otelcol 验证配置
otelcol validate --config config.yaml

# 使用 dry-run 模式测试
otelcol --config config.yaml --dry-run
```

**单元测试**：

```yaml
# 测试配置示例
test_cases:
  - name: "脱敏用户 ID"
    input:
      attributes:
        user.id: "12345"
      resource:
        attributes:
          env: "prod"
    expected:
      attributes:
        user.id: "5994471abb01112afcc18159f6cc74b4f511b99806da59b3caf5a9c173cacfc5"
```

## 9. 常见模式

### 9.1 PII 数据处理

**完整的 PII 处理流程**：

```yaml
processors:
  transform:
    error_mode: ignore
    trace_statements:
      # 1. 识别 PII 字段
      - set(attributes["_pii_fields"], [])
      - append(attributes["_pii_fields"], "user.id")
        where attributes["user.id"] != nil
      - append(attributes["_pii_fields"], "user.email")
        where attributes["user.email"] != nil
      
      # 2. 生产环境脱敏
      - set(attributes["user.id"], SHA256(attributes["user.id"]))
        where resource.attributes["env"] == "prod" and 
              attributes["user.id"] != nil
      - set(attributes["user.email"], 
          Concat(Substring(attributes["user.email"], 0, 3), "***@***.com"))
        where resource.attributes["env"] == "prod" and 
              attributes["user.email"] != nil
      
      # 3. 添加审计标记
      - set(attributes["pii.processed"], true)
        where Len(attributes["_pii_fields"]) > 0
      - set(attributes["pii.fields_count"], Len(attributes["_pii_fields"]))
      
      # 4. 清理临时字段
      - delete_key(attributes, "_pii_fields")
```

### 9.2 多租户隔离

**租户路由和隔离**：

```yaml
processors:
  transform:
    trace_statements:
      # 1. 提取租户信息
      - set(attributes["tenant.id"], 
          ExtractPattern(attributes["http.target"], "^/tenant/([^/]+)"))
        where IsMatch(attributes["http.target"], "^/tenant/")
      
      # 2. 验证租户
      - set(attributes["tenant.valid"], true)
        where attributes["tenant.id"] != nil and 
              Len(attributes["tenant.id"]) > 0
      
      # 3. 添加租户元数据
      - set(attributes["tenant.tier"], "premium")
        where attributes["tenant.id"] == "tenant-a"
      - set(attributes["tenant.tier"], "standard")
        where attributes["tenant.id"] == "tenant-b"
      
      # 4. 设置路由目标
      - set(attributes["route.target"], 
          Concat("tenant-", attributes["tenant.id"], "-backend"))
        where attributes["tenant.valid"] == true
      
      # 5. 无效租户处理
      - set(status.code, STATUS_CODE_ERROR)
        where attributes["tenant.valid"] != true
      - set(status.message, "Invalid tenant")
        where attributes["tenant.valid"] != true
```

### 9.3 成本优化

**数据量控制**：

```yaml
processors:
  transform:
    trace_statements:
      # 1. 丢弃健康检查
      - drop()
        where attributes["http.target"] == "/health" or 
              attributes["http.target"] == "/ready"
      
      # 2. 丢弃静态资源
      - drop()
        where IsMatch(attributes["http.target"], "\\.(js|css|png|jpg|ico)$")
      
      # 3. 采样非关键路径
      - set(attributes["sampling.drop"], true)
        where attributes["http.target"] != nil and 
              not IsMatch(attributes["http.target"], "^/api/") and 
              Hash(trace_id) % 100 > 10  # 保留 10%
      
      # 4. 降维高基数字段
      - replace_pattern(attributes["http.target"], 
          "/user/\\d+", "/user/{id}")
      - replace_pattern(attributes["http.target"], 
          "/order/[a-f0-9-]+", "/order/{uuid}")
      
      # 5. 删除大字段
      - delete_key(attributes, "http.request.body")
        where Len(attributes["http.request.body"]) > 1024
      - delete_key(attributes, "http.response.body")
        where Len(attributes["http.response.body"]) > 1024
```

## 10. 生产环境实战案例

### 10.1 电商平台订单追踪

**场景**：电商平台需要追踪订单流程，同时保护用户隐私和控制成本。

```yaml
processors:
  transform:
    error_mode: ignore
    trace_statements:
      # 1. 订单状态标准化
      - set(attributes["order.status"], "pending")
        where attributes["order_status"] == "0"
      - set(attributes["order.status"], "confirmed")
        where attributes["order_status"] == "1"
      - set(attributes["order.status"], "shipped")
        where attributes["order_status"] == "2"
      - set(attributes["order.status"], "delivered")
        where attributes["order_status"] == "3"
      - delete_key(attributes, "order_status")
      
      # 2. 用户信息脱敏
      - set(attributes["user.id"], SHA256(attributes["user.id"]))
        where resource.attributes["env"] == "prod"
      - set(attributes["user.phone"], 
          Concat(Substring(attributes["user.phone"], 0, 3), "****", 
                 Substring(attributes["user.phone"], 7, 4)))
        where attributes["user.phone"] != nil
      
      # 3. 金额格式化（分转元）
      - set(attributes["order.amount"], attributes["order.amount_cents"] / 100.0)
      - delete_key(attributes, "order.amount_cents")
      
      # 4. 地址脱敏（仅保留城市）
      - set(attributes["shipping.city"], 
          ExtractPattern(attributes["shipping.address"], "^([^省]+省)?([^市]+市)"))
      - delete_key(attributes, "shipping.address")
      
      # 5. 标记高价值订单
      - set(attributes["order.high_value"], true)
        where attributes["order.amount"] > 1000
      - set(attributes["sampling.priority"], "high")
        where attributes["order.high_value"] == true
      
      # 6. 支付方式标准化
      - set(attributes["payment.method"], "alipay")
        where IsMatch(attributes["payment_channel"], "(?i)alipay|支付宝")
      - set(attributes["payment.method"], "wechat")
        where IsMatch(attributes["payment_channel"], "(?i)wechat|微信")
      - set(attributes["payment.method"], "card")
        where IsMatch(attributes["payment_channel"], "(?i)card|银行卡")
      - delete_key(attributes, "payment_channel")
```

### 10.2 金融系统合规处理

**场景**：金融系统需要满足 GDPR/PCI-DSS 合规要求。

```yaml
processors:
  transform:
    error_mode: propagate  # 金融系统不容忍错误
    trace_statements:
      # 1. 强制脱敏所有 PII 数据
      - delete_matching_keys(attributes, ".*card.*number.*")
      - delete_matching_keys(attributes, ".*cvv.*")
      - delete_matching_keys(attributes, ".*password.*")
      - delete_matching_keys(attributes, ".*ssn.*")
      - delete_matching_keys(attributes, ".*id_card.*")
      
      # 2. 账户信息哈希
      - set(attributes["account.id"], SHA256(attributes["account.id"]))
        where attributes["account.id"] != nil
      - set(attributes["transaction.id"], SHA256(attributes["transaction.id"]))
        where attributes["transaction.id"] != nil
      
      # 3. 金额脱敏（仅保留范围）
      - set(attributes["amount.range"], "0-100")
        where attributes["amount"] <= 100
      - set(attributes["amount.range"], "100-1000")
        where attributes["amount"] > 100 and attributes["amount"] <= 1000
      - set(attributes["amount.range"], "1000-10000")
        where attributes["amount"] > 1000 and attributes["amount"] <= 10000
      - set(attributes["amount.range"], "10000+")
        where attributes["amount"] > 10000
      - delete_key(attributes, "amount")
      
      # 4. IP 地址脱敏
      - replace_pattern(attributes["client.ip"], 
          "(\\d+\\.\\d+)\\.\\d+\\.\\d+", "$1.0.0")
      
      # 5. 审计日志标记
      - set(attributes["audit.logged"], true)
      - set(attributes["audit.timestamp"], UnixNano(Now()))
      - set(attributes["audit.compliance"], "GDPR,PCI-DSS")
      
      # 6. 异常交易标记
      - set(attributes["transaction.suspicious"], true)
        where attributes["amount"] > 50000 or 
              attributes["transaction.country"] != attributes["account.country"]
      
      # 7. 保留时间标记（合规要求）
      - set(attributes["retention.days"], 2555)  # 7 年
        where attributes["transaction.type"] == "deposit" or 
              attributes["transaction.type"] == "withdrawal"
```

### 10.3 微服务调用链优化

**场景**：大规模微服务架构，需要优化追踪数据量和查询性能。

```yaml
processors:
  transform:
    trace_statements:
      # 1. 服务名称标准化
      - set(resource.attributes["service.name"], 
          Lowercase(resource.attributes["service.name"]))
      - replace_pattern(resource.attributes["service.name"], 
          "-[a-f0-9]{8}$", "")  # 移除 Pod hash
      
      # 2. 路径参数化（降低基数）
      - replace_pattern(attributes["http.target"], 
          "/api/v\\d+/users/\\d+", "/api/v{version}/users/{id}")
      - replace_pattern(attributes["http.target"], 
          "/api/v\\d+/orders/[a-f0-9-]{36}", "/api/v{version}/orders/{uuid}")
      - replace_pattern(attributes["http.target"], 
          "/api/v\\d+/products/[a-zA-Z0-9]+", "/api/v{version}/products/{sku}")
      
      # 3. gRPC 方法标准化
      - set(attributes["rpc.method"], 
          ExtractPattern(attributes["rpc.service"], "\\.(\\w+)$"))
        where attributes["rpc.service"] != nil
      
      # 4. 数据库查询优化
      - replace_pattern(attributes["db.statement"], 
          "IN \\([^)]+\\)", "IN (...)")  # 简化 IN 子句
      - replace_pattern(attributes["db.statement"], 
          "'[^']*'", "'?'")  # 参数化字符串
      - set(attributes["db.statement"], 
          Substring(attributes["db.statement"], 0, 200))
        where Len(attributes["db.statement"]) > 200
      
      # 5. 错误分类
      - set(attributes["error.category"], "client_error")
        where attributes["http.status_code"] >= 400 and 
              attributes["http.status_code"] < 500
      - set(attributes["error.category"], "server_error")
        where attributes["http.status_code"] >= 500
      - set(attributes["error.category"], "timeout")
        where duration > Duration("30s")
      - set(attributes["error.category"], "circuit_breaker")
        where IsMatch(attributes["error.message"], "(?i)circuit.*open")
      
      # 6. 性能分级
      - set(attributes["performance.grade"], "excellent")
        where duration < Duration("100ms")
      - set(attributes["performance.grade"], "good")
        where duration >= Duration("100ms") and duration < Duration("500ms")
      - set(attributes["performance.grade"], "acceptable")
        where duration >= Duration("500ms") and duration < Duration("1s")
      - set(attributes["performance.grade"], "poor")
        where duration >= Duration("1s") and duration < Duration("3s")
      - set(attributes["performance.grade"], "critical")
        where duration >= Duration("3s")
      
      # 7. 采样决策优化
      - set(attributes["sampling.priority"], "critical")
        where status.code == STATUS_CODE_ERROR or 
              attributes["performance.grade"] == "critical"
      - set(attributes["sampling.priority"], "high")
        where attributes["performance.grade"] == "poor" or 
              attributes["order.high_value"] == true
      - set(attributes["sampling.priority"], "normal")
        where attributes["sampling.priority"] == nil
```

### 10.4 Kubernetes 环境增强

**场景**：Kubernetes 集群中自动添加环境信息和优化标签。

```yaml
processors:
  transform:
    trace_statements:
      # 1. 从 Pod 名称提取信息
      - set(resource.attributes["k8s.deployment.name"], 
          ExtractPattern(resource.attributes["k8s.pod.name"], 
                        "^([a-z0-9-]+)-[a-z0-9]+-[a-z0-9]+$"))
      
      # 2. 环境判断
      - set(resource.attributes["deployment.environment"], "production")
        where IsMatch(resource.attributes["k8s.namespace.name"], "prod")
      - set(resource.attributes["deployment.environment"], "staging")
        where IsMatch(resource.attributes["k8s.namespace.name"], "stag")
      - set(resource.attributes["deployment.environment"], "development")
        where IsMatch(resource.attributes["k8s.namespace.name"], "dev")
      
      # 3. 区域信息提取
      - set(resource.attributes["cloud.region"], 
          ExtractPattern(resource.attributes["k8s.node.name"], 
                        "^[a-z]+-([a-z]+-\\d+)"))
      
      # 4. 添加集群标识
      - set(resource.attributes["k8s.cluster.id"], 
          Concat(resource.attributes["cloud.provider"], "-", 
                 resource.attributes["cloud.region"], "-", 
                 resource.attributes["k8s.cluster.name"]))
      
      # 5. 容器资源限制标记
      - set(attributes["container.limited"], true)
        where resource.attributes["container.memory.limit"] != nil
      
      # 6. 节点类型标记
      - set(resource.attributes["k8s.node.type"], "spot")
        where IsMatch(resource.attributes["k8s.node.name"], "spot")
      - set(resource.attributes["k8s.node.type"], "on-demand")
        where resource.attributes["k8s.node.type"] == nil
```

### 10.5 实时告警触发

**场景**：基于 OTTL 规则实时标记需要告警的事件。

```yaml
processors:
  transform:
    trace_statements:
      # 1. SLA 违规检测
      - set(attributes["alert.sla_violation"], true)
        where attributes["http.route"] == "/api/critical" and 
              duration > Duration("1s")
      - set(attributes["alert.severity"], "critical")
        where attributes["alert.sla_violation"] == true
      
      # 2. 错误率异常
      - set(attributes["alert.high_error_rate"], true)
        where status.code == STATUS_CODE_ERROR and 
              resource.attributes["service.name"] == "payment-service"
      - set(attributes["alert.severity"], "high")
        where attributes["alert.high_error_rate"] == true
      
      # 3. 资源耗尽预警
      - set(attributes["alert.memory_pressure"], true)
        where attributes["process.memory.usage"] > 
              attributes["process.memory.limit"] * 0.9
      - set(attributes["alert.severity"], "warning")
        where attributes["alert.memory_pressure"] == true
      
      # 4. 异常流量检测
      - set(attributes["alert.traffic_spike"], true)
        where attributes["http.requests_per_second"] > 10000
      
      # 5. 数据库慢查询
      - set(attributes["alert.slow_query"], true)
        where attributes["db.operation"] != nil and 
              duration > Duration("5s")
      - set(attributes["alert.severity"], "warning")
        where attributes["alert.slow_query"] == true
      
      # 6. 第三方服务超时
      - set(attributes["alert.external_timeout"], true)
        where IsMatch(attributes["http.url"], "https?://external\\.") and 
              duration > Duration("10s")
      
      # 7. 告警去重标记
      - set(attributes["alert.fingerprint"], 
          SHA256(Concat(
            resource.attributes["service.name"], 
            attributes["alert.severity"],
            attributes["http.route"]
          )))
        where attributes["alert.severity"] != nil
```

### 10.6 多云环境统一

**场景**：统一 AWS、GCP、Azure 等多云环境的标签格式。

```yaml
processors:
  transform:
    trace_statements:
      # 1. 云提供商标准化
      - set(resource.attributes["cloud.provider"], "aws")
        where resource.attributes["cloud.platform"] == "aws_ec2" or 
              resource.attributes["cloud.platform"] == "aws_ecs"
      - set(resource.attributes["cloud.provider"], "gcp")
        where resource.attributes["cloud.platform"] == "gcp_compute_engine" or 
              resource.attributes["cloud.platform"] == "gcp_kubernetes_engine"
      - set(resource.attributes["cloud.provider"], "azure")
        where resource.attributes["cloud.platform"] == "azure_vm" or 
              resource.attributes["cloud.platform"] == "azure_aks"
      
      # 2. 区域名称标准化
      - replace_pattern(resource.attributes["cloud.region"], 
          "^us-east-", "us-east-")  # AWS
      - replace_pattern(resource.attributes["cloud.region"], 
          "^us-central", "us-central")  # GCP
      - replace_pattern(resource.attributes["cloud.region"], 
          "^eastus", "us-east")  # Azure
      
      # 3. 实例类型映射
      - set(resource.attributes["host.type"], "compute")
        where IsMatch(resource.attributes["host.instance.type"], 
                     "^(t3|e2|Standard_B)")
      - set(resource.attributes["host.type"], "memory")
        where IsMatch(resource.attributes["host.instance.type"], 
                     "^(r5|n2-highmem|Standard_E)")
      - set(resource.attributes["host.type"], "compute-optimized")
        where IsMatch(resource.attributes["host.instance.type"], 
                     "^(c5|c2|Standard_F)")
      
      # 4. 成本标签
      - set(resource.attributes["cost.center"], 
          resource.attributes["cloud.account.id"])
      - set(resource.attributes["cost.project"], 
          resource.attributes["service.name"])
```

## 11. Go Collector 集成示例

### 11.1 在 Go 应用中使用 OTTL

虽然 OTTL 主要在 Collector 中使用，但可以在 Go 应用中预处理数据：

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/trace"
)

// 自定义 SpanProcessor 实现 OTTL 类似的转换
type OTTLProcessor struct {
    next trace.SpanProcessor
}

func NewOTTLProcessor(next trace.SpanProcessor) *OTTLProcessor {
    return &OTTLProcessor{next: next}
}

func (p *OTTLProcessor) OnStart(ctx context.Context, s trace.ReadWriteSpan) {
    // 应用转换规则
    p.transformSpan(s)
    p.next.OnStart(ctx, s)
}

func (p *OTTLProcessor) OnEnd(s trace.ReadOnlySpan) {
    p.next.OnEnd(s)
}

func (p *OTTLProcessor) Shutdown(ctx context.Context) error {
    return p.next.Shutdown(ctx)
}

func (p *OTTLProcessor) ForceFlush(ctx context.Context) error {
    return p.next.ForceFlush(ctx)
}

func (p *OTTLProcessor) transformSpan(s trace.ReadWriteSpan) {
    attrs := s.Attributes()
    newAttrs := make([]attribute.KeyValue, 0, len(attrs))
    
    for _, attr := range attrs {
        // 规则 1: 脱敏用户 ID
        if attr.Key == "user.id" {
            hash := sha256Hash(attr.Value.AsString())
            newAttrs = append(newAttrs, attribute.String("user.id", hash))
            continue
        }
        
        // 规则 2: 删除敏感字段
        if strings.Contains(string(attr.Key), "password") ||
           strings.Contains(string(attr.Key), "token") {
            continue
        }
        
        // 规则 3: 路径参数化
        if attr.Key == "http.target" {
            path := parameterizePath(attr.Value.AsString())
            newAttrs = append(newAttrs, attribute.String("http.target", path))
            continue
        }
        
        newAttrs = append(newAttrs, attr)
    }
    
    // 设置新属性
    s.SetAttributes(newAttrs...)
}

func parameterizePath(path string) string {
    // /user/123 -> /user/{id}
    re := regexp.MustCompile(`/user/\d+`)
    path = re.ReplaceAllString(path, "/user/{id}")
    
    // /order/uuid -> /order/{uuid}
    re = regexp.MustCompile(`/order/[a-f0-9-]{36}`)
    path = re.ReplaceAllString(path, "/order/{uuid}")
    
    return path
}

func sha256Hash(s string) string {
    h := sha256.New()
    h.Write([]byte(s))
    return hex.EncodeToString(h.Sum(nil))
}
```

## 12. 参考资料

- **OTTL 官方文档**：[OpenTelemetry Transformation Language](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/pkg/ottl)
- **函数参考**：[OTTL Functions](https://github.com/open-telemetry/opentelemetry-collector-contrib/blob/main/pkg/ottl/ottlfuncs/README.md)
- **Transform Processor**：[Transform Processor Documentation](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor/transformprocessor)
- **语义约定**：`docs/otlp/semantic-model.md`
- **Collector 配置**：`docs/design/technical-model.md`
- **性能优化**：`docs/analysis/golang-1.25.1-otlp-integration/2025-updates/07-performance-optimization.md`
