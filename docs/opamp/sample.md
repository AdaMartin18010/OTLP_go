# OPAMP 样例配置与流程

## 目录

- [OPAMP 样例配置与流程](#opamp-样例配置与流程)
  - [目录](#目录)
  - [1. Agent 能力声明](#1-agent-能力声明)
  - [2. 远程配置下发](#2-远程配置下发)
    - [2.1 基础配置示例](#21-基础配置示例)
    - [2.2 完整配置结构](#22-完整配置结构)
    - [2.3 配置应用流程](#23-配置应用流程)
  - [3. 证书轮转流程](#3-证书轮转流程)
  - [4. 插件/二进制升级流程](#4-插件二进制升级流程)
    - [4.1 WASM 插件分发](#41-wasm-插件分发)
    - [4.2 Agent 二进制升级](#42-agent-二进制升级)
  - [5. 健康监控与自愈](#5-健康监控与自愈)
    - [5.1 健康状态上报](#51-健康状态上报)
    - [5.2 自动回滚配置](#52-自动回滚配置)
  - [6. 灰度发布示例](#6-灰度发布示例)
  - [7. 完整部署示例](#7-完整部署示例)
    - [7.1 Server 端配置](#71-server-端配置)
    - [7.2 Agent 端配置](#72-agent-端配置)
  - [8. 最佳实践](#8-最佳实践)
  - [9. 完整端到端示例](#9-完整端到端示例)
    - [9.1 Server 端完整实现](#91-server-端完整实现)
    - [9.2 Agent 端完整实现](#92-agent-端完整实现)
    - [9.3 测试脚本](#93-测试脚本)

## 1. Agent 能力声明

Agent 启动时向 Server 声明自身支持的能力：

```yaml
# Agent 能力声明（完整版）
agent_description:
  identifying_attributes:
    - key: service.name
      value: otel-collector-edge
    - key: service.instance.id
      value: collector-001
    - key: deployment.environment
      value: production
    - key: k8s.cluster.name
      value: prod-us-west-1
    - key: k8s.namespace.name
      value: observability
    - key: k8s.pod.name
      value: otel-collector-edge-7d9f8b-x7k2m
  
  # 非识别属性（用于分组和路由）
  non_identifying_attributes:
    - key: region
      value: us-west
    - key: zone
      value: us-west-1a
    - key: tenant
      value: team-platform
  
  # 支持的能力
  capabilities:
    reports_effective_config: true      # 上报生效配置
    accepts_remote_config: true         # 接受远程配置
    reports_health: true                # 上报健康状态
    reports_remote_config_status: true  # 上报配置应用状态
    accepts_packages: true              # 接受包分发
    accepts_restart_command: true       # 接受重启命令
    reports_package_statuses: true      # 上报包状态
  
  # 支持的插件类型
  supported_plugins:
    - ottl      # OTTL 转换规则
    - wasm      # WebAssembly 插件
    - lua       # Lua 脚本（可选）
```

**Go 代码实现**：

```go
import (
    "github.com/open-telemetry/opamp-go/client"
    "github.com/open-telemetry/opamp-go/protobufs"
)

func createAgentDescription() *protobufs.AgentDescription {
    return &protobufs.AgentDescription{
        IdentifyingAttributes: []*protobufs.KeyValue{
            stringKeyValue("service.name", "otel-collector-edge"),
            stringKeyValue("service.instance.id", getInstanceID()),
            stringKeyValue("k8s.pod.name", os.Getenv("POD_NAME")),
        },
        NonIdentifyingAttributes: []*protobufs.KeyValue{
            stringKeyValue("region", os.Getenv("REGION")),
            stringKeyValue("tenant", os.Getenv("TENANT")),
        },
        Capabilities: protobufs.AgentCapabilities_AcceptsRemoteConfig |
                     protobufs.AgentCapabilities_ReportsHealth |
                     protobufs.AgentCapabilities_AcceptsPackages,
    }
}
```

## 2. 远程配置下发

### 2.1 基础配置示例

Server 下发的远程配置（带版本和签名）：

```yaml
# 远程配置消息
remote_config:
  # 版本控制
  config:
    config_hash: "sha256:a3f5b8c9d2e1..."
    body: |
      # Base64 编码的配置内容
      cmVjZWl2ZXJzOgogIG90bHA6CiAgICBwcm90b2NvbHM6...
  
  # 数字签名（可选，用于安全验证）
  signature:
    type: RSA_SHA256
    signature_data: "MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA..."
  
  # 配置元数据
  metadata:
    version: "v1.2.3"
    timestamp: "2025-10-05T10:30:00Z"
    author: "platform-team"
    description: "Enable tail sampling and update export endpoints"
```

**解码后的实际配置**：

```yaml
# OpenTelemetry Collector 配置
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  # 批处理优化
  batch:
    timeout: 10s
    send_batch_size: 1024
  
  # 内存限制器
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
    spike_limit_mib: 128
  
  # OTTL 转换规则（动态下发）
  transform:
    error_mode: ignore
    traces:
      # 生产环境脱敏
      - set(attributes["user.id"], SHA256(attributes["user.id"])) 
        where resource.attributes["env"] == "prod"
      
      # 超时标记
      - set(status.message, "timeout_exceeded") 
        where duration > Duration("3s")
      
      # 降维处理
      - delete_key(attributes, "http.request.header.cookie")
      - delete_key(attributes, "http.request.header.authorization")
  
  # 尾部采样（保留错误和慢请求）
  tail_sampling:
    decision_wait: 10s
    num_traces: 100000
    policies:
      - name: errors
        type: status_code
        status_code: {status_codes: [ERROR]}
      - name: slow
        type: latency
        latency: {threshold_ms: 1000}
      - name: probabilistic
        type: probabilistic
        probabilistic: {sampling_percentage: 10}

exporters:
  # 主后端
  otlp/primary:
    endpoint: traces-backend.example.com:4317
    tls:
      insecure: false
      cert_file: /etc/certs/client.crt
      key_file: /etc/certs/client.key
    retry_on_failure:
      enabled: true
      initial_interval: 1s
      max_interval: 30s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 5000
  
  # 备份后端
  otlp/backup:
    endpoint: traces-backup.example.com:4317
    tls:
      insecure: false

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch, transform, tail_sampling]
      exporters: [otlp/primary, otlp/backup]
  
  # 遥测配置
  telemetry:
    logs:
      level: info
    metrics:
      address: 0.0.0.0:8888
```

### 2.2 完整配置结构

```protobuf
message RemoteConfig {
  // 配置内容
  AgentConfigMap config = 1;
  
  // 配置哈希（用于去重和校验）
  bytes config_hash = 2;
  
  // 数字签名（可选）
  Signature signature = 3;
}

message AgentConfigMap {
  // 配置文件映射（支持多文件）
  map<string, AgentConfigFile> config_map = 1;
}

message AgentConfigFile {
  // 文件内容（Base64 编码）
  bytes body = 1;
  
  // 内容类型（yaml/json/toml）
  string content_type = 2;
}
```

### 2.3 配置应用流程

```mermaid
sequenceDiagram
    participant S as OPAMP Server
    participant A as Agent
    participant C as Collector
    
    S->>A: RemoteConfig (hash + signature)
    A->>A: 验证签名
    A->>A: 检查 hash 是否已应用
    
    alt 配置有变更
        A->>A: 解码配置内容
        A->>A: 验证配置格式
        A->>C: 应用新配置（热重载）
        C->>C: 重新加载 Pipeline
        C-->>A: 应用成功
        A->>S: RemoteConfigStatus (SUCCESS)
    else 配置无变更
        A->>S: RemoteConfigStatus (UNCHANGED)
    end
    
    alt 应用失败
        A->>A: 回滚到上一版本
        A->>S: RemoteConfigStatus (FAILED + error_message)
        S->>S: 记录失败，触发告警
    end
```

## 3. 证书轮转流程

```yaml
# Server 下发证书更新
certificate_offer:
  # 新证书
  certificate:
    cert_data: |
      -----BEGIN CERTIFICATE-----
      MIIDXTCCAkWgAwIBAgIJAKL3vZ5Z5Z5ZMA0GCSqGSIb3DQEBCwUAMEUxCzAJBgNV
      ...
      -----END CERTIFICATE-----
    
    private_key_data: |
      -----BEGIN PRIVATE KEY-----
      MIIEvQIBADANBgkqhkiG9w0BAQEFAASCBKcwggSjAgEAAoIBAQC...
      -----END PRIVATE KEY-----
    
    ca_cert_data: |
      -----BEGIN CERTIFICATE-----
      MIIDXTCCAkWgAwIBAgIJAKL3vZ5Z5Z5ZMA0GCSqGSIb3DQEBCwUAMEUxCzAJBgNV
      ...
      -----END CERTIFICATE-----
  
  # 证书元数据
  metadata:
    valid_from: "2025-10-05T00:00:00Z"
    valid_until: "2026-10-05T00:00:00Z"
    serial_number: "0A:B3:C5:D7:E9:F1"
    fingerprint: "sha256:1a2b3c4d5e6f..."
  
  # 签名（防篡改）
  signature:
    type: RSA_SHA256
    signature_data: "MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8..."
```

**证书应用流程**：

```go
func handleCertificateOffer(offer *protobufs.CertificateOffer) error {
    // 1. 验证签名
    if err := verifyCertificateSignature(offer); err != nil {
        return fmt.Errorf("signature verification failed: %w", err)
    }
    
    // 2. 验证证书有效期
    cert, err := x509.ParseCertificate(offer.Certificate.CertData)
    if err != nil {
        return fmt.Errorf("invalid certificate: %w", err)
    }
    
    // 3. 原子替换证书文件
    if err := atomicWriteCertificate(cert, offer.Certificate); err != nil {
        return fmt.Errorf("failed to write certificate: %w", err)
    }
    
    // 4. 重新加载 TLS 配置
    if err := reloadTLSConfig(); err != nil {
        // 回滚到旧证书
        rollbackCertificate()
        return fmt.Errorf("failed to reload TLS: %w", err)
    }
    
    // 5. 上报成功状态
    reportCertificateStatus(protobufs.CertificateStatus_INSTALLED)
    return nil
}
```

## 4. 插件/二进制升级流程

### 4.1 WASM 插件分发

```yaml
# Server 通知可用包
package_available:
  # 包类型
  type: WASM_PLUGIN
  
  # 包信息
  package:
    name: custom-processor
    version: v1.2.0
    file:
      download_url: https://packages.example.com/custom-processor-v1.2.0.wasm
      content_hash: sha256:9f8e7d6c5b4a3...
      signature: RSA_SHA256:MIIBIjANBgkqhkiG9w0...
      size_bytes: 2048576
  
  # 应用策略
  deployment:
    # 立即应用还是等待确认
    auto_apply: false
    # 应用后是否需要重启
    requires_restart: false
```

**Agent 处理流程**：

```go
func handlePackageAvailable(pkg *protobufs.PackageAvailable) error {
    // 1. 下载包
    data, err := downloadPackage(pkg.Package.File.DownloadUrl)
    if err != nil {
        return fmt.Errorf("download failed: %w", err)
    }
    
    // 2. 验证哈希
    hash := sha256.Sum256(data)
    if hex.EncodeToString(hash[:]) != pkg.Package.File.ContentHash {
        return fmt.Errorf("hash mismatch")
    }
    
    // 3. 验证签名
    if err := verifySignature(data, pkg.Package.File.Signature); err != nil {
        return fmt.Errorf("signature verification failed: %w", err)
    }
    
    // 4. 安装插件
    pluginPath := filepath.Join("/opt/plugins", pkg.Package.Name+".wasm")
    if err := os.WriteFile(pluginPath, data, 0644); err != nil {
        return fmt.Errorf("install failed: %w", err)
    }
    
    // 5. 加载插件（热加载）
    if err := loadWASMPlugin(pluginPath); err != nil {
        os.Remove(pluginPath)  // 清理失败的插件
        return fmt.Errorf("load failed: %w", err)
    }
    
    // 6. 上报状态
    reportPackageStatus(pkg.Package.Name, protobufs.PackageStatus_INSTALLED)
    return nil
}
```

### 4.2 Agent 二进制升级

```yaml
# 完整升级流程配置
package_available:
  type: AGENT_BINARY
  
  package:
    name: otel-collector
    version: v0.95.0
    file:
      download_url: https://packages.example.com/otelcol-v0.95.0-linux-amd64
      content_hash: sha256:a1b2c3d4e5f6...
      signature: RSA_SHA256:MIIBIjANBgkqhkiG9w0...
      size_bytes: 104857600  # 100MB
  
  deployment:
    auto_apply: false  # 需要人工确认
    requires_restart: true
    
    # 升级策略
    strategy:
      type: rolling_update
      max_unavailable: 10%
      health_check_timeout: 30s
```

**升级时序图**：

```mermaid
sequenceDiagram
    participant S as OPAMP Server
    participant A as Agent (Old)
    participant N as Agent (New)
    participant M as Monitor
    
    S->>A: PackageAvailable (v0.95.0)
    A->>A: 下载 + 验证
    A->>S: PackageStatus (DOWNLOADED)
    
    S->>A: Command (RESTART)
    A->>A: 保存当前状态
    A->>N: 启动新版本
    N->>N: 加载配置
    N->>S: AgentIdentify (v0.95.0)
    N->>M: 健康检查
    M-->>N: OK
    N->>S: StatusReport (HEALTHY)
    S->>S: 标记升级成功
    A->>A: 退出旧版本
```

## 5. 健康监控与自愈

### 5.1 健康状态上报

```yaml
# Agent 定期上报健康状态
health_report:
  # 整体健康状态
  healthy: true
  
  # 详细指标
  metrics:
    # 资源使用
    cpu_usage_percent: 45.2
    memory_usage_bytes: 536870912  # 512MB
    memory_limit_bytes: 1073741824  # 1GB
    goroutines_count: 128
    
    # 处理指标
    spans_received_per_sec: 15000
    spans_exported_per_sec: 14850
    spans_dropped_per_sec: 150
    export_latency_p99_ms: 85
    
    # 队列状态
    queue_size: 2048
    queue_capacity: 5000
    queue_utilization_percent: 40.96
    
    # 错误率
    export_error_rate_percent: 1.0
    pipeline_error_count: 5
  
  # 最近错误
  recent_errors:
    - timestamp: "2025-10-05T10:25:30Z"
      message: "export failed: context deadline exceeded"
      count: 3
    - timestamp: "2025-10-05T10:20:15Z"
      message: "memory limiter: dropping data"
      count: 2
  
  # 配置状态
  config_status:
    config_hash: "sha256:a3f5b8c9d2e1..."
    last_applied: "2025-10-05T10:00:00Z"
    status: APPLIED
```

### 5.2 自动回滚配置

```yaml
# Server 端自愈策略
auto_healing:
  # 触发条件
  triggers:
    - name: high_error_rate
      condition: export_error_rate_percent > 5
      action: rollback_config
      cooldown: 5m
    
    - name: high_memory
      condition: memory_usage_bytes > 0.9 * memory_limit_bytes
      action: apply_memory_limit
      cooldown: 1m
    
    - name: queue_overflow
      condition: queue_utilization_percent > 90
      action: increase_sampling
      cooldown: 2m
  
  # 回滚策略
  rollback:
    max_attempts: 3
    observation_window: 10m
    success_threshold: 95%  # 95% Agent 成功应用才算成功
```

**自愈响应示例**：

```yaml
# Server 下发紧急配置（降低采样率）
remote_config:
  config_hash: "sha256:emergency_001"
  priority: URGENT
  content:
    processors:
      probabilistic_sampler:
        sampling_percentage: 5  # 从 10% 降至 5%
      
      memory_limiter:
        limit_mib: 400  # 从 512MB 降至 400MB
        spike_limit_mib: 100
```

## 6. 灰度发布示例

```yaml
# 分阶段灰度发布配置
rollout_plan:
  # 配置内容
  config:
    config_hash: "sha256:feature_new_exporter"
    body: "..."  # 新配置内容
  
  # 灰度策略
  stages:
    # 阶段 1：Staging 环境
    - name: staging
      selector:
        match_labels:
          env: staging
      weight: 100%
      duration: 2h
      success_criteria:
        min_healthy_percent: 95
        max_error_rate: 1
    
    # 阶段 2：生产环境金丝雀（单个区域）
    - name: prod_canary
      selector:
        match_labels:
          env: prod
          region: us-west-1
      weight: 10%
      duration: 1h
      success_criteria:
        min_healthy_percent: 98
        max_error_rate: 0.5
    
    # 阶段 3：生产环境扩展
    - name: prod_rollout
      selector:
        match_labels:
          env: prod
      weight: 50%
      duration: 30m
      success_criteria:
        min_healthy_percent: 98
        max_error_rate: 0.5
    
    # 阶段 4：全量发布
    - name: prod_full
      selector:
        match_labels:
          env: prod
      weight: 100%
      success_criteria:
        min_healthy_percent: 99
        max_error_rate: 0.1
  
  # 自动回滚
  auto_rollback:
    enabled: true
    triggers:
      - error_rate_spike: 2x
      - healthy_agents_below: 90%
      - manual_trigger: true
```

## 7. 完整部署示例

### 7.1 Server 端配置

```yaml
# OPAMP Server 配置
server:
  # 监听地址
  listen:
    grpc: 0.0.0.0:4320
    http: 0.0.0.0:8080  # 管理 UI
  
  # TLS 配置
  tls:
    enabled: true
    cert_file: /etc/opamp/server.crt
    key_file: /etc/opamp/server.key
    client_ca_file: /etc/opamp/ca.crt
    client_auth: require_and_verify
  
  # 配置存储
  config_store:
    type: git
    git:
      repository: https://github.com/example/opamp-configs.git
      branch: main
      sync_interval: 1m
      auth:
        type: ssh_key
        ssh_key_file: /etc/opamp/git_deploy_key
  
  # 包仓库
  package_registry:
    type: s3
    s3:
      bucket: opamp-packages
      region: us-west-2
      endpoint: https://s3.us-west-2.amazonaws.com
  
  # 数据库（存储 Agent 状态）
  database:
    type: postgresql
    dsn: postgres://opamp:password@postgres:5432/opamp?sslmode=require
  
  # 认证
  auth:
    type: jwt
    jwt:
      signing_key_file: /etc/opamp/jwt_signing_key
      expiration: 24h
```

### 7.2 Agent 端配置

```yaml
# OPAMP Agent 配置
opamp:
  # Server 地址
  server:
    endpoint: wss://opamp.example.com:4320/v1/opamp
    
    # TLS 配置
    tls:
      insecure: false
      cert_file: /etc/certs/agent.crt
      key_file: /etc/certs/agent.key
      ca_file: /etc/certs/ca.crt
    
    # 认证
    headers:
      Authorization: "Bearer ${OPAMP_TOKEN}"
  
  # Agent 身份
  agent:
    # 从环境变量读取
    instance_id: "${HOSTNAME}"
    
    # 标签（用于配置选择）
    labels:
      env: "${ENV}"
      region: "${REGION}"
      tenant: "${TENANT}"
  
  # 能力配置
  capabilities:
    accepts_remote_config: true
    reports_health: true
    accepts_packages: true
    accepts_restart_command: true
  
  # 健康上报
  health:
    report_interval: 30s
    metrics:
      - cpu_usage
      - memory_usage
      - goroutines
      - spans_rate
      - export_latency
  
  # 本地配置文件路径
  local_config_path: /etc/otelcol/config.yaml
  
  # 包存储路径
  packages_dir: /opt/otelcol/packages
```

## 8. 最佳实践

1. **配置管理**：
   - 使用 Git 存储配置，保留完整历史
   - 配置变更需要 Code Review
   - 使用 CI/CD 自动验证配置格式

2. **安全性**：
   - 始终启用 mTLS 双向认证
   - 对所有配置和包进行签名验证
   - 定期轮转证书（建议 90 天）
   - 使用 Secret 管理工具存储敏感信息

3. **灰度发布**：
   - 先在 Staging 环境验证
   - 生产环境从单个区域开始
   - 设置明确的成功标准和回滚条件
   - 保留观察窗口（建议 10-30 分钟）

4. **监控告警**：
   - 监控 Agent 健康状态和配置应用成功率
   - 设置异常告警（错误率、资源使用）
   - 记录所有配置变更的审计日志

5. **容量规划**：
   - Server 端需要处理大量 Agent 连接（建议单实例 < 10K）
   - 使用负载均衡和水平扩展
   - 配置合理的心跳间隔（建议 30-60 秒）

6. **故障恢复**：
   - Agent 断线后自动重连（指数退避）
   - Server 故障时 Agent 使用本地配置继续运行
   - 保留配置历史，支持快速回滚

## 9. 完整端到端示例

### 9.1 Server 端完整实现

**Go 实现的 OPAMP Server**：

```go
package main

import (
    "context"
    "crypto/tls"
    "crypto/x509"
    "encoding/json"
    "fmt"
    "io/ioutil"
    "log"
    "net/http"
    "sync"
    "time"

    "github.com/google/uuid"
    "github.com/gorilla/websocket"
    "github.com/open-telemetry/opamp-go/protobufs"
    "github.com/open-telemetry/opamp-go/server"
    "github.com/open-telemetry/opamp-go/server/types"
    "google.golang.org/protobuf/proto"
)

type OPAMPServer struct {
    server     server.OpAMPServer
    agents     map[string]*AgentState
    agentsMux  sync.RWMutex
    configRepo *ConfigRepository
}

type AgentState struct {
    InstanceID      string
    LastHeartbeat   time.Time
    EffectiveConfig *protobufs.AgentConfigMap
    Health          *protobufs.ComponentHealth
    RemoteConfig    *protobufs.AgentRemoteConfig
}

type ConfigRepository struct {
    configs map[string]*protobufs.AgentRemoteConfig
    mu      sync.RWMutex
}

func NewConfigRepository() *ConfigRepository {
    return &ConfigRepository{
        configs: make(map[string]*protobufs.AgentRemoteConfig),
    }
}

func (r *ConfigRepository) GetConfig(agentID string, labels map[string]string) (*protobufs.AgentRemoteConfig, error) {
    r.mu.RLock()
    defer r.mu.RUnlock()
    
    // 根据标签匹配配置
    env := labels["env"]
    region := labels["region"]
    
    configKey := fmt.Sprintf("%s-%s", env, region)
    if config, ok := r.configs[configKey]; ok {
        return config, nil
    }
    
    // 返回默认配置
    return r.getDefaultConfig(), nil
}

func (r *ConfigRepository) getDefaultConfig() *protobufs.AgentRemoteConfig {
    configYAML := `
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 512

exporters:
  otlp:
    endpoint: collector.example.com:4317
    tls:
      insecure: false

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [otlp]
`
    
    return &protobufs.AgentRemoteConfig{
        Config: &protobufs.AgentConfigMap{
            ConfigMap: map[string]*protobufs.AgentConfigFile{
                "collector.yaml": {
                    Body:        []byte(configYAML),
                    ContentType: "application/x-yaml",
                },
            },
        },
        ConfigHash: []byte(hashConfig(configYAML)),
    }
}

func (r *ConfigRepository) UpdateConfig(key string, config *protobufs.AgentRemoteConfig) {
    r.mu.Lock()
    defer r.mu.Unlock()
    r.configs[key] = config
}

func NewOPAMPServer() *OPAMPServer {
    return &OPAMPServer{
        agents:     make(map[string]*AgentState),
        configRepo: NewConfigRepository(),
    }
}

func (s *OPAMPServer) Start(addr string, tlsConfig *tls.Config) error {
    settings := server.StartSettings{
        Settings: server.Settings{
            Callbacks: server.CallbacksStruct{
                OnConnectingFunc:         s.onAgentConnecting,
                OnConnectedFunc:          s.onAgentConnected,
                OnMessageFunc:            s.onMessage,
                OnConnectionCloseFunc:    s.onConnectionClose,
            },
        },
        ListenEndpoint: addr,
        TLSConfig:      tlsConfig,
    }
    
    srv := server.New(&NopLogger{})
    if err := srv.Start(settings); err != nil {
        return fmt.Errorf("failed to start server: %w", err)
    }
    
    s.server = srv
    
    // 启动健康检查监控
    go s.monitorAgentHealth()
    
    log.Printf("OPAMP Server started on %s", addr)
    return nil
}

func (s *OPAMPServer) onAgentConnecting(request *http.Request) types.ConnectionResponse {
    // 验证客户端证书
    if len(request.TLS.PeerCertificates) == 0 {
        log.Println("Client certificate required")
        return types.ConnectionResponse{
            Accept: false,
            HTTPStatusCode: http.StatusUnauthorized,
        }
    }
    
    // 验证 Authorization header
    authHeader := request.Header.Get("Authorization")
    if !s.validateToken(authHeader) {
        log.Println("Invalid authorization token")
        return types.ConnectionResponse{
            Accept: false,
            HTTPStatusCode: http.StatusForbidden,
        }
    }
    
    return types.ConnectionResponse{
        Accept: true,
        HTTPStatusCode: http.StatusSwitchingProtocols,
    }
}

func (s *OPAMPServer) onAgentConnected(conn types.Connection) {
    log.Printf("Agent connected: %s", conn.RemoteAddr())
}

func (s *OPAMPServer) onMessage(conn types.Connection, message *protobufs.AgentToServer) *protobufs.ServerToAgent {
    instanceID := string(message.InstanceUid)
    
    // 更新 Agent 状态
    s.updateAgentState(instanceID, message)
    
    // 构建响应
    response := &protobufs.ServerToAgent{
        InstanceUid: message.InstanceUid,
    }
    
    // 处理配置请求
    if message.RemoteConfigStatus != nil {
        config, err := s.getConfigForAgent(instanceID, message)
        if err != nil {
            log.Printf("Failed to get config for agent %s: %v", instanceID, err)
        } else {
            response.RemoteConfig = config
            response.Flags = protobufs.ServerToAgentFlags_ServerToAgentFlags_ReportFullState
        }
    }
    
    // 处理健康报告
    if message.Health != nil {
        s.processHealthReport(instanceID, message.Health)
    }
    
    // 处理包状态
    if message.PackageStatuses != nil {
        s.processPackageStatus(instanceID, message.PackageStatuses)
    }
    
    return response
}

func (s *OPAMPServer) onConnectionClose(conn types.Connection) {
    log.Printf("Agent disconnected: %s", conn.RemoteAddr())
}

func (s *OPAMPServer) updateAgentState(instanceID string, message *protobufs.AgentToServer) {
    s.agentsMux.Lock()
    defer s.agentsMux.Unlock()
    
    agent, exists := s.agents[instanceID]
    if !exists {
        agent = &AgentState{
            InstanceID: instanceID,
        }
        s.agents[instanceID] = agent
    }
    
    agent.LastHeartbeat = time.Now()
    
    if message.EffectiveConfig != nil {
        agent.EffectiveConfig = message.EffectiveConfig
    }
    
    if message.Health != nil {
        agent.Health = message.Health
    }
}

func (s *OPAMPServer) getConfigForAgent(instanceID string, message *protobufs.AgentToServer) (*protobufs.AgentRemoteConfig, error) {
    // 提取 Agent 标签
    labels := make(map[string]string)
    if message.AgentDescription != nil && message.AgentDescription.IdentifyingAttributes != nil {
        for _, attr := range message.AgentDescription.IdentifyingAttributes {
            labels[attr.Key] = attr.Value.GetStringValue()
        }
    }
    
    // 从配置仓库获取配置
    config, err := s.configRepo.GetConfig(instanceID, labels)
    if err != nil {
        return nil, err
    }
    
    return config, nil
}

func (s *OPAMPServer) processHealthReport(instanceID string, health *protobufs.ComponentHealth) {
    if !health.Healthy {
        log.Printf("ALERT: Agent %s is unhealthy: %s", instanceID, health.LastError)
        // 触发告警
        s.triggerAlert(instanceID, health)
    }
}

func (s *OPAMPServer) processPackageStatus(instanceID string, status *protobufs.PackageStatuses) {
    for name, pkgStatus := range status.Packages {
        if pkgStatus.ErrorMessage != "" {
            log.Printf("Package %s installation failed on agent %s: %s", 
                name, instanceID, pkgStatus.ErrorMessage)
        } else {
            log.Printf("Package %s successfully installed on agent %s (hash: %x)", 
                name, instanceID, pkgStatus.AgentHasHash)
        }
    }
}

func (s *OPAMPServer) monitorAgentHealth() {
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()
    
    for range ticker.C {
        s.agentsMux.RLock()
        now := time.Now()
        for id, agent := range s.agents {
            if now.Sub(agent.LastHeartbeat) > 2*time.Minute {
                log.Printf("ALERT: Agent %s heartbeat timeout", id)
                // 触发告警
            }
        }
        s.agentsMux.RUnlock()
    }
}

func (s *OPAMPServer) triggerAlert(instanceID string, health *protobufs.ComponentHealth) {
    // 实现告警逻辑（发送到 PagerDuty、Slack 等）
    log.Printf("Triggering alert for agent %s", instanceID)
}

func (s *OPAMPServer) validateToken(authHeader string) bool {
    // 实现 JWT token 验证
    return authHeader != ""
}

func hashConfig(config string) string {
    // 实现配置哈希
    return fmt.Sprintf("%x", len(config))
}

type NopLogger struct{}

func (l *NopLogger) Debugf(format string, v ...interface{}) {}
func (l *NopLogger) Errorf(format string, v ...interface{}) {
    log.Printf("ERROR: "+format, v...)
}

func loadTLSConfig(certFile, keyFile, caFile string) (*tls.Config, error) {
    cert, err := tls.LoadX509KeyPair(certFile, keyFile)
    if err != nil {
        return nil, err
    }
    
    caCert, err := ioutil.ReadFile(caFile)
    if err != nil {
        return nil, err
    }
    
    caCertPool := x509.NewCertPool()
    caCertPool.AppendCertsFromPEM(caCert)
    
    return &tls.Config{
        Certificates: []tls.Certificate{cert},
        ClientAuth:   tls.RequireAndVerifyClientCert,
        ClientCAs:    caCertPool,
        MinVersion:   tls.VersionTLS13,
    }, nil
}

func main() {
    // 加载 TLS 配置
    tlsConfig, err := loadTLSConfig(
        "/etc/certs/server.crt",
        "/etc/certs/server.key",
        "/etc/certs/ca.crt",
    )
    if err != nil {
        log.Fatalf("Failed to load TLS config: %v", err)
    }
    
    // 创建并启动 Server
    server := NewOPAMPServer()
    if err := server.Start("0.0.0.0:4320", tlsConfig); err != nil {
        log.Fatalf("Failed to start server: %v", err)
    }
    
    // 等待中断信号
    select {}
}
```

### 9.2 Agent 端完整实现

**Go 实现的 OPAMP Agent**：

```go
package main

import (
    "context"
    "crypto/tls"
    "crypto/x509"
    "fmt"
    "io/ioutil"
    "log"
    "os"
    "os/signal"
    "syscall"
    "time"

    "github.com/google/uuid"
    "github.com/open-telemetry/opamp-go/client"
    "github.com/open-telemetry/opamp-go/client/types"
    "github.com/open-telemetry/opamp-go/protobufs"
)

type OPAMPAgent struct {
    client         client.OpAMPClient
    instanceID     uuid.UUID
    agentVersion   string
    effectiveConfig *protobufs.AgentConfigMap
    configFile     string
    collectorCmd   *CollectorManager
}

type CollectorManager struct {
    // Collector 进程管理
}

func NewOPAMPAgent(configFile string) *OPAMPAgent {
    return &OPAMPAgent{
        instanceID:   uuid.New(),
        agentVersion: "1.0.0",
        configFile:   configFile,
        collectorCmd: &CollectorManager{},
    }
}

func (a *OPAMPAgent) Start(serverURL string, tlsConfig *tls.Config) error {
    logger := &SimpleLogger{}
    
    opampClient := client.NewWebSocket(logger)
    
    settings := types.StartSettings{
        OpAMPServerURL: serverURL,
        TLSConfig:      tlsConfig,
        InstanceUid:    a.instanceID.String(),
        Callbacks: types.CallbacksStruct{
            OnConnectFunc:          a.onConnect,
            OnConnectFailedFunc:    a.onConnectFailed,
            OnErrorFunc:            a.onError,
            OnMessageFunc:          a.onMessage,
            OnOpampConnectionSettingsFunc: a.onOpampConnectionSettings,
            SaveRemoteConfigStatusFunc:    a.saveRemoteConfigStatus,
            GetEffectiveConfigFunc:        a.getEffectiveConfig,
        },
        Capabilities: protobufs.AgentCapabilities_AgentCapabilities_AcceptsRemoteConfig |
            protobufs.AgentCapabilities_AgentCapabilities_ReportsHealth |
            protobufs.AgentCapabilities_AgentCapabilities_AcceptsPackages |
            protobufs.AgentCapabilities_AgentCapabilities_AcceptsRestartCommand,
    }
    
    if err := opampClient.Start(context.Background(), settings); err != nil {
        return fmt.Errorf("failed to start OPAMP client: %w", err)
    }
    
    a.client = opampClient
    
    // 发送初始状态
    if err := a.sendAgentDescription(); err != nil {
        log.Printf("Failed to send agent description: %v", err)
    }
    
    // 启动健康报告
    go a.reportHealth()
    
    log.Printf("OPAMP Agent started, instance ID: %s", a.instanceID)
    return nil
}

func (a *OPAMPAgent) onConnect() {
    log.Println("Connected to OPAMP server")
}

func (a *OPAMPAgent) onConnectFailed(err error) {
    log.Printf("Failed to connect to OPAMP server: %v", err)
}

func (a *OPAMPAgent) onError(err error) {
    log.Printf("OPAMP error: %v", err)
}

func (a *OPAMPAgent) onMessage(ctx context.Context, msg *types.MessageData) {
    // 处理远程配置
    if msg.RemoteConfig != nil {
        if err := a.applyRemoteConfig(msg.RemoteConfig); err != nil {
            log.Printf("Failed to apply remote config: %v", err)
            a.sendConfigStatus(false, err.Error())
        } else {
            log.Println("Remote config applied successfully")
            a.sendConfigStatus(true, "")
        }
    }
    
    // 处理包更新
    if msg.PackagesAvailable != nil {
        a.downloadAndInstallPackages(msg.PackagesAvailable)
    }
    
    // 处理重启命令
    if msg.AgentIdentification != nil {
        log.Println("Received restart command")
        a.restartCollector()
    }
}

func (a *OPAMPAgent) onOpampConnectionSettings(ctx context.Context, settings *protobufs.OpAMPConnectionSettings) error {
    // 处理连接设置更新（证书轮转等）
    log.Println("Received new connection settings")
    return nil
}

func (a *OPAMPAgent) saveRemoteConfigStatus(ctx context.Context, status *protobufs.RemoteConfigStatus) {
    // 保存配置状态到本地
    log.Printf("Saving remote config status: %v", status)
}

func (a *OPAMPAgent) getEffectiveConfig(ctx context.Context) (*protobufs.EffectiveConfig, error) {
    // 读取当前生效的配置
    configData, err := ioutil.ReadFile(a.configFile)
    if err != nil {
        return nil, err
    }
    
    return &protobufs.EffectiveConfig{
        ConfigMap: &protobufs.AgentConfigMap{
            ConfigMap: map[string]*protobufs.AgentConfigFile{
                "collector.yaml": {
                    Body:        configData,
                    ContentType: "application/x-yaml",
                },
            },
        },
    }, nil
}

func (a *OPAMPAgent) sendAgentDescription() error {
    hostname, _ := os.Hostname()
    
    description := &protobufs.AgentDescription{
        IdentifyingAttributes: []*protobufs.KeyValue{
            {Key: "service.name", Value: &protobufs.AnyValue{Value: &protobufs.AnyValue_StringValue{StringValue: "otel-collector"}}},
            {Key: "service.version", Value: &protobufs.AnyValue{Value: &protobufs.AnyValue_StringValue{StringValue: a.agentVersion}}},
            {Key: "host.name", Value: &protobufs.AnyValue{Value: &protobufs.AnyValue_StringValue{StringValue: hostname}}},
            {Key: "env", Value: &protobufs.AnyValue{Value: &protobufs.AnyValue_StringValue{StringValue: os.Getenv("ENV")}}},
            {Key: "region", Value: &protobufs.AnyValue{Value: &protobufs.AnyValue_StringValue{StringValue: os.Getenv("REGION")}}},
        },
        NonIdentifyingAttributes: []*protobufs.KeyValue{
            {Key: "os.type", Value: &protobufs.AnyValue{Value: &protobufs.AnyValue_StringValue{StringValue: "linux"}}},
        },
    }
    
    return a.client.SetAgentDescription(description)
}

func (a *OPAMPAgent) applyRemoteConfig(config *protobufs.AgentRemoteConfig) error {
    // 1. 验证配置
    if err := a.validateConfig(config); err != nil {
        return fmt.Errorf("config validation failed: %w", err)
    }
    
    // 2. 备份当前配置
    if err := a.backupCurrentConfig(); err != nil {
        return fmt.Errorf("failed to backup config: %w", err)
    }
    
    // 3. 写入新配置
    for filename, fileContent := range config.Config.ConfigMap {
        filepath := fmt.Sprintf("/etc/otelcol/%s", filename)
        if err := ioutil.WriteFile(filepath, fileContent.Body, 0644); err != nil {
            // 回滚
            a.restoreBackup()
            return fmt.Errorf("failed to write config: %w", err)
        }
    }
    
    // 4. 重载 Collector
    if err := a.reloadCollector(); err != nil {
        // 回滚
        a.restoreBackup()
        return fmt.Errorf("failed to reload collector: %w", err)
    }
    
    a.effectiveConfig = config.Config
    return nil
}

func (a *OPAMPAgent) validateConfig(config *protobufs.AgentRemoteConfig) error {
    // 实现配置验证逻辑
    return nil
}

func (a *OPAMPAgent) backupCurrentConfig() error {
    // 实现配置备份
    return nil
}

func (a *OPAMPAgent) restoreBackup() error {
    // 实现配置恢复
    return nil
}

func (a *OPAMPAgent) reloadCollector() error {
    // 发送 SIGHUP 信号重载 Collector
    return nil
}

func (a *OPAMPAgent) restartCollector() {
    log.Println("Restarting collector...")
    // 实现 Collector 重启逻辑
}

func (a *OPAMPAgent) sendConfigStatus(success bool, errorMsg string) {
    status := &protobufs.RemoteConfigStatus{
        LastRemoteConfigHash: []byte("config-hash"),
        Status:               protobufs.RemoteConfigStatuses_RemoteConfigStatuses_APPLIED,
    }
    
    if !success {
        status.Status = protobufs.RemoteConfigStatuses_RemoteConfigStatuses_FAILED
        status.ErrorMessage = errorMsg
    }
    
    a.client.SetRemoteConfigStatus(status)
}

func (a *OPAMPAgent) reportHealth() {
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()
    
    for range ticker.C {
        health := &protobufs.ComponentHealth{
            Healthy:              true,
            StartTimeUnixNano:    uint64(time.Now().UnixNano()),
            LastError:            "",
        }
        
        // 检查 Collector 健康状态
        if !a.collectorCmd.IsHealthy() {
            health.Healthy = false
            health.LastError = "Collector is not responding"
        }
        
        a.client.SetHealth(health)
    }
}

func (a *OPAMPAgent) downloadAndInstallPackages(packages *protobufs.PackagesAvailable) {
    for name, pkg := range packages.Packages {
        log.Printf("Downloading package %s from %s", name, pkg.DownloadUrl)
        // 实现包下载和安装逻辑
    }
}

func (a *OPAMPAgent) Stop() {
    if a.client != nil {
        a.client.Stop(context.Background())
    }
}

type SimpleLogger struct{}

func (l *SimpleLogger) Debugf(format string, v ...interface{}) {
    log.Printf("DEBUG: "+format, v...)
}

func (l *SimpleLogger) Errorf(format string, v ...interface{}) {
    log.Printf("ERROR: "+format, v...)
}

func (cm *CollectorManager) IsHealthy() bool {
    // 实现健康检查
    return true
}

func loadAgentTLSConfig(certFile, keyFile, caFile string) (*tls.Config, error) {
    cert, err := tls.LoadX509KeyPair(certFile, keyFile)
    if err != nil {
        return nil, err
    }
    
    caCert, err := ioutil.ReadFile(caFile)
    if err != nil {
        return nil, err
    }
    
    caCertPool := x509.NewCertPool()
    caCertPool.AppendCertsFromPEM(caCert)
    
    return &tls.Config{
        Certificates: []tls.Certificate{cert},
        RootCAs:      caCertPool,
        MinVersion:   tls.VersionTLS13,
    }, nil
}

func main() {
    // 加载 TLS 配置
    tlsConfig, err := loadAgentTLSConfig(
        "/etc/certs/agent.crt",
        "/etc/certs/agent.key",
        "/etc/certs/ca.crt",
    )
    if err != nil {
        log.Fatalf("Failed to load TLS config: %v", err)
    }
    
    // 创建并启动 Agent
    agent := NewOPAMPAgent("/etc/otelcol/config.yaml")
    if err := agent.Start("wss://opamp.example.com:4320/v1/opamp", tlsConfig); err != nil {
        log.Fatalf("Failed to start agent: %v", err)
    }
    
    // 等待中断信号
    sigChan := make(chan os.Signal, 1)
    signal.Notify(sigChan, syscall.SIGINT, syscall.SIGTERM)
    <-sigChan
    
    log.Println("Shutting down...")
    agent.Stop()
}
```

### 9.3 测试脚本

**集成测试脚本**：

```bash
#!/bin/bash
# test-opamp.sh

set -e

echo "=== OPAMP 端到端测试 ==="

# 1. 启动 Server
echo "Starting OPAMP Server..."
docker run -d --name opamp-server \
  -p 4320:4320 \
  -v $(pwd)/certs:/etc/certs \
  -v $(pwd)/configs:/etc/configs \
  opamp-server:latest

sleep 5

# 2. 启动 Agent
echo "Starting OPAMP Agent..."
docker run -d --name opamp-agent \
  -v $(pwd)/certs:/etc/certs \
  -e OPAMP_SERVER=wss://opamp-server:4320/v1/opamp \
  -e ENV=test \
  -e REGION=us-west-2 \
  opamp-agent:latest

sleep 10

# 3. 验证连接
echo "Verifying connection..."
docker logs opamp-server | grep "Agent connected" || {
  echo "ERROR: Agent failed to connect"
  exit 1
}

# 4. 推送新配置
echo "Pushing new configuration..."
curl -X POST http://localhost:8080/api/v1/config \
  -H "Content-Type: application/json" \
  -d '{
    "target": "env=test,region=us-west-2",
    "config": {
      "receivers": {
        "otlp": {
          "protocols": {
            "grpc": {"endpoint": "0.0.0.0:4317"}
          }
        }
      }
    }
  }'

sleep 5

# 5. 验证配置应用
echo "Verifying config application..."
docker exec opamp-agent cat /etc/otelcol/config.yaml | grep "0.0.0.0:4317" || {
  echo "ERROR: Config not applied"
  exit 1
}

# 6. 清理
echo "Cleaning up..."
docker stop opamp-server opamp-agent
docker rm opamp-server opamp-agent

echo "=== 测试完成 ==="
```

---

**参考资料**：

- OPAMP 概览：`docs/opamp/overview.md`
- 技术模型：`docs/design/technical-model.md`
- OTTL 示例：`docs/otlp/ottl-examples.md`
