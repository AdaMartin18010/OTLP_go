# OPAMP 控制平面协议规范与设计

> **文档版本**: v1.0  
> **最后更新**: 2025-10-03  
> **OPAMP 版本**: v1.0 (Stable since 2025-03)  
> **关联文档**: [OTTL 转换语言](./06-ottl-transformation-language.md), [分布式架构](./05-distributed-architecture-mapping.md)

---

## 目录

- [OPAMP 控制平面协议规范与设计](#opamp-控制平面协议规范与设计)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 核心价值](#11-核心价值)
    - [1.2 与数据平面的关系](#12-与数据平面的关系)
  - [2. 协议架构](#2-协议架构)
    - [2.1 设计目标](#21-设计目标)
    - [2.2 消息模型](#22-消息模型)
      - [2.2.1 Protobuf 定义](#221-protobuf-定义)
      - [2.2.2 Capability 位掩码](#222-capability-位掩码)
    - [2.3 传输层](#23-传输层)
      - [2.3.1 WebSocket (推荐)](#231-websocket-推荐)
      - [2.3.2 HTTP/2 (后备)](#232-http2-后备)
  - [3. 核心消息规范](#3-核心消息规范)
    - [3.1 AgentToServer](#31-agenttoserver)
      - [3.1.1 AgentDescription](#311-agentdescription)
      - [3.1.2 EffectiveConfig](#312-effectiveconfig)
      - [3.1.3 AgentHealth](#313-agenthealth)
    - [3.2 ServerToAgent](#32-servertoagent)
      - [3.2.1 AgentRemoteConfig](#321-agentremoteconfig)
      - [3.2.2 PackagesAvailable](#322-packagesavailable)
    - [3.3 心跳与连接管理](#33-心跳与连接管理)
      - [3.3.1 心跳机制](#331-心跳机制)
      - [3.3.2 断线重连](#332-断线重连)
  - [4. 配置管理](#4-配置管理)
    - [4.1 远程配置下发](#41-远程配置下发)
      - [4.1.1 配置格式 (YAML)](#411-配置格式-yaml)
      - [4.1.2 配置应用流程](#412-配置应用流程)
    - [4.2 配置哈希与版本控制](#42-配置哈希与版本控制)
      - [4.2.1 Canonical Hash 算法](#421-canonical-hash-算法)
    - [4.3 多配置源合并](#43-多配置源合并)
  - [5. 证书与密钥管理](#5-证书与密钥管理)
    - [5.1 mTLS 证书轮换](#51-mtls-证书轮换)
      - [5.1.1 证书下发](#511-证书下发)
      - [5.1.2 原子替换流程](#512-原子替换流程)
    - [5.2 信任链验证](#52-信任链验证)
  - [6. 包管理与升级](#6-包管理与升级)
    - [6.1 二进制分发](#61-二进制分发)
      - [6.1.1 包描述符](#611-包描述符)
      - [6.1.2 下载与验证](#612-下载与验证)
    - [6.2 签名验证](#62-签名验证)
      - [6.2.1 Ed25519 签名方案](#621-ed25519-签名方案)
    - [6.3 原子升级机制](#63-原子升级机制)
      - [6.3.1 Linux 原子替换](#631-linux-原子替换)
      - [6.3.2 回滚机制](#632-回滚机制)
  - [7. 灰度发布与金丝雀](#7-灰度发布与金丝雀)
    - [7.1 标签选择器](#71-标签选择器)
      - [7.1.1 语法](#711-语法)
      - [7.1.2 匹配逻辑](#712-匹配逻辑)
    - [7.2 权重路由](#72-权重路由)
      - [7.2.1 金丝雀发布策略](#721-金丝雀发布策略)
      - [7.2.2 实现](#722-实现)
    - [7.3 自动回滚](#73-自动回滚)
      - [7.3.1 健康检查触发](#731-健康检查触发)
  - [8. 实现示例](#8-实现示例)
    - [8.1 Golang Agent 实现](#81-golang-agent-实现)
    - [8.2 控制平面实现](#82-控制平面实现)
  - [9. 安全模型](#9-安全模型)
    - [9.1 威胁模型](#91-威胁模型)
    - [9.2 审计日志](#92-审计日志)
  - [10. 与 OTTL 集成](#10-与-ottl-集成)
    - [10.1 动态下发 OTTL 规则](#101-动态下发-ottl-规则)
    - [10.2 A/B 测试不同 OTTL 策略](#102-ab-测试不同-ottl-策略)
  - [11. 参考文献](#11-参考文献)

---

## 1. 概述

**OPAMP (Open Agent Management Protocol)** 是 OpenTelemetry 社区定义的**反向控制通道**协议，用于管理分布式环境中的遥测数据收集器 (Agent/Collector)。

### 1.1 核心价值

| 功能 | 传统方式 | OPAMP 方式 |
|------|----------|-----------|
| **配置更新** | SSH + Ansible 滚动 | 灰度推送，4 秒生效 |
| **证书轮换** | 手动替换 + 重启 | 自动下发，无重启 |
| **版本升级** | 停机维护窗口 | 金丝雀发布，自动回滚 |
| **健康监控** | 外部探针 | Agent 主动心跳 |

### 1.2 与数据平面的关系

```text
┌──────────────────────────────────────────────────────────┐
│                   控制平面 (OPAMP)                        │
│  ┌──────────────┐       ┌──────────────┐                 │
│  │ Config Store │──────>│ OPAMP Server │                 │
│  └──────────────┘       └───────┬──────┘                 │
└────────────────────────────────┼─────────────────────────┘
                                  │ gRPC/WebSocket (TLS)
                ┌─────────────────┼─────────────────┐
                │                 │                 │
                ▼                 ▼                 ▼
      ┌──────────────┐  ┌──────────────┐  ┌──────────────┐
      │ OTel Agent 1 │  │ OTel Agent 2 │  │ OTel Agent N │
      └───────┬──────┘  └───────┬──────┘  └───────┬──────┘
              │                 │                 │
┌─────────────┴─────────────────┴─────────────────┴───────┐
│                 数据平面 (OTLP)                          │
│     Traces ────────> Gateway ────────> Backend           │
│     Metrics ───────> Gateway ────────> Backend           │
│     Logs ──────────> Gateway ────────> Backend           │
└──────────────────────────────────────────────────────────┘
```

---

## 2. 协议架构

### 2.1 设计目标

1. **供应商中立**: 协议层不绑定任何实现
2. **双向通信**: Agent 主动心跳 + Server 主动推送
3. **可扩展性**: 支持自定义 Capability
4. **安全第一**: mTLS + 签名验证 + 审计日志

### 2.2 消息模型

#### 2.2.1 Protobuf 定义

```protobuf
// opamp.proto (v1.0)
service OpAMPService {
    // WebSocket 长连接模式
    rpc AttachStream(stream AgentToServer) returns (stream ServerToAgent);
    
    // HTTP 轮询模式 (后备)
    rpc Poll(AgentToServer) returns (ServerToAgent);
}

message AgentToServer {
    string instance_uid = 1;           // Agent 唯一标识
    uint64 sequence_num = 2;           // 递增序列号
    AgentDescription agent_description = 3;
    uint64 capabilities = 4;           // 位掩码 (见 2.2.2)
    EffectiveConfig effective_config = 5;
    RemoteConfigStatus remote_config_status = 6;
    PackageStatuses package_statuses = 7;
    AgentHealth health = 8;
    ConnectionSettingsRequest connection_settings_request = 9;
    CustomCapabilities custom_capabilities = 10;
}

message ServerToAgent {
    string instance_uid = 1;
    ErrorResponse error_response = 2;
    AgentRemoteConfig remote_config = 3;
    ConnectionSettings connection_settings = 4;
    PackagesAvailable packages_available = 5;
    uint64 flags = 6;
    CustomMessage custom_message = 7;
}
```

#### 2.2.2 Capability 位掩码

```go
const (
    // Agent → Server 能力
    AgentCapability_ReportsStatus             = 1 << 0  // 0x01
    AgentCapability_AcceptsRemoteConfig       = 1 << 1  // 0x02
    AgentCapability_ReportsEffectiveConfig    = 1 << 2  // 0x04
    AgentCapability_AcceptsPackages           = 1 << 3  // 0x08
    AgentCapability_ReportsPackageStatuses    = 1 << 4  // 0x10
    AgentCapability_ReportsOwnTraces          = 1 << 5  // 0x20
    AgentCapability_ReportsOwnMetrics         = 1 << 6  // 0x40
    AgentCapability_ReportsOwnLogs            = 1 << 7  // 0x80
    AgentCapability_AcceptsOpAMPConnectionSettings = 1 << 8  // 0x100
    AgentCapability_AcceptsOtherConnectionSettings = 1 << 9  // 0x200
    AgentCapability_AcceptsRestartCommand     = 1 << 10 // 0x400
    AgentCapability_ReportsHealth             = 1 << 11 // 0x800
    AgentCapability_ReportsRemoteConfig       = 1 << 12 // 0x1000
)

// Server → Agent 标志
const (
    ServerFlag_ReportFullState = 1 << 0  // 要求 Agent 上报完整状态
)
```

### 2.3 传输层

#### 2.3.1 WebSocket (推荐)

```text
优势:
    - 长连接，延迟低 (< 50 ms)
    - 双向推送，无需轮询
    - 自动重连机制

URL 格式:
    wss://opamp-server.example.com/v1/opamp
    
握手:
    HTTP/1.1 101 Switching Protocols
    Upgrade: websocket
    Connection: Upgrade
    Sec-WebSocket-Protocol: opamp.v1
```

#### 2.3.2 HTTP/2 (后备)

```text
适用场景:
    - 网络环境不支持 WebSocket
    - 需要 HTTP 代理

轮询间隔:
    - 健康状态: 30 秒
    - 配置变更中: 5 秒
    - 错误恢复: 指数退避 (1s, 2s, 4s, ..., 最大 60s)
```

---

## 3. 核心消息规范

### 3.1 AgentToServer

#### 3.1.1 AgentDescription

```protobuf
message AgentDescription {
    repeated KeyValue identifying_attributes = 1;  // service.name, k8s.pod.name
    repeated KeyValue non_identifying_attributes = 2;  // host.arch, os.version
    
    // 示例
    // identifying_attributes: [
    //     {key: "service.name", value: "api-gateway"},
    //     {key: "k8s.pod.uid", value: "abc-123-def"}
    // ]
}
```

#### 3.1.2 EffectiveConfig

```protobuf
message EffectiveConfig {
    AgentConfigMap config_map = 1;  // 实际生效的配置
    
    // 配置来源追踪
    message ConfigSource {
        string source_id = 1;       // "remote", "local_file", "env_var"
        bytes hash = 2;             // SHA-256 哈希
    }
    ConfigSource config_source = 2;
}

message AgentConfigMap {
    map<string, AgentConfigFile> config_map = 1;
    
    // 多文件配置支持
    // config_map: {
    //     "config.yaml": { body: "receivers: ...", hash: 0xabcd },
    //     "sampling.yaml": { body: "processors: ...", hash: 0x1234 }
    // }
}
```

#### 3.1.3 AgentHealth

```protobuf
message AgentHealth {
    bool healthy = 1;
    uint64 start_timestamp_unix_nano = 2;
    string last_error = 3;
    
    // 组件级健康度
    repeated ComponentHealth component_health = 4;
}

message ComponentHealth {
    string component_name = 1;  // "receiver:otlp", "processor:batch"
    bool healthy = 2;
    uint64 status_timestamp = 3;
    string error_message = 4;
}
```

### 3.2 ServerToAgent

#### 3.2.1 AgentRemoteConfig

```protobuf
message AgentRemoteConfig {
    AgentConfigMap config = 1;
    bytes config_hash = 2;  // SHA-256 of canonical form
}

// 配置应用流程
// 1. Agent 收到 remote_config
// 2. 验证 config_hash
// 3. 应用配置 (热重载或重启)
// 4. 回报 RemoteConfigStatus
```

#### 3.2.2 PackagesAvailable

```protobuf
message PackagesAvailable {
    map<string, PackageAvailable> packages = 1;
    bool all_packages_hash = 2;  // 完整性校验
}

message PackageAvailable {
    PackageType type = 1;           // ADDON_PACKAGE, TOP_LEVEL_PACKAGE
    string version = 2;             // "1.19.0"
    DownloadableFile file = 3;
    bytes hash = 4;                 // 文件 SHA-256
    bytes signature = 5;            // Ed25519 签名
}

message DownloadableFile {
    string download_url = 1;        // "https://cdn.example.com/otel-agent-v1.19.0"
    bytes content_hash = 2;
    uint64 signature_algorithm = 3; // SIGNATURE_ALGORITHM_ED25519
}
```

### 3.3 心跳与连接管理

#### 3.3.1 心跳机制

```go
// Agent 侧伪代码
func (a *Agent) heartbeatLoop() {
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            // 发送心跳 (仅包含 instance_uid 和 sequence_num)
            msg := &AgentToServer{
                InstanceUid: a.uid,
                SequenceNum: atomic.AddUint64(&a.seqNum, 1),
            }
            a.stream.Send(msg)
            
        case <-a.ctx.Done():
            return
        }
    }
}
```

#### 3.3.2 断线重连

```text
重连策略:
    初始间隔: 1 秒
    最大间隔: 60 秒
    退避因子: 2
    抖动: ±10%

状态保持:
    - 本地缓存上次 config_hash
    - 重连后上报 effective_config
    - Server 比对差异，决定是否重新下发
```

---

## 4. 配置管理

### 4.1 远程配置下发

#### 4.1.1 配置格式 (YAML)

```yaml
# Server 下发的配置
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

processors:
  batch:
    timeout: 1s
    send_batch_size: 1024

exporters:
  otlp:
    endpoint: gateway.example.com:4317
    tls:
      insecure: false
      cert_file: /etc/certs/client.crt
      key_file: /etc/certs/client.key

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp]
```

#### 4.1.2 配置应用流程

```text
┌─────────┐                              ┌─────────┐
│ Server  │                              │  Agent  │
└────┬────┘                              └────┬────┘
     │                                        │
     │  ServerToAgent {                      │
     │    remote_config: {                   │
     │      config: "receivers: ...",        │
     │      hash: 0xabcd1234                 │
     │    }                                  │
     │  } ──────────────────────────────────>│
     │                                        │
     │                          验证 hash    │
     │                          应用配置     │
     │                          热重载      │
     │                                        │
     │  <─────────────────────────────────── │
     │  AgentToServer {                      │
     │    remote_config_status: {            │
     │      status: APPLIED,                 │
     │      effective_config_hash: 0xabcd1234│
     │    }                                  │
     │  }                                    │
     │                                        │
```

### 4.2 配置哈希与版本控制

#### 4.2.1 Canonical Hash 算法

```go
// 确保配置哈希可复现
func CanonicalHash(config map[string]string) []byte {
    // 1. 按键名排序
    keys := make([]string, 0, len(config))
    for k := range config {
        keys = append(keys, k)
    }
    sort.Strings(keys)
    
    // 2. 拼接为 Canonical Form
    var buf bytes.Buffer
    for _, k := range keys {
        buf.WriteString(k)
        buf.WriteByte('=')
        buf.WriteString(config[k])
        buf.WriteByte('\n')
    }
    
    // 3. SHA-256
    hash := sha256.Sum256(buf.Bytes())
    return hash[:]
}
```

### 4.3 多配置源合并

```go
// 配置优先级 (高到低)
// 1. OPAMP 远程配置
// 2. 环境变量
// 3. 本地配置文件

func (a *Agent) MergeConfig() *Config {
    base := LoadLocalConfig("config.yaml")
    env := LoadEnvOverrides()
    remote := a.effectiveRemoteConfig
    
    // 深度合并 (remote 优先)
    final := DeepMerge(base, env, remote)
    return final
}
```

---

## 5. 证书与密钥管理

### 5.1 mTLS 证书轮换

#### 5.1.1 证书下发

```protobuf
message ServerToAgent {
    TLSCertificate tls_certificate = 1;
}

message TLSCertificate {
    bytes public_key = 1;           // X.509 证书 (PEM)
    bytes private_key = 2;          // RSA/ECDSA 私钥 (PEM, 加密)
    bytes ca_certificate = 3;       // CA 证书链
    
    // 私钥加密 (使用 Agent 的预共享密钥)
    // private_key = AES-256-GCM(plaintext_key, preshared_secret)
}
```

#### 5.1.2 原子替换流程

```go
func (a *Agent) rotateCertificate(cert *TLSCertificate) error {
    // 1. 验证证书有效性
    x509Cert, err := x509.ParseCertificate(cert.PublicKey)
    if err != nil {
        return err
    }
    
    // 2. 解密私钥
    privateKey, err := a.decryptPrivateKey(cert.PrivateKey)
    if err != nil {
        return err
    }
    
    // 3. 写入临时文件
    tmpCert := "/etc/otel/certs/.new_cert.pem"
    tmpKey := "/etc/otel/certs/.new_key.pem"
    
    ioutil.WriteFile(tmpCert, cert.PublicKey, 0644)
    ioutil.WriteFile(tmpKey, privateKey, 0600)
    
    // 4. 原子替换 (Linux rename 是原子的)
    os.Rename(tmpCert, "/etc/otel/certs/client.crt")
    os.Rename(tmpKey, "/etc/otel/certs/client.key")
    
    // 5. 通知 TLS 连接重新加载
    a.tlsReloader.Reload()
    
    return nil
}
```

### 5.2 信任链验证

```go
func (a *Agent) verifyCertificateChain(cert, ca []byte) error {
    roots := x509.NewCertPool()
    roots.AppendCertsFromPEM(ca)
    
    leaf, _ := x509.ParseCertificate(cert)
    opts := x509.VerifyOptions{
        Roots:     roots,
        KeyUsages: []x509.ExtKeyUsage{x509.ExtKeyUsageClientAuth},
    }
    
    _, err := leaf.Verify(opts)
    return err
}
```

---

## 6. 包管理与升级

### 6.1 二进制分发

#### 6.1.1 包描述符

```json
{
  "name": "otel-collector",
  "version": "1.19.0",
  "type": "TOP_LEVEL_PACKAGE",
  "download_url": "https://cdn.example.com/otel-collector-v1.19.0-linux-amd64",
  "hash": "sha256:abcd1234...",
  "signature": "ed25519:cafe5678...",
  "public_key_id": "key-2025-01"
}
```

#### 6.1.2 下载与验证

```go
func (a *Agent) downloadPackage(pkg *PackageAvailable) error {
    // 1. 下载二进制
    resp, err := http.Get(pkg.File.DownloadUrl)
    if err != nil {
        return err
    }
    defer resp.Body.Close()
    
    data, _ := ioutil.ReadAll(resp.Body)
    
    // 2. 验证哈希
    actualHash := sha256.Sum256(data)
    if !bytes.Equal(actualHash[:], pkg.Hash) {
        return fmt.Errorf("hash mismatch")
    }
    
    // 3. 验证签名 (Ed25519)
    publicKey := a.getPublicKey(pkg.Signature.KeyId)
    if !ed25519.Verify(publicKey, pkg.Hash, pkg.Signature.Signature) {
        return fmt.Errorf("signature invalid")
    }
    
    // 4. 保存到临时目录
    tmpPath := "/tmp/otel-collector.new"
    ioutil.WriteFile(tmpPath, data, 0755)
    
    return nil
}
```

### 6.2 签名验证

#### 6.2.1 Ed25519 签名方案

```go
// 签名生成 (Server 侧)
func signPackage(binaryData []byte, privateKey ed25519.PrivateKey) []byte {
    hash := sha256.Sum256(binaryData)
    signature := ed25519.Sign(privateKey, hash[:])
    return signature
}

// 签名验证 (Agent 侧)
func verifyPackage(binaryData []byte, signature []byte, publicKey ed25519.PublicKey) bool {
    hash := sha256.Sum256(binaryData)
    return ed25519.Verify(publicKey, hash[:], signature)
}
```

### 6.3 原子升级机制

#### 6.3.1 Linux 原子替换

```bash
# 利用 Linux renameat2 的 RENAME_EXCHANGE 特性
# 实现零停机升级

# 1. 下载新版本到临时位置
/tmp/otel-collector.new

# 2. 原子交换 (内核级原子操作)
syscall(SYS_renameat2, 
        AT_FDCWD, "/usr/bin/otel-collector",
        AT_FDCWD, "/tmp/otel-collector.new",
        RENAME_EXCHANGE)

# 3. 发送 SIGHUP 触发热重载
kill -HUP $(pidof otel-collector)
```

#### 6.3.2 回滚机制

```go
func (a *Agent) upgradeWithRollback(newBinary string) error {
    // 1. 备份当前版本
    currentPath := "/usr/bin/otel-collector"
    backupPath := "/usr/bin/otel-collector.backup"
    os.Rename(currentPath, backupPath)
    
    // 2. 安装新版本
    os.Rename(newBinary, currentPath)
    
    // 3. 重启服务
    cmd := exec.Command("systemctl", "restart", "otel-collector")
    if err := cmd.Run(); err != nil {
        // 回滚
        os.Rename(backupPath, currentPath)
        exec.Command("systemctl", "restart", "otel-collector").Run()
        return err
    }
    
    // 4. 健康检查 (30 秒窗口)
    time.Sleep(30 * time.Second)
    if !a.isHealthy() {
        // 自动回滚
        os.Rename(backupPath, currentPath)
        exec.Command("systemctl", "restart", "otel-collector").Run()
        return fmt.Errorf("health check failed, rolled back")
    }
    
    return nil
}
```

---

## 7. 灰度发布与金丝雀

### 7.1 标签选择器

#### 7.1.1 语法

```yaml
# Server 配置
rollout:
  target_selector:
    match_labels:
      - key: "environment"
        value: "production"
      - key: "region"
        value: "us-east-1"
      - key: "version"
        value: "1.18.*"  # 支持通配符
    
    match_expressions:
      - key: "load"
        operator: "LessThan"  # LessThan, GreaterThan, In, NotIn
        value: "80"
```

#### 7.1.2 匹配逻辑

```go
func (s *Server) selectTargetAgents(selector *TargetSelector) []*Agent {
    var matched []*Agent
    
    for _, agent := range s.agents {
        if s.matchesLabels(agent, selector.MatchLabels) &&
           s.matchesExpressions(agent, selector.MatchExpressions) {
            matched = append(matched, agent)
        }
    }
    
    return matched
}
```

### 7.2 权重路由

#### 7.2.1 金丝雀发布策略

```yaml
rollout:
  stages:
    - name: "canary"
      weight: 5        # 5% 流量
      duration: "10m"
      
    - name: "stage1"
      weight: 25
      duration: "30m"
      
    - name: "stage2"
      weight: 50
      duration: "1h"
      
    - name: "full"
      weight: 100
```

#### 7.2.2 实现

```go
func (s *Server) selectCanaryAgents(agents []*Agent, weight int) []*Agent {
    // 基于一致性哈希选择固定的 weight% 的 Agent
    hashRing := consistent.New()
    for _, agent := range agents {
        hashRing.Add(agent.InstanceUid)
    }
    
    targetCount := len(agents) * weight / 100
    selected := make([]*Agent, 0, targetCount)
    
    for i := 0; i < targetCount; i++ {
        node, _ := hashRing.Get(fmt.Sprintf("canary-%d", i))
        for _, agent := range agents {
            if agent.InstanceUid == node {
                selected = append(selected, agent)
                break
            }
        }
    }
    
    return selected
}
```

### 7.3 自动回滚

#### 7.3.1 健康检查触发

```go
func (s *Server) monitorRollout(rollout *Rollout) {
    ticker := time.NewTicker(10 * time.Second)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            stats := s.collectAgentStats(rollout.TargetAgents)
            
            // 错误率 > 5% 触发回滚
            if stats.ErrorRate > 0.05 {
                s.rollback(rollout)
                return
            }
            
            // P99 延迟 > 基线 2 倍触发回滚
            if stats.P99Latency > rollout.BaselineP99*2 {
                s.rollback(rollout)
                return
            }
            
        case <-rollout.Done():
            return
        }
    }
}
```

---

## 8. 实现示例

### 8.1 Golang Agent 实现

```go
package main

import (
    "context"
    "github.com/open-telemetry/opamp-go/client"
    "github.com/open-telemetry/opamp-go/protobufs"
)

type MyAgent struct {
    opampClient client.OpAMPClient
    config      *Config
}

func (a *MyAgent) Start() error {
    // 1. 创建 OPAMP 客户端
    a.opampClient = client.NewWebSocket(nil)
    
    settings := client.StartSettings{
        OpAMPServerURL: "wss://opamp.example.com/v1/opamp",
        InstanceUid:    "agent-12345",
        Callbacks: client.CallbacksStruct{
            OnMessageFunc:         a.onMessage,
            OnConnectFunc:         a.onConnect,
            OnConnectFailedFunc:   a.onConnectFailed,
            OnErrorFunc:           a.onError,
            GetEffectiveConfigFunc: a.getEffectiveConfig,
            OnRemoteConfigFunc:    a.onRemoteConfig,
        },
        Capabilities: protobufs.AgentCapabilities_AgentCapabilities_AcceptsRemoteConfig |
                      protobufs.AgentCapabilities_AgentCapabilities_ReportsEffectiveConfig |
                      protobufs.AgentCapabilities_AgentCapabilities_AcceptsPackages,
    }
    
    // 2. 启动客户端
    err := a.opampClient.Start(context.Background(), settings)
    if err != nil {
        return err
    }
    
    return nil
}

func (a *MyAgent) onRemoteConfig(config *protobufs.AgentRemoteConfig) error {
    // 3. 处理远程配置
    newConfig, err := ParseConfig(config.Config.ConfigMap)
    if err != nil {
        return err
    }
    
    // 4. 热重载配置
    a.config = newConfig
    a.reloadPipelines()
    
    // 5. 回报成功
    a.opampClient.SetRemoteConfigStatus(&protobufs.RemoteConfigStatus{
        Status:              protobufs.RemoteConfigStatuses_RemoteConfigStatuses_APPLIED,
        EffectiveConfigHash: config.ConfigHash,
    })
    
    return nil
}
```

### 8.2 控制平面实现

```go
package main

import (
    "github.com/open-telemetry/opamp-go/server"
    "github.com/open-telemetry/opamp-go/protobufs"
)

type ControlPlane struct {
    server server.OpAMPServer
    agents map[string]*AgentInfo
}

func (cp *ControlPlane) Start() error {
    settings := server.StartSettings{
        ListenEndpoint: "0.0.0.0:4320",
        Callbacks: server.CallbacksStruct{
            OnConnectedFunc:    cp.onAgentConnected,
            OnMessageFunc:      cp.onMessage,
        },
    }
    
    cp.server = server.New(nil)
    return cp.server.Start(settings)
}

func (cp *ControlPlane) onAgentConnected(conn server.Connection) {
    // Agent 连接时
    instanceUID := conn.InstanceUid()
    
    // 推送配置
    newConfig := cp.generateConfigForAgent(instanceUID)
    conn.Send(&protobufs.ServerToAgent{
        RemoteConfig: newConfig,
    })
}

func (cp *ControlPlane) PushConfigToAllAgents(config *protobufs.AgentRemoteConfig) {
    for uid, info := range cp.agents {
        info.connection.Send(&protobufs.ServerToAgent{
            RemoteConfig: config,
        })
    }
}
```

---

## 9. 安全模型

### 9.1 威胁模型

| 威胁 | 缓解措施 |
|------|----------|
| **中间人攻击** | mTLS 双向认证 |
| **配置注入** | Config Hash 验证 |
| **二进制篡改** | Ed25519 签名 + Hash 校验 |
| **重放攻击** | Sequence Number 单调递增 |
| **权限提升** | RBAC + 最小权限原则 |

### 9.2 审计日志

```go
type AuditLog struct {
    Timestamp   time.Time
    AgentUID    string
    Action      string  // "config_applied", "package_installed", "cert_rotated"
    OldValue    string
    NewValue    string
    Success     bool
    ErrorMsg    string
}

func (cp *ControlPlane) logAudit(log *AuditLog) {
    // 1. 写入持久化存储
    cp.auditDB.Insert(log)
    
    // 2. 发送到 SIEM 系统
    cp.siemExporter.Send(log)
    
    // 3. 如果是高危操作,发送告警
    if log.Action == "cert_rotated" && !log.Success {
        cp.alertManager.Send(Alert{
            Severity: "CRITICAL",
            Message:  fmt.Sprintf("Cert rotation failed for %s", log.AgentUID),
        })
    }
}
```

---

## 10. 与 OTTL 集成

### 10.1 动态下发 OTTL 规则

```yaml
# Server 推送的配置
processors:
  transform:
    trace_statements:
      - context: span
        statements:
          # OTTL 规则 (由 OPAMP 动态下发)
          - set(attributes["tenant"], resource.attributes["service.namespace"])
          - delete_key(attributes, "internal.debug.info") where attributes["env"] == "prod"
          - set(status.message, "timeout") where duration > 3000
```

### 10.2 A/B 测试不同 OTTL 策略

```go
// 金丝雀组使用新 OTTL 规则
canaryConfig := &Config{
    Processors: map[string]interface{}{
        "transform": map[string]interface{}{
            "trace_statements": []string{
                `set(attributes["version"], "v2")`,
                `drop() where attributes["noise"] == "true"`,  // 新规则
            },
        },
    },
}

cp.PushConfigToAgents(canaryAgents, canaryConfig)

// 30 分钟后比对效果
time.Sleep(30 * time.Minute)
if canaryMetrics.DroppedSpans < baselineMetrics.DroppedSpans*0.9 {
    // 新规则有效,全量推送
    cp.PushConfigToAllAgents(canaryConfig)
}
```

---

## 11. 参考文献

1. **OpenTelemetry OPAMP Specification** (2025). <https://github.com/open-telemetry/opamp-spec>
2. **OPAMP Protocol Buffer Definitions** (v1.0). <https://github.com/open-telemetry/opamp-go>
3. **Ed25519 Signature Scheme** (RFC 8032). <https://tools.ietf.org/html/rfc8032>
4. **Kubernetes Admission Control** (Label Selector). <https://kubernetes.io/docs/concepts/overview/working-with-objects/labels/>

---

**下一篇**: [OTTL 转换语言深度解析](./06-ottl-transformation-language.md)
