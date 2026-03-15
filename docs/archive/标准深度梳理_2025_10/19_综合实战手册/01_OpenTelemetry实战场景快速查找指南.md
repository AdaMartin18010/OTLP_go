# OpenTelemetry实战场景快速查找指南

> **目标**: 根据实际场景快速找到对应的配置、代码和最佳实践  
> **更新日期**: 2025年10月8日  
> **适用人群**: 所有OpenTelemetry用户

---

## 目录

- [OpenTelemetry实战场景快速查找指南](#opentelemetry实战场景快速查找指南)
  - [目录](#目录)
  - [🚀 快速导航](#-快速导航)
    - [我想](#我想)
  - [1. 按开发语言查找](#1-按开发语言查找)
    - [1.1 Go语言](#11-go语言)
    - [1.2 Python语言](#12-python语言)
    - [1.3 Java语言](#13-java语言)
    - [1.4 JavaScript/TypeScript](#14-javascripttypescript)
  - [2. 按应用类型查找](#2-按应用类型查找)
    - [2.1 Web应用监控](#21-web应用监控)
    - [2.2 微服务追踪](#22-微服务追踪)
    - [2.3 数据库监控](#23-数据库监控)
    - [2.4 消息队列监控](#24-消息队列监控)
    - [2.5 FaaS/Serverless监控](#25-faasserverless监控)
    - [2.6 日志聚合](#26-日志聚合)
    - [2.7 移动端监控](#27-移动端监控)
    - [2.8 IoT设备监控](#28-iot设备监控)
  - [3. 按技术栈查找](#3-按技术栈查找)
    - [3.1 容器与编排](#31-容器与编排)
    - [3.2 云服务商](#32-云服务商)
    - [3.3 监控后端](#33-监控后端)
  - [4. 按问题类型查找](#4-按问题类型查找)
    - [4.1 性能问题](#41-性能问题)
    - [4.2 连接问题](#42-连接问题)
    - [4.3 数据丢失](#43-数据丢失)
    - [4.4 数据质量](#44-数据质量)
    - [4.5 集成问题](#45-集成问题)
    - [4.6 安全与合规](#46-安全与合规)
  - [5. 按部署环境查找](#5-按部署环境查找)
    - [5.1 本地开发](#51-本地开发)
    - [5.2 Kubernetes生产](#52-kubernetes生产)
    - [5.3 AWS云平台](#53-aws云平台)
    - [5.4 Azure云平台](#54-azure云平台)
    - [5.5 GCP云平台](#55-gcp云平台)
  - [6. 按行业场景查找](#6-按行业场景查找)
    - [6.1 电商零售](#61-电商零售)
    - [6.2 金融行业](#62-金融行业)
    - [6.3 制造业](#63-制造业)
    - [6.4 医疗健康](#64-医疗健康)
    - [6.5 物流运输](#65-物流运输)
    - [6.6 游戏行业](#66-游戏行业)
  - [7. 场景决策树](#7-场景决策树)
    - [我该使用哪种采样策略?](#我该使用哪种采样策略)
    - [我该选择哪种Collector部署模式?](#我该选择哪种collector部署模式)
    - [我该使用哪种传输协议?](#我该使用哪种传输协议)
  - [8. 快速参考表](#8-快速参考表)
    - [8.1 常用端口](#81-常用端口)
    - [8.2 常用环境变量](#82-常用环境变量)
    - [8.3 核心文档索引](#83-核心文档索引)
    - [8.4 学习路径建议](#84-学习路径建议)

---

## 🚀 快速导航

### 我想

```text
📊 监控我的应用性能
   → 章节 2.1 Web应用监控

🐛 追踪分布式调用链路
   → 章节 2.2 微服务追踪

📝 采集应用日志
   → 章节 2.6 日志聚合

⚡ 优化追踪性能
   → 章节 4.3 性能优化

🔒 确保数据安全
   → 章节 4.6 安全与合规

☁️ 部署到云平台
   → 章节 5 按部署环境查找

🏢 实现行业方案
   → 章节 6 按行业场景查找
```

---

## 1. 按开发语言查找

### 1.1 Go语言

**适用场景**: Go微服务、API服务、gRPC服务

| 场景 | 文档位置 | 核心组件 |
|------|----------|----------|
| HTTP服务追踪 | `02_Semantic_Conventions/02_追踪属性/01_HTTP.md` | `otelhttp.NewHandler` |
| gRPC服务追踪 | `02_Semantic_Conventions/02_追踪属性/02_gRPC.md` | `otelgrpc.UnaryServerInterceptor` |
| 数据库操作追踪 | `02_Semantic_Conventions/04_数据库属性/01_SQL数据库属性详解.md` | `otelsql` |
| Redis操作追踪 | `02_Semantic_Conventions/03_消息队列属性/03_Redis.md` | `go-redis/v9` with OTEL |
| Kafka生产消费 | `02_Semantic_Conventions/03_消息队列属性/01_Kafka.md` | `otelkafka` |
| 完整微服务案例 | `06_实战案例/01_微服务追踪实战.md` | 全栈示例 |

**快速开始**:

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// 初始化
func initTracer() *sdktrace.TracerProvider {
    exporter, _ := otlptracegrpc.New(context.Background())
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
    )
    otel.SetTracerProvider(tp)
    return tp
}
```

### 1.2 Python语言

**适用场景**: Django/Flask/FastAPI应用、数据处理、AI/ML

| 场景 | 文档位置 | 核心组件 |
|------|----------|----------|
| Flask应用追踪 | `02_Semantic_Conventions/02_追踪属性/01_HTTP.md` | `FlaskInstrumentor` |
| FastAPI追踪 | `06_实战案例/01_微服务追踪实战.md` | `FastAPIInstrumentor` |
| Django追踪 | `02_Semantic_Conventions/02_追踪属性/01_HTTP.md` | `DjangoInstrumentor` |
| SQLAlchemy追踪 | `02_Semantic_Conventions/04_数据库属性/01_SQL数据库属性详解.md` | `SQLAlchemyInstrumentor` |
| Celery任务追踪 | `02_Semantic_Conventions/03_消息队列属性/04_RabbitMQ.md` | `CeleryInstrumentor` |

**快速开始**:

```python
from opentelemetry import trace
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor

# 初始化
provider = TracerProvider()
processor = BatchSpanProcessor(OTLPSpanExporter())
provider.add_span_processor(processor)
trace.set_tracer_provider(provider)
```

### 1.3 Java语言

**适用场景**: Spring Boot、企业应用、Android

| 场景 | 文档位置 | 核心组件 |
|------|----------|----------|
| Spring Boot追踪 | `06_实战案例/01_微服务追踪实战.md` | `spring-boot-starter-otel` |
| JDBC追踪 | `02_Semantic_Conventions/04_数据库属性/01_SQL数据库属性详解.md` | `opentelemetry-jdbc` |
| Servlet追踪 | `02_Semantic_Conventions/02_追踪属性/01_HTTP.md` | Auto-instrumentation |
| Kafka追踪 | `02_Semantic_Conventions/03_消息队列属性/01_Kafka.md` | `opentelemetry-kafka` |
| Android应用 | `12_移动端可观测性/01_移动端可观测性概述与实践.md` | Android SDK |

**快速开始** (Java Agent):

```bash
java -javaagent:opentelemetry-javaagent.jar \
     -Dotel.service.name=my-service \
     -Dotel.exporter.otlp.endpoint=http://localhost:4317 \
     -jar myapp.jar
```

### 1.4 JavaScript/TypeScript

**适用场景**: Node.js服务、前端应用、React/Vue

| 场景 | 文档位置 | 核心组件 |
|------|----------|----------|
| Express.js追踪 | `06_实战案例/01_微服务追踪实战.md` | `@opentelemetry/instrumentation-express` |
| Nest.js追踪 | `02_Semantic_Conventions/02_追踪属性/01_HTTP.md` | Auto-instrumentation |
| 前端追踪 | `12_移动端可观测性/01_移动端可观测性概述与实践.md` | `@opentelemetry/web` |
| MongoDB追踪 | `02_Semantic_Conventions/04_数据库属性/02_MongoDB.md` | `@opentelemetry/instrumentation-mongodb` |

---

## 2. 按应用类型查找

### 2.1 Web应用监控

**我的应用是**: RESTful API、Web服务、SPA

**关键需求**:

- 追踪HTTP请求响应
- 监控API延迟
- 识别慢接口
- 追踪错误率

**文档路径**:

```text
1. 基础概念: 01_OTLP核心协议/01_协议概述.md
2. HTTP语义约定: 02_Semantic_Conventions/02_追踪属性/01_HTTP.md
3. SDK集成: 04_核心组件/01_SDK概述.md
4. 实战案例: 06_实战案例/01_微服务追踪实战.md
5. 性能优化: 05_采样与性能/02_性能优化实践.md
```

**快速配置**:

```yaml
# SDK配置
service_name: web-api
exporters:
  otlp:
    endpoint: http://collector:4317

# 采样策略
sampling:
  type: probabilistic
  probability: 0.1  # 10%采样率
```

### 2.2 微服务追踪

**我的应用是**: 分布式微服务架构、服务网格

**关键需求**:

- 跨服务调用追踪
- 服务依赖分析
- 分布式事务监控
- 调用链路可视化

**文档路径**:

```text
1. Context传播: 04_核心组件/04_Context_Propagation详解.md
2. 微服务实战: 06_实战案例/01_微服务追踪实战.md
3. 服务发现: 10_云平台集成/01_AWS集成指南.md (Kubernetes章节)
4. 性能优化: 06_实战案例/04_生产环境最佳实践.md
```

**核心配置**:

```go
// Context传播
propagator := propagation.NewCompositeTextMapPropagator(
    propagation.TraceContext{},
    propagation.Baggage{},
)
otel.SetTextMapPropagator(propagator)

// HTTP客户端自动传播
client := &http.Client{
    Transport: otelhttp.NewTransport(http.DefaultTransport),
}
```

### 2.3 数据库监控

**我的应用使用**: SQL数据库、NoSQL、缓存

**关键需求**:

- 慢查询识别
- 数据库调用追踪
- 连接池监控
- 查询语句脱敏

**文档路径**:

```text
1. SQL数据库: 02_Semantic_Conventions/04_数据库属性/01_SQL数据库属性详解.md
2. MongoDB: 02_Semantic_Conventions/04_数据库属性/02_MongoDB.md
3. Redis: 02_Semantic_Conventions/03_消息队列属性/03_Redis.md
4. Cassandra: 02_Semantic_Conventions/04_数据库属性/03_Cassandra.md
```

### 2.4 消息队列监控

**我的应用使用**: Kafka、RabbitMQ、NATS、SQS

**关键需求**:

- 消息生产消费追踪
- 消息延迟监控
- 死信队列追踪
- 消费者性能

**文档路径**:

```text
1. Kafka: 02_Semantic_Conventions/03_消息队列属性/01_Kafka.md
2. RabbitMQ: 02_Semantic_Conventions/03_消息队列属性/04_RabbitMQ.md
3. NATS: 02_Semantic_Conventions/03_消息队列属性/02_NATS.md
4. AWS SQS/SNS: 02_Semantic_Conventions/03_消息队列属性/06_AWS_SQS_SNS.md
```

### 2.5 FaaS/Serverless监控

**我的应用使用**: AWS Lambda、Azure Functions、Cloud Functions

**关键需求**:

- 函数冷启动追踪
- 函数执行时间
- 跨函数调用链
- 成本分析

**文档路径**:

```text
1. AWS Lambda: 02_Semantic_Conventions/06_FaaS属性/01_AWS_Lambda.md
2. Azure Functions: 02_Semantic_Conventions/06_FaaS属性/02_Azure_Functions.md
3. Google Cloud Functions: 02_Semantic_Conventions/06_FaaS属性/03_Google_Cloud_Functions.md
4. 云平台集成: 10_云平台集成/01_AWS集成指南.md
```

### 2.6 日志聚合

**我的需求**: 结构化日志、日志关联追踪、日志搜索

**关键需求**:

- 日志与Trace关联
- 结构化日志采集
- 日志严重性管理
- 大规模日志处理

**文档路径**:

```text
1. Logs数据模型: 03_数据模型/03_Logs数据模型/02_Logs字段与严重性详解.md
2. Filelog Receiver: 04_核心组件/04_Collector_Receiver配置详解.md
3. 日志处理: 04_核心组件/03_Collector_Processor配置详解.md
```

### 2.7 移动端监控

**我的应用是**: iOS、Android App

**关键需求**:

- 崩溃追踪
- 网络请求监控
- 性能指标(FPS、内存)
- 用户会话追踪
- 离线数据缓存

**文档路径**:

```text
1. 移动端完整指南: 12_移动端可观测性/01_移动端可观测性概述与实践.md
```

### 2.8 IoT设备监控

**我的应用是**: 物联网设备、边缘设备、传感器

**关键需求**:

- 轻量级追踪
- 间歇性连接处理
- 资源受限优化
- 边缘数据聚合

**文档路径**:

```text
1. IoT完整指南: 13_IoT可观测性/01_IoT可观测性概述与实践.md
```

---

## 3. 按技术栈查找

### 3.1 容器与编排

| 技术 | 文档位置 | 关键配置 |
|------|----------|----------|
| **Docker** | `04_核心组件/06_Collector生产环境完整配置示例.md` (Docker Compose章节) | 容器化部署 |
| **Kubernetes** | `04_核心组件/06_Collector生产环境完整配置示例.md` (K8s章节) | DaemonSet/Deployment |
| **Helm** | `10_云平台集成/01_AWS集成指南.md` | Chart配置 |
| **Istio/服务网格** | `06_实战案例/04_生产环境最佳实践.md` | Sidecar注入 |

### 3.2 云服务商

| 云平台 | 文档位置 | 特色功能 |
|--------|----------|----------|
| **AWS** | `10_云平台集成/01_AWS集成指南.md` | ECS/EKS/Lambda/X-Ray |
| **Azure** | `10_云平台集成/03_Azure集成指南.md` | AKS/App Service/Monitor |
| **Google Cloud** | `10_云平台集成/02_GCP集成指南.md` | GKE/Cloud Run/Trace |
| **多云对比** | `10_云平台集成/04_多云平台深度对比分析.md` | 架构对比 |

### 3.3 监控后端

| 后端系统 | 文档位置 | Exporter配置 |
|----------|----------|--------------|
| **Jaeger** | `04_核心组件/05_Collector_Exporter配置详解.md` | `jaeger` exporter |
| **Prometheus** | `04_核心组件/05_Collector_Exporter配置详解.md` | `prometheus` exporter |
| **Elasticsearch** | `04_核心组件/05_Collector_Exporter配置详解.md` | `elasticsearch` exporter |
| **AWS X-Ray** | `10_云平台集成/01_AWS集成指南.md` | `awsxray` exporter |
| **Azure Monitor** | `10_云平台集成/03_Azure集成指南.md` | `azuremonitor` exporter |

---

## 4. 按问题类型查找

### 4.1 性能问题

**症状**: 响应慢、超时、资源不足

| 问题 | 文档位置 | 解决方案 |
|------|----------|----------|
| 识别慢接口 | `05_采样与性能/01_采样策略.md` | 尾部采样 |
| 数据库慢查询 | `02_Semantic_Conventions/04_数据库属性/01_SQL数据库属性详解.md` | 慢查询追踪 |
| 内存占用高 | `16_故障排查手册/01_OpenTelemetry故障排查完整手册.md` | Memory Limiter |
| Collector性能 | `14_性能与基准测试/01_OpenTelemetry性能基准测试.md` | 性能调优 |
| 采样优化 | `05_采样与性能/01_采样策略.md` | 采样策略 |

### 4.2 连接问题

**症状**: 连接失败、超时、TLS错误

| 问题 | 文档位置 | 解决方案 |
|------|----------|----------|
| TLS配置 | `15_安全加固指南/01_OpenTelemetry安全加固完整指南.md` | TLS/mTLS配置 |
| 认证失败 | `15_安全加固指南/01_OpenTelemetry安全加固完整指南.md` | 认证配置 |
| 网络超时 | `16_故障排查手册/01_OpenTelemetry故障排查完整手册.md` | 超时调优 |
| 负载均衡 | `04_核心组件/06_Collector生产环境完整配置示例.md` (HA章节) | 集群配置 |

### 4.3 数据丢失

**症状**: 数据不完整、trace断裂、指标缺失

| 问题 | 文档位置 | 解决方案 |
|------|----------|----------|
| Context丢失 | `04_核心组件/04_Context_Propagation详解.md` | Propagator配置 |
| 采样过度 | `05_采样与性能/01_采样策略.md` | 采样率调整 |
| Exporter失败 | `16_故障排查手册/01_OpenTelemetry故障排查完整手册.md` | 重试与队列 |
| Pipeline配置错误 | `04_核心组件/06_Collector生产环境完整配置示例.md` | Pipeline配置 |

### 4.4 数据质量

**症状**: 属性缺失、命名不规范、数据混乱

| 问题 | 文档位置 | 解决方案 |
|------|----------|----------|
| 属性规范化 | `02_Semantic_Conventions/00_语义约定总览.md` | Semantic Conventions |
| 资源属性 | `02_Semantic_Conventions/04_资源属性/01_通用资源属性.md` | Resource配置 |
| 数据转换 | `04_核心组件/03_Collector_Processor配置详解.md` | Transform处理器 |
| 数据脱敏 | `15_安全加固指南/01_OpenTelemetry安全加固完整指南.md` | 敏感数据处理 |

### 4.5 集成问题

**症状**: SDK集成失败、框架不兼容、自动仪表化问题

| 问题 | 文档位置 | 解决方案 |
|------|----------|----------|
| SDK初始化 | `04_核心组件/01_SDK概述.md` | SDK配置 |
| 自动仪表化 | `06_实战案例/03_eBPF自动追踪.md` | eBPF/Agent |
| 框架兼容性 | `17_最佳实践清单/01_OpenTelemetry最佳实践完整清单.md` | 兼容性检查 |

### 4.6 安全与合规

**症状**: 数据泄露风险、合规要求、认证问题

| 问题 | 文档位置 | 解决方案 |
|------|----------|----------|
| 数据脱敏 | `07_安全与合规/02_数据隐私合规.md` | PII处理 |
| GDPR合规 | `07_安全与合规/02_数据隐私合规.md` | GDPR指南 |
| PCI-DSS | `07_安全与合规/02_数据隐私合规.md` | 支付卡合规 |
| HIPAA | `14_更多行业案例/01_多行业可观测性案例集.md` (医疗章节) | 医疗合规 |

---

## 5. 按部署环境查找

### 5.1 本地开发

**场景**: 开发测试、本地调试

```text
1. 快速开始: 快速开始指南.md
2. Docker部署: 04_核心组件/06_Collector生产环境完整配置示例.md (Docker Compose)
3. 调试技巧: 16_故障排查手册/01_OpenTelemetry故障排查完整手册.md
```

**快速启动**:

```bash
# Docker Compose快速启动
docker-compose -f docker-compose.yml up -d
```

### 5.2 Kubernetes生产

**场景**: K8s集群、生产环境

```text
1. K8s部署: 04_核心组件/06_Collector生产环境完整配置示例.md (K8s章节)
2. Helm Chart: 10_云平台集成/01_AWS集成指南.md
3. HA配置: 04_核心组件/06_Collector生产环境完整配置示例.md (HA章节)
4. 最佳实践: 06_实战案例/04_生产环境最佳实践.md
```

### 5.3 AWS云平台

**场景**: ECS、EKS、Lambda

```text
1. AWS集成: 10_云平台集成/01_AWS集成指南.md
2. Lambda监控: 02_Semantic_Conventions/06_FaaS属性/01_AWS_Lambda.md
3. X-Ray集成: 10_云平台集成/01_AWS集成指南.md
```

### 5.4 Azure云平台

**场景**: AKS、App Service、Functions

```text
1. Azure集成: 10_云平台集成/03_Azure集成指南.md
2. Azure Functions: 02_Semantic_Conventions/06_FaaS属性/02_Azure_Functions.md
3. Azure Monitor: 10_云平台集成/03_Azure集成指南.md
```

### 5.5 GCP云平台

**场景**: GKE、Cloud Run、Cloud Functions

```text
1. GCP集成: 10_云平台集成/02_GCP集成指南.md
2. Cloud Functions: 02_Semantic_Conventions/06_FaaS属性/03_Google_Cloud_Functions.md
3. Cloud Trace: 10_云平台集成/02_GCP集成指南.md
```

---

## 6. 按行业场景查找

### 6.1 电商零售

**关键需求**: 订单追踪、支付监控、库存同步、用户行为

```text
1. 完整案例: 06_实战案例/05_大规模电商系统可观测性实战.md
2. 分布式事务: 06_实战案例/02_分布式事务追踪.md
3. 最佳实践: 17_最佳实践清单/01_OpenTelemetry最佳实践完整清单.md
```

### 6.2 金融行业

**关键需求**: 交易追踪、合规审计、实时风控

```text
1. 金融案例: 06_实战案例/06_金融行业核心系统可观测性实战.md
2. 安全合规: 07_安全与合规/02_数据隐私合规.md (PCI-DSS章节)
3. 审计日志: 03_数据模型/03_Logs数据模型/02_Logs字段与严重性详解.md
```

### 6.3 制造业

**关键需求**: IoT设备监控、生产线追踪、设备预测维护

```text
1. 制造案例: 06_实战案例/07_智能制造可观测性实战.md
2. IoT监控: 13_IoT可观测性/01_IoT可观测性概述与实践.md
3. MQTT集成: 02_Semantic_Conventions/03_消息队列属性/07_MQTT.md
```

### 6.4 医疗健康

**关键需求**: HIPAA合规、患者数据保护、医疗设备监控

```text
1. 医疗案例: 14_更多行业案例/01_多行业可观测性案例集.md (医疗章节)
2. HIPAA合规: 07_安全与合规/02_数据隐私合规.md (HIPAA章节)
3. 数据脱敏: 15_安全加固指南/01_OpenTelemetry安全加固完整指南.md
```

### 6.5 物流运输

**关键需求**: 货物追踪、路径优化、实时调度

```text
1. 物流案例: 06_实战案例/08_智慧物流可观测性实战.md
2. 地理位置追踪: 02_Semantic_Conventions/02_追踪属性/05_通用Span属性.md
3. 移动端监控: 12_移动端可观测性/01_移动端可观测性概述与实践.md
```

### 6.6 游戏行业

**关键需求**: 玩家行为追踪、游戏服务器监控、资产服务

```text
1. 游戏案例: 14_更多行业案例/01_多行业可观测性案例集.md (游戏章节)
2. 实时监控: 06_实战案例/04_生产环境最佳实践.md
3. 高并发优化: 14_性能与基准测试/01_OpenTelemetry性能基准测试.md
```

---

## 7. 场景决策树

### 我该使用哪种采样策略?

```text
开始
  │
  ├─ 是否需要追踪所有错误?
  │   ├─ 是 → 使用 Tail Sampling (错误保留)
  │   └─ 否 → 继续
  │
  ├─ 流量是否很大 (>10k traces/s)?
  │   ├─ 是 → 使用概率采样 (1-5%)
  │   └─ 否 → 继续
  │
  ├─ 是否需要追踪慢请求?
  │   ├─ 是 → 使用 Tail Sampling (延迟策略)
  │   └─ 否 → 继续
  │
  └─ 默认 → 使用 ParentBased + AlwaysOn (开发)
            或 ParentBased + TraceIdRatioBased(10%) (生产)

📖 详见: 05_采样与性能/01_采样策略.md
```

### 我该选择哪种Collector部署模式?

```text
开始
  │
  ├─ 规模: 小型应用 (<100 services)
  │   └─ 单节点Collector
  │       📖 04_核心组件/06_Collector生产环境完整配置示例.md (单节点)
  │
  ├─ 规模: 中型应用 (100-500 services)
  │   └─ Gateway + Agent模式
  │       📖 04_核心组件/06_Collector生产环境完整配置示例.md (HA集群)
  │
  └─ 规模: 大型应用 (>500 services)
      └─ Gateway + Kafka + Agent
          📖 04_核心组件/06_Collector生产环境完整配置示例.md (HA集群)
```

### 我该使用哪种传输协议?

```text
开始
  │
  ├─ 性能要求: 高吞吐、低延迟
  │   └─ 使用 gRPC
  │       📖 01_OTLP核心协议/02_传输层_gRPC.md
  │
  ├─ 兼容性: 浏览器、旧系统
  │   └─ 使用 HTTP/JSON
  │       📖 01_OTLP核心协议/03_传输层_HTTP.md
  │
  └─ 云环境: Serverless/Lambda
      └─ 使用 HTTP (更简单)
          📖 02_Semantic_Conventions/06_FaaS属性/01_AWS_Lambda.md
```

---

## 8. 快速参考表

### 8.1 常用端口

| 组件 | 端口 | 协议 | 用途 |
|------|------|------|------|
| Collector | 4317 | gRPC | OTLP接收 |
| Collector | 4318 | HTTP | OTLP接收 |
| Collector | 8888 | HTTP | Prometheus指标 |
| Collector | 13133 | HTTP | 健康检查 |
| Collector | 55679 | HTTP | zPages |
| Jaeger | 16686 | HTTP | UI |
| Jaeger | 14250 | gRPC | 接收 |
| Prometheus | 9090 | HTTP | UI + API |

### 8.2 常用环境变量

| 环境变量 | 描述 | 示例 |
|----------|------|------|
| `OTEL_SERVICE_NAME` | 服务名称 | `my-service` |
| `OTEL_EXPORTER_OTLP_ENDPOINT` | Collector地址 | `http://localhost:4317` |
| `OTEL_TRACES_SAMPLER` | 采样器类型 | `traceidratio` |
| `OTEL_TRACES_SAMPLER_ARG` | 采样率 | `0.1` (10%) |
| `OTEL_RESOURCE_ATTRIBUTES` | 资源属性 | `env=prod,region=us-east-1` |

### 8.3 核心文档索引

| 主题 | 文档路径 | 页数估算 |
|------|----------|----------|
| 协议概述 | `01_OTLP核心协议/01_协议概述.md` | ~800行 |
| 语义约定 | `02_Semantic_Conventions/00_语义约定总览.md` | ~1,000行 |
| SDK概述 | `04_核心组件/01_SDK概述.md` | ~1,000行 |
| Collector配置 | `04_核心组件/06_Collector生产环境完整配置示例.md` | ~2,800行 |
| 微服务实战 | `06_实战案例/01_微服务追踪实战.md` | ~1,200行 |
| 故障排查 | `16_故障排查手册/01_OpenTelemetry故障排查完整手册.md` | ~2,500行 |
| 最佳实践 | `17_最佳实践清单/01_OpenTelemetry最佳实践完整清单.md` | ~3,000行 |

### 8.4 学习路径建议

| 角色 | 时间 | 推荐文档 |
|------|------|----------|
| **新手** | 1-2天 | 快速开始 → 协议概述 → HTTP追踪 → 微服务实战 |
| **开发者** | 1周 | SDK概述 → 语义约定 → 数据模型 → 实战案例 |
| **架构师** | 2周 | 完整技术栈 → Collector配置 → 云平台集成 → 最佳实践 |
| **SRE/运维** | 1周 | Collector架构 → HA部署 → 故障排查 → 性能优化 |

---

**文档版本**: v1.0  
**最后更新**: 2025年10月8日  
**维护者**: OTLP深度梳理项目组

**📖 快速开始**: 从 [快速开始指南](../快速开始指南.md) 开始你的OpenTelemetry之旅！
