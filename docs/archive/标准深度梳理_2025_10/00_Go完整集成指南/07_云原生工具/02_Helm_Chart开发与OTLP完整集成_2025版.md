# Helm Chart 开发与 OTLP 完整集成（2025版）

> **Helm 版本**: v3.13+  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **Kubernetes**: v1.28+  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [Helm Chart 开发与 OTLP 完整集成（2025版）](#helm-chart-开发与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. Helm 概述](#1-helm-概述)
    - [1.1 为什么选择 Helm](#11-为什么选择-helm)
    - [1.2 Helm 架构](#12-helm-架构)
    - [1.3 Chart 结构](#13-chart-结构)
  - [2. 快速开始](#2-快速开始)
    - [2.1 安装 Helm](#21-安装-helm)
    - [2.2 创建 Chart](#22-创建-chart)
  - [3. Chart 开发](#3-chart-开发)
    - [3.1 Chart.yaml](#31-chartyaml)
    - [3.2 values.yaml](#32-valuesyaml)
    - [3.3 Deployment 模板](#33-deployment-模板)
    - [3.4 \_helpers.tpl（模板辅助函数）](#34-_helperstpl模板辅助函数)
  - [4. OTLP 集成](#4-otlp-集成)
    - [4.1 ConfigMap 配置](#41-configmap-配置)
    - [4.2 ServiceMonitor](#42-servicemonitor)
  - [5. 完整示例](#5-完整示例)
    - [5.1 多环境部署](#51-多环境部署)
    - [5.2 升级和回滚](#52-升级和回滚)
  - [6. 最佳实践](#6-最佳实践)
    - [6.1 Chart 测试](#61-chart-测试)
    - [6.2 Chart 打包和发布](#62-chart-打包和发布)
    - [6.3 依赖管理](#63-依赖管理)
  - [7. 发布与维护](#7-发布与维护)
    - [7.1 版本管理](#71-版本管理)
    - [7.2 文档编写](#72-文档编写)
  - [8. 总结](#8-总结)
    - [8.1 优势与劣势](#81-优势与劣势)

---

## 1. Helm 概述

### 1.1 为什么选择 Helm

**Helm** 是 Kubernetes 的包管理器，CNCF 毕业项目。

```text
✅ 核心优势:
  - 包管理 - 简化应用部署
  - 版本控制 - 回滚和升级
  - 配置管理 - 灵活的参数化
  - 依赖管理 - 自动处理依赖
  - 模板引擎 - 强大的模板系统
  - 生态丰富 - 大量官方 Chart

📊 使用统计:
  - GitHub Stars: 26,000+
  - Chart 总数: 1,800+ 官方
  - 生产使用: 数万家公司
  - CNCF: 毕业项目
```

### 1.2 Helm 架构

```text
┌─────────────────────────────────────────────────┐
│                Helm 架构                         │
├─────────────────────────────────────────────────┤
│                                                   │
│  ┌──────────────────────────────────────────┐   │
│  │         Helm CLI (客户端)                 │   │
│  │  ┌────────────┬──────────────┐           │   │
│  │  │ helm install│ helm upgrade │           │   │
│  │  │ helm list  │ helm rollback│           │   │
│  │  └────────────┴──────────────┘           │   │
│  └──────────────────────────────────────────┘   │
│                    ↓                             │
│  ┌──────────────────────────────────────────┐   │
│  │      Kubernetes API Server               │   │
│  └──────────────────────────────────────────┘   │
│                    ↓                             │
│  ┌──────────────────────────────────────────┐   │
│  │        Kubernetes 资源                    │   │
│  │  ┌────────┬─────────┬────────────┐      │   │
│  │  │ Deploy │ Service │ ConfigMap  │      │   │
│  │  │ ment   │         │            │      │   │
│  │  └────────┴─────────┴────────────┘      │   │
│  └──────────────────────────────────────────┘   │
└─────────────────────────────────────────────────┘
```

### 1.3 Chart 结构

```text
my-app-chart/
├── Chart.yaml          # Chart 元数据
├── values.yaml         # 默认配置值
├── templates/          # K8s 资源模板
│   ├── deployment.yaml
│   ├── service.yaml
│   ├── configmap.yaml
│   ├── ingress.yaml
│   ├── _helpers.tpl   # 模板辅助函数
│   └── NOTES.txt      # 安装后提示
├── charts/            # 依赖 Chart
└── README.md          # 文档
```

---

## 2. 快速开始

### 2.1 安装 Helm

```bash
# macOS
brew install helm

# Linux
curl https://raw.githubusercontent.com/helm/helm/main/scripts/get-helm-3 | bash

# Windows
choco install kubernetes-helm

# 验证安装
helm version
```

### 2.2 创建 Chart

```bash
# 创建新 Chart
helm create go-app

# 查看生成的结构
tree go-app

# 验证 Chart
helm lint go-app

# 模板渲染（不安装）
helm template go-app go-app/

# 安装 Chart
helm install my-release go-app

# 查看已安装的 Release
helm list

# 卸载
helm uninstall my-release
```

---

## 3. Chart 开发

### 3.1 Chart.yaml

```yaml
# Chart.yaml
apiVersion: v2
name: go-app
description: A Helm chart for Go application with OTLP support
type: application
version: 1.0.0
appVersion: "1.0.0"

keywords:
  - go
  - otlp
  - observability
  - opentelemetry

maintainers:
  - name: Your Name
    email: your@email.com
    url: https://your-website.com

dependencies:
  - name: opentelemetry-collector
    version: "0.78.0"
    repository: https://open-telemetry.github.io/opentelemetry-helm-charts
    condition: otlp.collector.enabled

home: https://github.com/your-org/go-app
sources:
  - https://github.com/your-org/go-app

icon: https://your-website.com/logo.png
```

### 3.2 values.yaml

```yaml
# values.yaml - 默认配置
replicaCount: 3

image:
  repository: your-registry/go-app
  pullPolicy: IfNotPresent
  tag: "1.0.0"

imagePullSecrets: []
nameOverride: ""
fullnameOverride: ""

serviceAccount:
  create: true
  annotations: {}
  name: ""

podAnnotations:
  prometheus.io/scrape: "true"
  prometheus.io/port: "8080"
  prometheus.io/path: "/metrics"

podSecurityContext:
  runAsNonRoot: true
  runAsUser: 1000
  fsGroup: 1000

securityContext:
  allowPrivilegeEscalation: false
  capabilities:
    drop:
    - ALL
  readOnlyRootFilesystem: true

service:
  type: ClusterIP
  port: 8080
  targetPort: 8080
  annotations: {}

ingress:
  enabled: true
  className: nginx
  annotations:
    cert-manager.io/cluster-issuer: letsencrypt-prod
  hosts:
    - host: app.example.com
      paths:
        - path: /
          pathType: Prefix
  tls:
    - secretName: app-tls
      hosts:
        - app.example.com

resources:
  limits:
    cpu: 1000m
    memory: 512Mi
  requests:
    cpu: 100m
    memory: 128Mi

autoscaling:
  enabled: true
  minReplicas: 2
  maxReplicas: 10
  targetCPUUtilizationPercentage: 80
  targetMemoryUtilizationPercentage: 80

livenessProbe:
  httpGet:
    path: /health
    port: http
  initialDelaySeconds: 30
  periodSeconds: 10
  timeoutSeconds: 5
  failureThreshold: 3

readinessProbe:
  httpGet:
    path: /ready
    port: http
  initialDelaySeconds: 10
  periodSeconds: 5
  timeoutSeconds: 3
  failureThreshold: 3

nodeSelector: {}

tolerations: []

affinity:
  podAntiAffinity:
    preferredDuringSchedulingIgnoredDuringExecution:
    - weight: 100
      podAffinityTerm:
        labelSelector:
          matchExpressions:
          - key: app.kubernetes.io/name
            operator: In
            values:
            - go-app
        topologyKey: kubernetes.io/hostname

# OTLP 配置
otlp:
  enabled: true
  endpoint: "opentelemetry-collector:4317"
  insecure: true
  
  # OpenTelemetry Collector 依赖
  collector:
    enabled: true
    mode: deployment
    image:
      repository: otel/opentelemetry-collector
      tag: "0.91.0"
    
    config:
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
        jaeger:
          endpoint: jaeger-collector:14250
          tls:
            insecure: true
        prometheus:
          endpoint: 0.0.0.0:8889
        logging:
          loglevel: debug
      
      service:
        pipelines:
          traces:
            receivers: [otlp]
            processors: [memory_limiter, batch]
            exporters: [jaeger, logging]
          metrics:
            receivers: [otlp]
            processors: [memory_limiter, batch]
            exporters: [prometheus, logging]

# 监控配置
monitoring:
  serviceMonitor:
    enabled: true
    interval: 30s
    scrapeTimeout: 10s
```

### 3.3 Deployment 模板

```yaml
# templates/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: {{ include "go-app.fullname" . }}
  labels:
    {{- include "go-app.labels" . | nindent 4 }}
spec:
  {{- if not .Values.autoscaling.enabled }}
  replicas: {{ .Values.replicaCount }}
  {{- end }}
  selector:
    matchLabels:
      {{- include "go-app.selectorLabels" . | nindent 6 }}
  template:
    metadata:
      annotations:
        checksum/config: {{ include (print $.Template.BasePath "/configmap.yaml") . | sha256sum }}
        {{- with .Values.podAnnotations }}
        {{- toYaml . | nindent 8 }}
        {{- end }}
      labels:
        {{- include "go-app.selectorLabels" . | nindent 8 }}
    spec:
      {{- with .Values.imagePullSecrets }}
      imagePullSecrets:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      serviceAccountName: {{ include "go-app.serviceAccountName" . }}
      securityContext:
        {{- toYaml .Values.podSecurityContext | nindent 8 }}
      containers:
      - name: {{ .Chart.Name }}
        securityContext:
          {{- toYaml .Values.securityContext | nindent 12 }}
        image: "{{ .Values.image.repository }}:{{ .Values.image.tag | default .Chart.AppVersion }}"
        imagePullPolicy: {{ .Values.image.pullPolicy }}
        ports:
        - name: http
          containerPort: {{ .Values.service.targetPort }}
          protocol: TCP
        env:
        - name: SERVICE_NAME
          value: {{ include "go-app.fullname" . }}
        - name: SERVICE_VERSION
          value: {{ .Chart.AppVersion | quote }}
        - name: ENVIRONMENT
          value: {{ .Release.Namespace }}
        {{- if .Values.otlp.enabled }}
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: {{ .Values.otlp.endpoint | quote }}
        - name: OTEL_EXPORTER_OTLP_INSECURE
          value: {{ .Values.otlp.insecure | quote }}
        {{- end }}
        livenessProbe:
          {{- toYaml .Values.livenessProbe | nindent 12 }}
        readinessProbe:
          {{- toYaml .Values.readinessProbe | nindent 12 }}
        resources:
          {{- toYaml .Values.resources | nindent 12 }}
        volumeMounts:
        - name: tmp
          mountPath: /tmp
        - name: cache
          mountPath: /app/cache
      volumes:
      - name: tmp
        emptyDir: {}
      - name: cache
        emptyDir: {}
      {{- with .Values.nodeSelector }}
      nodeSelector:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      {{- with .Values.affinity }}
      affinity:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      {{- with .Values.tolerations }}
      tolerations:
        {{- toYaml . | nindent 8 }}
      {{- end }}
```

### 3.4 _helpers.tpl（模板辅助函数）

```yaml
# templates/_helpers.tpl
{{/*
Expand the name of the chart.
*/}}
{{- define "go-app.name" -}}
{{- default .Chart.Name .Values.nameOverride | trunc 63 | trimSuffix "-" }}
{{- end }}

{{/*
Create a default fully qualified app name.
*/}}
{{- define "go-app.fullname" -}}
{{- if .Values.fullnameOverride }}
{{- .Values.fullnameOverride | trunc 63 | trimSuffix "-" }}
{{- else }}
{{- $name := default .Chart.Name .Values.nameOverride }}
{{- if contains $name .Release.Name }}
{{- .Release.Name | trunc 63 | trimSuffix "-" }}
{{- else }}
{{- printf "%s-%s" .Release.Name $name | trunc 63 | trimSuffix "-" }}
{{- end }}
{{- end }}
{{- end }}

{{/*
Create chart name and version as used by the chart label.
*/}}
{{- define "go-app.chart" -}}
{{- printf "%s-%s" .Chart.Name .Chart.Version | replace "+" "_" | trunc 63 | trimSuffix "-" }}
{{- end }}

{{/*
Common labels
*/}}
{{- define "go-app.labels" -}}
helm.sh/chart: {{ include "go-app.chart" . }}
{{ include "go-app.selectorLabels" . }}
{{- if .Chart.AppVersion }}
app.kubernetes.io/version: {{ .Chart.AppVersion | quote }}
{{- end }}
app.kubernetes.io/managed-by: {{ .Release.Service }}
{{- end }}

{{/*
Selector labels
*/}}
{{- define "go-app.selectorLabels" -}}
app.kubernetes.io/name: {{ include "go-app.name" . }}
app.kubernetes.io/instance: {{ .Release.Name }}
{{- end }}

{{/*
Create the name of the service account to use
*/}}
{{- define "go-app.serviceAccountName" -}}
{{- if .Values.serviceAccount.create }}
{{- default (include "go-app.fullname" .) .Values.serviceAccount.name }}
{{- else }}
{{- default "default" .Values.serviceAccount.name }}
{{- end }}
{{- end }}

{{/*
OTLP Endpoint
*/}}
{{- define "go-app.otlp.endpoint" -}}
{{- if .Values.otlp.collector.enabled }}
{{- printf "%s-opentelemetry-collector:4317" .Release.Name }}
{{- else }}
{{- .Values.otlp.endpoint }}
{{- end }}
{{- end }}
```

---

## 4. OTLP 集成

### 4.1 ConfigMap 配置

```yaml
# templates/configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: {{ include "go-app.fullname" . }}
  labels:
    {{- include "go-app.labels" . | nindent 4 }}
data:
  otel-config.yaml: |
    service:
      name: {{ include "go-app.fullname" . }}
      version: {{ .Chart.AppVersion }}
      environment: {{ .Release.Namespace }}
    
    otlp:
      endpoint: {{ include "go-app.otlp.endpoint" . }}
      insecure: {{ .Values.otlp.insecure }}
      headers:
        x-service-name: {{ include "go-app.fullname" . }}
    
    sampling:
      ratio: 1.0
```

### 4.2 ServiceMonitor

```yaml
# templates/servicemonitor.yaml
{{- if .Values.monitoring.serviceMonitor.enabled }}
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: {{ include "go-app.fullname" . }}
  labels:
    {{- include "go-app.labels" . | nindent 4 }}
spec:
  selector:
    matchLabels:
      {{- include "go-app.selectorLabels" . | nindent 6 }}
  endpoints:
  - port: http
    path: /metrics
    interval: {{ .Values.monitoring.serviceMonitor.interval }}
    scrapeTimeout: {{ .Values.monitoring.serviceMonitor.scrapeTimeout }}
{{- end }}
```

---

## 5. 完整示例

### 5.1 多环境部署

```bash
# values-dev.yaml
replicaCount: 1
resources:
  limits:
    cpu: 500m
    memory: 256Mi
autoscaling:
  enabled: false
otlp:
  collector:
    enabled: true

# values-staging.yaml
replicaCount: 2
otlp:
  endpoint: "otel-collector.observability:4317"
  collector:
    enabled: false

# values-prod.yaml
replicaCount: 3
resources:
  limits:
    cpu: 2000m
    memory: 1Gi
autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 20
otlp:
  endpoint: "otel-collector.observability:4317"
  collector:
    enabled: false

# 部署到不同环境
helm install my-app ./go-app -f values-dev.yaml -n dev
helm install my-app ./go-app -f values-staging.yaml -n staging
helm install my-app ./go-app -f values-prod.yaml -n prod
```

### 5.2 升级和回滚

```bash
# 升级
helm upgrade my-app ./go-app \
  --set image.tag=1.1.0 \
  --wait \
  --timeout 5m

# 查看历史
helm history my-app

# 回滚到上一版本
helm rollback my-app

# 回滚到指定版本
helm rollback my-app 3
```

---

## 6. 最佳实践

### 6.1 Chart 测试

```yaml
# templates/tests/test-connection.yaml
apiVersion: v1
kind: Pod
metadata:
  name: "{{ include "go-app.fullname" . }}-test-connection"
  labels:
    {{- include "go-app.labels" . | nindent 4 }}
  annotations:
    "helm.sh/hook": test
spec:
  containers:
  - name: wget
    image: busybox
    command: ['wget']
    args: ['{{ include "go-app.fullname" . }}:{{ .Values.service.port }}/health']
  restartPolicy: Never
```

```bash
# 运行测试
helm test my-app
```

### 6.2 Chart 打包和发布

```bash
# 打包 Chart
helm package go-app

# 创建索引
helm repo index .

# 推送到 Chart Museum
curl --data-binary "@go-app-1.0.0.tgz" http://chartmuseum:8080/api/charts

# 推送到 Harbor
helm registry login harbor.example.com
helm push go-app-1.0.0.tgz oci://harbor.example.com/library
```

### 6.3 依赖管理

```bash
# 更新依赖
helm dependency update go-app

# 查看依赖
helm dependency list go-app

# 构建依赖
helm dependency build go-app
```

---

## 7. 发布与维护

### 7.1 版本管理

```yaml
# 语义化版本
# Chart.yaml
version: 1.2.3  # MAJOR.MINOR.PATCH
appVersion: "1.2.3"

# 版本更新规则:
# MAJOR: 不兼容的 API 变更
# MINOR: 向后兼容的功能新增
# PATCH: 向后兼容的问题修正
```

### 7.2 文档编写

```markdown
    # README.md

    ## 安装

    ```bash
    helm repo add myrepo https://charts.example.com
    helm install my-app myrepo/go-app
    ```

    ## 配置参数

    | 参数 | 描述 | 默认值 |
    |------|------|--------|
    | `replicaCount` | 副本数量 | `3` |
    | `image.repository` | 镜像仓库 | `your-registry/go-app` |
    | `otlp.enabled` | 启用 OTLP | `true` |

    ## 升级

    ```bash
    helm upgrade my-app myrepo/go-app --version 1.1.0
    ```

```

---

## 8. 总结

### 8.1 优势与劣势

```text
✅ 优势:
  - 标准化部署
  - 版本控制
  - 配置管理
  - 回滚能力
  - 生态丰富

❌ 劣势:
  - 学习曲线
  - 模板复杂性
  - 调试困难
```

**相关文档**:

- [01_Istio_Service_Mesh与OTLP完整集成_2025版.md](./01_Istio_Service_Mesh与OTLP完整集成_2025版.md)
- [03_ArgoCD_GitOps与OTLP完整集成_2025版.md](./03_ArgoCD_GitOps与OTLP完整集成_2025版.md)

---

**更新日期**: 2025-10-11  
**Helm 版本**: v3.13+  
**推荐指数**: ⭐⭐⭐⭐⭐
