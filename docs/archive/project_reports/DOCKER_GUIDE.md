# 🐳 OTLP Go - Docker 配置指南

本文档详细介绍 OTLP Go 项目的 Docker 配置和使用方法。

## 📋 目录

- [🐳 OTLP Go - Docker 配置指南](#)

---

## 🚀 快速开始

### 1. 启动完整服务栈

```bash
# 启动所有服务（生产模式）
docker-compose up -d

# 查看服务状态
docker-compose ps

# 查看日志
docker-compose logs -f
```

### 2. 访问服务

| 服务 | URL | 说明 |
|------|-----|------|
| **应用** | <http://localhost:8080> | OTLP Go 应用 |
| **Grafana** | <http://localhost:3000> | 可视化仪表板 (admin/admin) |
| **Prometheus** | <http://localhost:9090> | 指标查询 |
| **Jaeger** | <http://localhost:16686> | 分布式追踪 |

---

## 📁 配置文件说明

### Dockerfile（生产环境）

多阶段构建优化：

- **Builder 阶段**: 使用 `golang:1.26-alpine` 编译二进制
- **Production 阶段**: 使用 `distroless/static-debian12:nonroot` 运行
- **Debug 阶段**: 基于 Alpine，包含调试工具

特点：

- ✅ 最小镜像体积（~25MB 最终镜像）
- ✅ 非 root 用户运行（UID: 65532）
- ✅ 无 shell，减少攻击面
- ✅ 支持健康检查
- ✅ 构建参数支持版本信息注入

### Dockerfile.dev（开发环境）

开发优化：

- 包含 `air` 热重载工具
- 包含 `delve` 调试器
- 包含 `golangci-lint` 代码检查
- 源代码挂载，实时更新

### docker-compose.yml

完整服务栈：

| 服务 | 镜像 | 端口 | 说明 |
|------|------|------|------|
| app | 本地构建 | 8080 | Go 应用（生产模式） |
| app-dev | 本地构建 | 8080, 2345 | Go 应用（开发模式，热重载） |
| otel-collector | otel/opentelemetry-collector-contrib | 4317, 4318, 8888, 8889 | OTLP 收集器 |
| jaeger | jaegertracing/all-in-one | 16686 | 分布式追踪 UI |
| prometheus | prom/prometheus | 9090 | 指标存储和查询 |
| grafana | grafana/grafana | 3000 | 可视化平台 |
| tempo | grafana/tempo | 3200 | 追踪后端（可选） |

---

## 🏭 生产环境部署

### 构建生产镜像

```bash
# 构建生产镜像
docker build -t otlp-go:latest .

# 构建带版本标签的镜像
docker build \
  --build-arg VERSION=1.0.0 \
  --build-arg BUILD_TIME=$(date -u +"%Y-%m-%dT%H:%M:%SZ") \
  --build-arg GIT_COMMIT=$(git rev-parse --short HEAD) \
  --build-arg GIT_BRANCH=$(git rev-parse --abbrev-ref HEAD) \
  -t otlp-go:1.0.0 .
```

### 运行生产容器

```bash
docker run -d \
  --name otlp-go \
  -p 8080:8080 \
  -e OTLP_GRPC_ENDPOINT=otel-collector:4317 \
  -e LOG_LEVEL=info \
  --read-only \
  --security-opt no-new-privileges:true \
  otlp-go:latest
```

### 使用 Docker Compose 生产部署

```bash
# 复制环境变量模板
cp .env.example .env

# 编辑 .env 文件，设置生产值
# GRAFANA_ADMIN_PASSWORD=your-secure-password

# 启动生产服务
docker-compose up -d app prometheus grafana jaeger otel-collector
```

---

## 💻 开发环境使用

### 启动开发环境

```bash
# 使用开发配置启动
docker-compose --profile dev up -d app-dev

# 或者启动整个开发栈
docker-compose --profile dev up -d
```

### 热重载

开发容器使用 `air` 实现热重载：

- 修改 `src/` 目录下的 Go 文件
- 应用自动重新编译和重启
- 无需手动重建容器

### 远程调试

```bash
# 1. 确保开发容器在运行
docker-compose ps app-dev

# 2. 在 VS Code 中配置 launch.json
```

**launch.json 配置示例：**

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "name": "Remote Debug (Docker)",
      "type": "go",
      "request": "attach",
      "mode": "remote",
      "remotePath": "/app",
      "port": 2345,
      "host": "localhost",
      "showLog": true
    }
  ]
}
```

### 代码检查

```bash
# 进入开发容器
docker-compose exec app-dev sh

# 运行代码检查
golangci-lint run ./...

# 格式化代码
goimports -w .
```

---

## 🏗️ 服务架构

```
┌─────────────────────────────────────────────────────────────┐
│                        客户端请求                            │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────────┐
│  OTLP Go App (Port: 8080)                                   │
│  - 生成 Traces, Metrics, Logs                               │
└──────────┬────────────────────────────────┬─────────────────┘
           │                                │
           ▼                                ▼
┌─────────────────────┐           ┌─────────────────────┐
│  OTLP gRPC (4317)   │           │  OTLP HTTP (4318)   │
└──────────┬──────────┘           └──────────┬──────────┘
           │                                 │
           └────────────────┬────────────────┘
                            ▼
           ┌────────────────────────────────┐
           │  OpenTelemetry Collector       │
           │  - 接收 OTLP 数据              │
           │  - 处理和批处理                │
           │  - 路由到后端                  │
           └──────┬───────────────┬─────────┘
                  │               │
        ┌─────────┘               └─────────┐
        ▼                                   ▼
┌───────────────┐                  ┌───────────────┐
│   Jaeger      │                  │  Prometheus   │
│  (Traces)     │                  │  (Metrics)    │
│  Port: 16686  │                  │  Port: 9090   │
└───────┬───────┘                  └───────┬───────┘
        │                                  │
        └──────────────┬───────────────────┘
                       ▼
              ┌────────────────┐
              │    Grafana     │
              │  Port: 3000    │
              │  统一可视化    │
              └────────────────┘
```

---

## 🔧 故障排查

### 查看服务日志

```bash
# 查看所有服务日志
docker-compose logs -f

# 查看特定服务日志
docker-compose logs -f app
docker-compose logs -f otel-collector
docker-compose logs -f jaeger

# 查看最后 100 行
docker-compose logs --tail=100 app
```

### 健康检查

```bash
# 检查服务健康状态
docker-compose ps

# 手动测试健康检查
curl http://localhost:8080/health
curl http://localhost:13133/  # Collector health
wget -qO- http://localhost:9090/-/healthy  # Prometheus
```

### 常见问题

#### 端口冲突

```bash
# 检查端口占用
lsof -i :8080
lsof -i :3000

# 修改 docker-compose.yml 中的端口映射
# ports:
#   - "8081:8080"  # 使用 8081 替代 8080
```

#### 内存不足

```bash
# 查看容器资源使用
docker stats

# 调整资源限制（docker-compose.yml）
deploy:
  resources:
    limits:
      cpus: '1.0'
      memory: 512M
```

#### 网络问题

```bash
# 检查网络
docker network ls
docker network inspect otlp-go_otlp-network

# 重启服务
docker-compose restart
```

### 清理命令

```bash
# 停止所有服务
docker-compose down

# 停止并删除数据卷
docker-compose down -v

# 删除所有未使用的镜像、容器、网络和卷
docker system prune -a --volumes

# 仅删除构建缓存
docker builder prune
```

---

## 📊 性能优化

### 镜像大小优化

| 镜像类型 | 大小 | 说明 |
|---------|------|------|
| Builder | ~400MB | 包含完整 Go 工具链 |
| Production (distroless) | ~25MB | 仅包含必要二进制和 CA 证书 |
| Debug (alpine) | ~50MB | 包含调试工具 |

### 构建缓存优化

```dockerfile
# 好的做法：先复制依赖文件
COPY go.mod go.sum ./
RUN go mod download  # 这一层会被缓存

# 后复制源代码
COPY . .
RUN go build ...
```

### 运行时优化

```yaml
# docker-compose.yml
services:
  app:
    deploy:
      resources:
        limits:
          cpus: '1.0'
          memory: 512M
        reservations:
          cpus: '0.25'
          memory: 128M
    security_opt:
      - no-new-privileges:true
    read_only: true
    tmpfs:
      - /tmp:noexec,nosuid,size=100m
```

---

## 🔒 安全建议

1. **使用非 root 用户运行容器**（已在配置中实现）
2. **只读文件系统**（`read_only: true`）
3. **禁止特权提升**（`no-new-privileges:true`）
4. **定期更新基础镜像**
5. **使用 secrets 管理敏感信息**
6. **网络隔离**：使用 Docker 网络而非 host 网络

---

## 📚 相关文档

- [Dockerfile 参考](https://docs.docker.com/engine/reference/builder/)
- [Docker Compose 参考](https://docs.docker.com/compose/compose-file/)
- [Distroless 镜像](https://github.com/GoogleContainerTools/distroless)
- [OpenTelemetry Collector](https://opentelemetry.io/docs/collector/)
