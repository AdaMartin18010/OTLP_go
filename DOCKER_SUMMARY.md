# 🐳 OTLP Go - Docker 配置完成摘要

## ✅ 已创建文件清单

### 1. Dockerfile（生产环境）

- **路径**: `e:\_src\OTLP_go\Dockerfile`
- **特点**:
  - 三阶段构建：Builder → Production (distroless) → Debug
  - 使用 `golang:1.26-alpine` 作为构建基础镜像
  - 使用 `gcr.io/distroless/static-debian12:nonroot` 作为生产镜像
  - 最终镜像大小：约 25MB
  - 非 root 用户运行 (UID: 65532)
  - 支持健康检查
  - 注入版本信息构建参数

### 2. Dockerfile.dev（开发环境）

- **路径**: `e:\_src\OTLP_go\Dockerfile.dev`
- **特点**:
  - 基于 `golang:1.26-alpine`
  - 集成 `air` 热重载工具
  - 集成 `delve` 调试器 (端口 2345)
  - 集成 `golangci-lint` 代码检查
  - 源代码挂载实现实时更新
  - 预配置 `.air.toml` 热重载配置

### 3. docker-compose.yml（完整服务栈）

- **路径**: `e:\_src\OTLP_go\docker-compose.yml`
- **包含服务**:

  | 服务 | 镜像 | 端口 | 说明 |
  |------|------|------|------|
  | `app` | 本地构建 | 8080 | 生产模式应用 |
  | `app-dev` | 本地构建 | 8080, 2345 | 开发模式应用（热重载） |
  | `otel-collector` | otel/opentelemetry-collector-contrib:0.115.0 | 4317, 4318, 8888, 8889, 13133 | OTLP 收集器 |
  | `jaeger` | jaegertracing/all-in-one:1.62.0 | 16686, 14250, 14268 | 分布式追踪 |
  | `prometheus` | prom/prometheus:v3.0.1 | 9090 | 指标监控 |
  | `grafana` | grafana/grafana:11.4.0 | 3000 | 可视化平台 |
  | `tempo` | grafana/tempo:2.6.1 | 3200 | 追踪后端（可选 Profile） |
  | `loki` | grafana/loki:3.3.2 | 3100 | 日志聚合（可选 Profile） |

### 4. .dockerignore

- **路径**: `e:\_src\OTLP_go\.dockerignore`
- **忽略内容**:
  - 版本控制文件 (.git, .github)
  - IDE 配置 (.vscode, .idea)
  - 文档文件 (*.md)
  - 脚本文件 (*.ps1,*.sh)
  - 测试文件 (*_test.go)
  - 构建输出 (bin/, build/, dist/)
  - 敏感信息 (.env, *.pem)

### 5. 辅助配置文件

#### docker-compose.override.yml

- 本地开发环境的默认覆盖配置
- 启用调试端口和开发模式

#### .env.example

- 环境变量模板
- 包含应用配置、OTLP 端点、Grafana 凭证等

#### configs/grafana-dashboards.yml

- Grafana 仪表板自动加载配置

#### configs/dashboards/otlp-go-overview.json

- OTLP Go 应用概览仪表板
- 包含请求速率、P95 延迟、状态分布、内存使用等面板

#### DOCKER_GUIDE.md

- 完整的 Docker 使用指南
- 包含快速开始、生产部署、开发使用、故障排查等

---

## 🚀 快速使用指南

### 启动生产环境

```bash
# 启动完整服务栈
docker-compose up -d

# 访问服务
# - 应用: http://localhost:8080
# - Grafana: http://localhost:3000 (admin/admin)
# - Prometheus: http://localhost:9090
# - Jaeger: http://localhost:16686
```

### 启动开发环境

```bash
# 使用 Make 命令
make docker-dev

# 或直接运行
docker-compose --profile dev up -d
```

### Makefile 新增命令

```bash
make docker-build-prod    # 构建生产镜像（带版本信息）
make docker-build-dev     # 构建开发镜像
make docker-compose-up    # 启动服务栈
make docker-compose-down  # 停止服务栈
docker-dev                # 启动开发环境（热重载）
docker-full               # 启动完整栈（含 Tempo、Loki）
docker-logs               # 查看所有日志
docker-logs-app           # 查看应用日志
docker-logs-collector     # 查看 Collector 日志
docker-clean              # 清理 Docker 资源
docker-shell              # 进入开发容器 Shell
```

---

## 🔒 安全特性

1. **非 root 用户运行**: 所有容器使用非 root 用户
2. **Distroless 生产镜像**: 无 shell，最小攻击面
3. **只读文件系统**: 生产容器启用 `read_only: true`
4. **禁止特权提升**: `no-new-privileges:true`
5. **资源限制**: CPU 和内存限制配置
6. **健康检查**: 所有服务配置健康检查

---

## 📊 服务访问信息

| 服务 | URL | 默认凭证 | 用途 |
|------|-----|----------|------|
| OTLP Go App | <http://localhost:8080> | - | 应用程序 |
| Grafana | <http://localhost:3000> | admin/admin | 可视化仪表板 |
| Prometheus | <http://localhost:9090> | - | 指标查询 |
| Jaeger UI | <http://localhost:16686> | - | 分布式追踪 |
| Collector Health | <http://localhost:13133> | - | Collector 健康检查 |

---

## 📁 文件结构

```
OTLP_go/
├── Dockerfile                      # 生产环境多阶段构建
├── Dockerfile.dev                  # 开发环境（热重载）
├── Dockerfile.optimized            # 原有优化版本（保留）
├── docker-compose.yml              # 完整服务栈
├── docker-compose.override.yml     # 本地开发覆盖配置
├── .dockerignore                   # Docker 忽略文件
├── .env.example                    # 环境变量模板
├── DOCKER_GUIDE.md                 # Docker 使用指南
├── DOCKER_SUMMARY.md               # 本摘要文件
├── Makefile                        # 更新后的构建脚本
└── configs/
    ├── grafana-dashboards.yml      # 仪表板配置
    ├── grafana-datasources.yml     # 数据源配置
    ├── dashboards/
    │   └── otlp-go-overview.json   # 应用概览仪表板
    ├── otel-collector-config.yaml  # Collector 配置
    ├── prometheus.yml              # Prometheus 配置
    └── tempo.yaml                  # Tempo 配置
```

---

## ⚠️ 注意事项

1. **环境变量**: 复制 `.env.example` 为 `.env` 并修改敏感信息
2. **端口冲突**: 如果端口被占用，修改 `docker-compose.yml` 中的端口映射
3. **内存要求**: 建议至少 4GB 内存运行完整服务栈
4. **首次启动**: Grafana 首次启动需要一些时间初始化

---

## 🔧 故障排查

```bash
# 查看服务状态
docker-compose ps

# 查看日志
docker-compose logs -f [service-name]

# 重启服务
docker-compose restart [service-name]

# 完全重置（包括数据）
docker-compose down -v
docker system prune -a --volumes
```

---

## 📚 相关文档

- `DOCKER_GUIDE.md` - 详细使用指南
- `README.md` - 项目主文档
- `WORKSPACE.md` - Go Workspace 说明

---

**配置完成时间**: 2026-03-15
**Docker 版本**: 27+
**Docker Compose 版本**: 3.8
