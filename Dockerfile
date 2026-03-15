# syntax=docker/dockerfile:1
# OTLP Go - Production Dockerfile
# 多阶段构建优化：使用 golang:1.26-alpine + distroless

# ============================================
# Stage 1: Builder
# ============================================
FROM golang:1.26-alpine AS builder

# 安装构建依赖
RUN apk add --no-cache \
    git \
    ca-certificates \
    tzdata \
    && update-ca-certificates

# 设置工作目录
WORKDIR /build

# 创建非 root 用户（用于最终阶段）
RUN adduser -D -u 10001 appuser

# 首先复制依赖文件（利用 Docker 缓存层）
COPY go.mod go.sum go.work go.work.sum ./
COPY pkg/ ./pkg/

# 下载依赖（如果 go.mod 没有变化，这层会被缓存）
RUN go mod download && go work sync

# 复制源代码
COPY src/ ./src/
COPY examples/ ./examples/
COPY configs/ ./configs/

# 构建参数
ARG VERSION=dev
ARG BUILD_TIME
ARG GIT_COMMIT
ARG GIT_BRANCH

# 构建二进制文件
# -ldflags 优化：减少二进制文件大小，移除调试信息
# -trimpath：移除文件系统路径，提高可复现性
RUN CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build \
    -ldflags="-w -s \
    -X main.Version=${VERSION} \
    -X main.BuildTime=${BUILD_TIME} \
    -X main.GitCommit=${GIT_COMMIT} \
    -X main.GitBranch=${GIT_BRANCH}" \
    -trimpath \
    -o /build/bin/app \
    ./src

# 验证二进制文件
RUN ls -la /build/bin/app && \
    file /build/bin/app && \
    /build/bin/app -help 2>&1 || true

# ============================================
# Stage 2: Production (Distroless)
# ============================================
FROM gcr.io/distroless/static-debian12:nonroot AS production

# 从 builder 阶段复制 CA 证书
COPY --from=builder /etc/ssl/certs/ca-certificates.crt /etc/ssl/certs/

# 从 builder 阶段复制时区数据
COPY --from=builder /usr/share/zoneinfo /usr/share/zoneinfo

# 设置工作目录
WORKDIR /app

# 复制编译好的二进制文件
COPY --from=builder /build/bin/app /app/server

# 复制配置文件（可选，根据应用需求）
COPY --from=builder /build/configs/ /app/configs/

# 暴露应用端口
EXPOSE 8080

# 健康检查
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
    CMD ["/app/server", "-health-check"] || exit 1

# 使用非 root 用户运行（distroless 默认就是 nonroot）
USER nonroot:nonroot

# 入口点
ENTRYPOINT ["/app/server"]

# ============================================
# Stage 3: Debug (基于 Alpine，带 Shell)
# ============================================
FROM alpine:3.20 AS debug

# 安装调试工具
RUN apk add --no-cache \
    ca-certificates \
    tzdata \
    curl \
    wget \
    busybox-extras \
    bind-tools \
    tcpdump \
    strace \
    gdb

# 创建非 root 用户
RUN adduser -D -u 10001 appuser

WORKDIR /app

# 从 builder 复制二进制
COPY --from=builder /build/bin/app /app/server
COPY --from=builder /build/configs/ /app/configs/

# 暴露端口
EXPOSE 8080

# 健康检查
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
    CMD wget --spider -q http://localhost:8080/health || exit 1

USER appuser

ENTRYPOINT ["/app/server"]
