.PHONY: help build test bench clean run-examples docker-up docker-down lint fmt

# 默认目标
.DEFAULT_GOAL := help

# 颜色定义
GREEN  := $(shell tput -Txterm setaf 2)
YELLOW := $(shell tput -Txterm setaf 3)
WHITE  := $(shell tput -Txterm setaf 7)
RESET  := $(shell tput -Txterm sgr0)

## help: 显示帮助信息
help:
	@echo ''
	@echo 'Usage:'
	@echo '  ${YELLOW}make${RESET} ${GREEN}<target>${RESET}'
	@echo ''
	@echo 'Targets:'
	@awk 'BEGIN {FS = ":.*?## "} { \
		if (/^[a-zA-Z_-]+:.*?##.*$$/) {printf "  ${YELLOW}%-20s${GREEN}%s${RESET}\n", $$1, $$2} \
		else if (/^## .*$$/) {printf "  ${WHITE}%s${RESET}\n", substr($$1,4)} \
		}' $(MAKEFILE_LIST)

## build: 编译所有示例
build:
	@echo "Building all examples..."
	@cd examples/basic && go build -o ../../bin/basic main.go
	@cd examples/context-propagation && go build -o ../../bin/context-propagation main.go
	@cd examples/custom-sampler && go build -o ../../bin/custom-sampler main.go
	@cd examples/batch-export && go build -o ../../bin/batch-export main.go
	@cd examples/metrics && go build -o ../../bin/metrics main.go
	@cd examples/performance/span-pool && go build -o ../../../bin/span-pool main.go
	@cd examples/performance/zero-alloc && go build -o ../../../bin/zero-alloc main.go
	@cd examples/resilience/circuit-breaker && go build -o ../../../bin/circuit-breaker main.go
	@cd examples/resilience/retry && go build -o ../../../bin/retry main.go
	@cd examples/custom-processor && go build -o ../../bin/custom-processor main.go
	@cd examples/distributed-tracing && go build -o ../../bin/distributed-tracing main.go
	@echo "✅ Build complete! Binaries in ./bin/"

## test: 运行所有测试
test:
	@echo "Running tests..."
	@go test -v ./...
	@echo "✅ Tests complete!"

## bench: 运行性能基准测试
bench:
	@echo "Running benchmarks..."
	@cd benchmarks && go test -bench=. -benchmem -benchtime=3s
	@echo "✅ Benchmarks complete!"

## bench-cpu: 运行 CPU profiling
bench-cpu:
	@echo "Running CPU profiling..."
	@cd benchmarks && go test -bench=. -cpuprofile=cpu.prof
	@echo "Analyze with: go tool pprof benchmarks/cpu.prof"

## bench-mem: 运行内存 profiling
bench-mem:
	@echo "Running memory profiling..."
	@cd benchmarks && go test -bench=. -memprofile=mem.prof
	@echo "Analyze with: go tool pprof benchmarks/mem.prof"

## clean: 清理编译产物
clean:
	@echo "Cleaning..."
	@rm -rf bin/
	@rm -f benchmarks/*.prof
	@echo "✅ Clean complete!"

## run-basic: 运行基础示例
run-basic:
	@echo "Running basic example..."
	@cd examples/basic && go run main.go

## run-all: 运行所有示例
run-all:
	@echo "Running all examples..."
	@for dir in examples/*/; do \
		if [ -f "$$dir/main.go" ]; then \
			echo "Running $$dir..."; \
			cd "$$dir" && go run main.go && cd ../..; \
		fi \
	done
	@echo "✅ All examples complete!"

## docker-up: 启动 OTLP Collector 和 Jaeger
docker-up:
	@echo "Starting OTLP Collector and Jaeger..."
	@docker-compose up -d
	@echo "✅ Services started!"
	@echo "  - OTLP Collector: localhost:4317 (gRPC), localhost:4318 (HTTP)"
	@echo "  - Jaeger UI: http://localhost:16686"
	@echo "  - Prometheus: http://localhost:9090"
	@echo "  - Grafana: http://localhost:3000"

## docker-down: 停止所有服务
docker-down:
	@echo "Stopping services..."
	@docker-compose down
	@echo "✅ Services stopped!"

## docker-logs: 查看日志
docker-logs:
	@docker-compose logs -f

## lint: 运行代码检查
lint:
	@echo "Running linters..."
	@golangci-lint run ./...
	@echo "✅ Lint complete!"

## fmt: 格式化代码
fmt:
	@echo "Formatting code..."
	@go fmt ./...
	@echo "✅ Format complete!"

## mod-tidy: 整理依赖
mod-tidy:
	@echo "Tidying dependencies..."
	@go mod tidy
	@echo "✅ Dependencies tidied!"

## mod-download: 下载依赖
mod-download:
	@echo "Downloading dependencies..."
	@go mod download
	@echo "✅ Dependencies downloaded!"

## install-tools: 安装开发工具
install-tools:
	@echo "Installing development tools..."
	@go install github.com/golangci/golangci-lint/cmd/golangci-lint@latest
	@echo "✅ Tools installed!"

## stats: 显示项目统计
stats:
	@echo "Project Statistics:"
	@echo "  Documents: $$(find docs -name '*.md' | wc -l)"
	@echo "  Examples: $$(find examples -name 'main.go' | wc -l)"
	@echo "  Tests: $$(find benchmarks -name '*_test.go' | wc -l)"
	@echo "  Total Lines (Go): $$(find . -name '*.go' -not -path './vendor/*' | xargs wc -l | tail -1 | awk '{print $$1}')"
	@echo "  Total Lines (Docs): $$(find docs -name '*.md' | xargs wc -l | tail -1 | awk '{print $$1}')"

## check: 运行所有检查（lint + test）
check: lint test
	@echo "✅ All checks passed!"

## dev: 开发模式（启动服务 + 运行示例）
dev: docker-up
	@sleep 3
	@$(MAKE) run-basic

## all: 完整流程（清理 + 编译 + 测试）
all: clean build test bench
	@echo "✅ All tasks complete!"
