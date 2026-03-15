# OTLP Go SDK - Makefile
# Cross-platform build system supporting Windows, Linux, and macOS

# Detect OS
ifeq ($(OS),Windows_NT)
    DETECTED_OS := Windows
    RM := del /Q
    RMDIR := rmdir /S /Q
    PATHSEP := \
    EXEC_EXT := .exe
    DEV_NULL := nul
else
    DETECTED_OS := $(shell uname -s)
    RM := rm -f
    RMDIR := rm -rf
    PATHSEP := /
    EXEC_EXT :=
    DEV_NULL := /dev/null
endif

# Colors for terminal output
ifeq ($(DETECTED_OS),Windows)
    CYAN :=
    GREEN :=
    YELLOW :=
    RED :=
    RESET :=
else
    CYAN := \033[36m
    GREEN := \033[32m
    YELLOW := \033[33m
    RED := \033[31m
    RESET := \033[0m
endif

# Variables
PROJECT_NAME := otlp-go
VERSION := $(shell git describe --tags --always --dirty 2>$(DEV_NULL) || echo "dev")
BUILD_TIME := $(shell date -u +"%Y-%m-%dT%H:%M:%SZ" 2>$(DEV_NULL) || echo "unknown")
LDFLAGS := -ldflags "-X main.Version=$(VERSION) -X main.BuildTime=$(BUILD_TIME)"

# Directories
BUILD_DIR := build
BIN_DIR := bin
COVERAGE_DIR := $(BUILD_DIR)/coverage
SCRIPTS_DIR := scripts

# Default target
.PHONY: all
all: fmt vet build test

# Help target
.PHONY: help
help:
	@echo "$(CYAN)OTLP Go SDK - Available Targets:$(RESET)"
	@echo ""
	@echo "  $(GREEN)all$(RESET)              - Run fmt, vet, build, and test"
	@echo "  $(GREEN)build$(RESET)            - Build all modules"
	@echo "  $(GREEN)test$(RESET)             - Run all tests"
	@echo "  $(GREEN)coverage$(RESET)         - Generate coverage report"
	@echo "  $(GREEN)lint$(RESET)             - Run code linting"
	@echo "  $(GREEN)benchmark$(RESET)        - Run benchmark tests"
	@echo "  $(GREEN)clean$(RESET)            - Clean build artifacts"
	@echo "  $(GREEN)install$(RESET)          - Install dependencies"
	@echo "  $(GREEN)tidy$(RESET)             - Tidy go modules"
	@echo "  $(GREEN)fmt$(RESET)              - Format code"
	@echo "  $(GREEN)vet$(RESET)              - Run static analysis"
	@echo "  $(GREEN)docker-build$(RESET)     - Build Docker image"
	@echo "  $(GREEN)docker-run$(RESET)       - Run Docker container"
	@echo "  $(GREEN)docker-compose-up$(RESET) - Start services with docker-compose"
	@echo "  $(GREEN)docker-compose-down$(RESET) - Stop docker-compose services"
	@echo "  $(GREEN)check$(RESET)            - Run health checks"
	@echo "  $(GREEN)ci$(RESET)               - Run CI pipeline"
	@echo "  $(GREEN)release$(RESET)          - Prepare release build"
	@echo "  $(GREEN)generate$(RESET)         - Run code generation"
	@echo "  $(GREEN)docs$(RESET)             - Generate documentation"
	@echo ""
	@echo "$(CYAN)Scripts (alternative usage):$(RESET)"
	@echo "  $(YELLOW)make run-script SCRIPT=test$(RESET)    - Run test.sh"
	@echo "  $(YELLOW)make run-script SCRIPT=build$(RESET)   - Run build.sh"
	@echo "  $(YELLOW)make run-script SCRIPT=lint$(RESET)    - Run lint.sh"
	@echo ""

# Build all modules
.PHONY: build
build:
	@echo "$(CYAN)Building all modules...$(RESET)"
	@go build $(LDFLAGS) ./...
	@go build $(LDFLAGS) ./pkg/...
	@go build $(LDFLAGS) ./examples/...
	@echo "$(GREEN)✅ Build completed$(RESET)"

# Run all tests
.PHONY: test
test:
	@echo "$(CYAN)Running tests...$(RESET)"
	@go test -race -v ./... 2>&1 | tee $(BUILD_DIR)/test.log || exit 1
	@echo "$(GREEN)✅ Tests completed$(RESET)"

# Run tests with coverage
.PHONY: coverage
coverage:
	@echo "$(CYAN)Running tests with coverage...$(RESET)"
	@mkdir -p $(COVERAGE_DIR)
	@go test -race -coverprofile=$(COVERAGE_DIR)/coverage.out ./...
	@go tool cover -html=$(COVERAGE_DIR)/coverage.out -o $(COVERAGE_DIR)/coverage.html
	@go tool cover -func=$(COVERAGE_DIR)/coverage.out | tail -n 1
	@echo "$(GREEN)✅ Coverage report generated: $(COVERAGE_DIR)/coverage.html$(RESET)"

# Run coverage for all modules individually
.PHONY: coverage-all
coverage-all:
	@echo "$(CYAN)Generating coverage report for all modules...$(RESET)"
	@mkdir -p $(COVERAGE_DIR)
	@echo "mode: set" > $(COVERAGE_DIR)/coverage.out
	@for module in . ./pkg/* ./examples/*; do \
		if [ -f "$$module/go.mod" ]; then \
			echo "Processing $$module..."; \
			(cd $$module && go test -coverprofile=coverage.tmp ./... 2>/dev/null || true); \
			if [ -f "$$module/coverage.tmp" ]; then \
				cat $$module/coverage.tmp | grep -v "mode: set" >> $(COVERAGE_DIR)/coverage.out; \
				rm -f $$module/coverage.tmp; \
			fi; \
		fi; \
	done
	@go tool cover -html=$(COVERAGE_DIR)/coverage.out -o $(COVERAGE_DIR)/coverage.html 2>/dev/null || echo "$(YELLOW)⚠️  Could not generate HTML report$(RESET)"
	@echo "$(GREEN)✅ Coverage report generated$(RESET)"

# Run linter
.PHONY: lint
lint:
	@echo "$(CYAN)Running linter...$(RESET)"
	@if command -v golangci-lint >$(DEV_NULL) 2>&1; then \
		golangci-lint run ./...; \
	else \
		echo "$(YELLOW)⚠️  golangci-lint not found, using go vet instead$(RESET)"; \
		go vet ./...; \
	fi
	@echo "$(GREEN)✅ Linting completed$(RESET)"

# Run benchmarks
.PHONY: benchmark
benchmark:
	@echo "$(CYAN)Running benchmarks...$(RESET)"
	@go test -bench=. -benchmem -run=^$$ ./pkg/... 2>&1 | tee $(BUILD_DIR)/benchmark.log
	@echo "$(GREEN)✅ Benchmarks completed$(RESET)"

# Run benchmarks with detailed output
.PHONY: benchmark-detailed
benchmark-detailed:
	@echo "$(CYAN)Running detailed benchmarks...$(RESET)"
	@go test -bench=. -benchmem -benchtime=5s -cpuprofile=$(BUILD_DIR)/cpu.prof -memprofile=$(BUILD_DIR)/mem.prof -run=^$$ ./pkg/...
	@echo "$(GREEN)✅ Detailed benchmarks completed$(RESET)"
	@echo "$(CYAN)Profiles saved to $(BUILD_DIR)/$(RESET)"

# Format code
.PHONY: fmt
fmt:
	@echo "$(CYAN)Formatting code...$(RESET)"
	@go fmt ./...
	@echo "$(GREEN)✅ Formatting completed$(RESET)"

# Run go vet
.PHONY: vet
vet:
	@echo "$(CYAN)Running go vet...$(RESET)"
	@go vet ./...
	@echo "$(GREEN)✅ Vet completed$(RESET)"

# Tidy all modules
.PHONY: tidy
tidy:
	@echo "$(CYAN)Tidying modules...$(RESET)"
	@go mod tidy
	@go work sync
	@for dir in pkg/* examples/* benchmarks; do \
		if [ -f "$$dir/go.mod" ]; then \
			echo "Tidying $$dir..."; \
			(cd $$dir && go mod tidy 2>/dev/null || true); \
		fi; \
	done
	@echo "$(GREEN)✅ Tidy completed$(RESET)"

# Install dependencies
.PHONY: install
install:
	@echo "$(CYAN)Installing dependencies...$(RESET)"
	@go mod download
	@go work sync
	@echo "$(GREEN)✅ Dependencies installed$(RESET)"

# Clean build artifacts
.PHONY: clean
clean:
	@echo "$(CYAN)Cleaning build artifacts...$(RESET)"
	@-$(RMDIR) $(BUILD_DIR) 2>$(DEV_NULL) || true
	@-$(RM) coverage.out coverage.html 2>$(DEV_NULL) || true
	@go clean -cache -testcache
	@echo "$(GREEN)✅ Clean completed$(RESET)"

# Deep clean (including module cache)
.PHONY: clean-all
clean-all: clean
	@echo "$(CYAN)Deep cleaning...$(RESET)"
	@go clean -modcache
	@echo "$(GREEN)✅ Deep clean completed$(RESET)"

# Build Docker image
.PHONY: docker-build
docker-build:
	@echo "$(CYAN)Building Docker image...$(RESET)"
	@docker build -t $(PROJECT_NAME):$(VERSION) -t $(PROJECT_NAME):latest .
	@echo "$(GREEN)✅ Docker image built: $(PROJECT_NAME):$(VERSION)$(RESET)"

# Run Docker container
.PHONY: docker-run
docker-run:
	@echo "$(CYAN)Running Docker container...$(RESET)"
	@docker run --rm -it $(PROJECT_NAME):latest

# Docker compose up
.PHONY: docker-compose-up
docker-compose-up:
	@echo "$(CYAN)Starting services with docker-compose...$(RESET)"
	@docker-compose up -d
	@echo "$(GREEN)✅ Services started. Grafana: http://localhost:3000 (admin/admin)$(RESET)"

# Docker compose down
.PHONY: docker-compose-down
docker-compose-down:
	@echo "$(CYAN)Stopping docker-compose services...$(RESET)"
	@docker-compose down
	@echo "$(GREEN)✅ Services stopped$(RESET)"

# Docker compose with dev profile
.PHONY: docker-dev
docker-dev:
	@echo "$(CYAN)Starting development services with hot reload...$(RESET)"
	@docker-compose --profile dev up -d
	@echo "$(GREEN)✅ Dev services started with hot reload$(RESET)"

# Docker compose with all optional services
.PHONY: docker-full
docker-full:
	@echo "$(CYAN)Starting full stack (including Tempo and Loki)...$(RESET)"
	@docker-compose --profile tempo --profile loki up -d
	@echo "$(GREEN)✅ Full stack started$(RESET)"

# Docker compose logs
.PHONY: docker-logs
docker-logs:
	@docker-compose logs -f

# Docker compose logs for specific service
.PHONY: docker-logs-app
docker-logs-app:
	@docker-compose logs -f app

# Docker compose logs for collector
.PHONY: docker-logs-collector
docker-logs-collector:
	@docker-compose logs -f otel-collector

# Docker build production image with build args
.PHONY: docker-build-prod
docker-build-prod:
	@echo "$(CYAN)Building production Docker image...$(RESET)"
	@docker build \
		--build-arg VERSION=$(VERSION) \
		--build-arg BUILD_TIME=$(BUILD_TIME) \
		--build-arg GIT_COMMIT=$(shell git rev-parse --short HEAD 2>/dev/null || echo "unknown") \
		--build-arg GIT_BRANCH=$(shell git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "unknown") \
		--target production \
		-t $(PROJECT_NAME):$(VERSION) \
		-t $(PROJECT_NAME):latest \
		.
	@echo "$(GREEN)✅ Production image built: $(PROJECT_NAME):$(VERSION)$(RESET)"

# Docker build development image
.PHONY: docker-build-dev
docker-build-dev:
	@echo "$(CYAN)Building development Docker image...$(RESET)"
	@docker build -f Dockerfile.dev -t $(PROJECT_NAME):dev .
	@echo "$(GREEN)✅ Development image built: $(PROJECT_NAME):dev$(RESET)"

# Docker security scan
.PHONY: docker-scan
docker-scan:
	@echo "$(CYAN)Scanning Docker image for vulnerabilities...$(RESET)"
	@docker scan $(PROJECT_NAME):latest || echo "$(YELLOW)⚠️  Docker scan not available$(RESET)"

# Docker cleanup
.PHONY: docker-clean
docker-clean:
	@echo "$(CYAN)Cleaning up Docker resources...$(RESET)"
	@docker-compose down -v --remove-orphans
	@docker system prune -f
	@echo "$(GREEN)✅ Docker cleanup completed$(RESET)"

# Docker shell into dev container
.PHONY: docker-shell
docker-shell:
	@echo "$(CYAN)Opening shell in development container...$(RESET)"
	@docker-compose exec app-dev sh || echo "$(RED)Dev container not running. Run 'make docker-dev' first.$(RESET)"

# Check project health
.PHONY: check
check:
	@echo "$(CYAN)Running project health checks...$(RESET)"
	@echo "1. Build check..."
	@go build ./... >$(DEV_NULL) 2>&1 && echo "  $(GREEN)✓$(RESET) Build successful" || (echo "  $(RED)✗$(RESET) Build failed" && exit 1)
	@echo "2. Test check..."
	@go test ./... >$(DEV_NULL) 2>&1 && echo "  $(GREEN)✓$(RESET) Tests passed" || (echo "  $(RED)✗$(RESET) Tests failed" && exit 1)
	@echo "3. Format check..."
	@if [ -z "$$(gofmt -l .)" ]; then \
		echo "  $(GREEN)✓$(RESET) Code is formatted"; \
	else \
		echo "  $(RED)✗$(RESET) Code needs formatting:"; \
		gofmt -l .; \
		exit 1; \
	fi
	@echo "4. Vet check..."
	@go vet ./... >$(DEV_NULL) 2>&1 && echo "  $(GREEN)✓$(RESET) Vet passed" || (echo "  $(RED)✗$(RESET) Vet failed" && exit 1)
	@echo "5. Module check..."
	@go mod verify >$(DEV_NULL) 2>&1 && echo "  $(GREEN)✓$(RESET) Modules verified" || (echo "  $(RED)✗$(RESET) Module verification failed" && exit 1)
	@echo ""
	@echo "$(GREEN)✅ All health checks passed!$(RESET)"

# CI pipeline
.PHONY: ci
ci: fmt vet build test coverage
	@echo "$(GREEN)✅ CI pipeline completed$(RESET)"

# Release build
.PHONY: release
release:
	@echo "$(CYAN)Building release...$(RESET)"
	@mkdir -p $(BUILD_DIR)/release
	@GOOS=linux GOARCH=amd64 go build $(LDFLAGS) -o $(BUILD_DIR)/release/$(PROJECT_NAME)-linux-amd64$(EXEC_EXT) ./...
	@GOOS=linux GOARCH=arm64 go build $(LDFLAGS) -o $(BUILD_DIR)/release/$(PROJECT_NAME)-linux-arm64$(EXEC_EXT) ./...
	@GOOS=darwin GOARCH=amd64 go build $(LDFLAGS) -o $(BUILD_DIR)/release/$(PROJECT_NAME)-darwin-amd64$(EXEC_EXT) ./...
	@GOOS=darwin GOARCH=arm64 go build $(LDFLAGS) -o $(BUILD_DIR)/release/$(PROJECT_NAME)-darwin-arm64$(EXEC_EXT) ./...
	@GOOS=windows GOARCH=amd64 go build $(LDFLAGS) -o $(BUILD_DIR)/release/$(PROJECT_NAME)-windows-amd64.exe ./...
	@echo "$(GREEN)✅ Release builds completed: $(BUILD_DIR)/release/$(RESET)"

# Generate code
.PHONY: generate
generate:
	@echo "$(CYAN)Running code generation...$(RESET)"
	@go generate ./...
	@echo "$(GREEN)✅ Code generation completed$(RESET)"

# Generate documentation
.PHONY: docs
docs:
	@echo "$(CYAN)Generating documentation...$(RESET)"
	@mkdir -p $(BUILD_DIR)/docs
	@godoc -http=:6060 &
	@echo "$(GREEN)✅ Documentation server started at http://localhost:6060$(RESET)"

# Run specific example
.PHONY: example-logs
example-logs:
	@echo "$(CYAN)Running logs example...$(RESET)"
	@go run examples/logs/main.go

.PHONY: example-metrics
example-metrics:
	@echo "$(CYAN)Running metrics example...$(RESET)"
	@go run examples/metrics/main.go

.PHONY: example-basic
example-basic:
	@echo "$(CYAN)Running basic example...$(RESET)"
	@go run examples/basic/main.go

.PHONY: example-tracing
example-tracing:
	@echo "$(CYAN)Running tracing example...$(RESET)"
	@go run examples/distributed-tracing/main.go

# Development mode (requires air)
.PHONY: dev
dev:
	@echo "$(CYAN)Starting development server...$(RESET)"
	@if command -v air >$(DEV_NULL) 2>&1; then \
		air; \
	else \
		echo "$(YELLOW)⚠️  air not installed. Install with: go install github.com/cosmtrek/air@latest$(RESET)"; \
		exit 1; \
	fi

# Run scripts
.PHONY: run-script
run-script:
	@echo "$(CYAN)Running script: $(SCRIPT).sh$(RESET)"
	@chmod +x $(SCRIPTS_DIR)/$(SCRIPT).sh 2>/dev/null || true
	@bash $(SCRIPTS_DIR)/$(SCRIPT).sh

# Security scan
.PHONY: security
security:
	@echo "$(CYAN)Running security scan...$(RESET)"
	@if command -v govulncheck >$(DEV_NULL) 2>&1; then \
		govulncheck ./...; \
	else \
		echo "$(YELLOW)⚠️  govulncheck not found. Install with: go install golang.org/x/vuln/cmd/govulncheck@latest$(RESET)"; \
		exit 1; \
	fi

# List all modules
.PHONY: modules
modules:
	@echo "$(CYAN)Workspace modules:$(RESET)"
	@go list -m all

# Show module graph
.PHONY: mod-graph
mod-graph:
	@echo "$(CYAN)Module dependency graph:$(RESET)"
	@go mod graph

# Update dependencies
.PHONY: update-deps
update-deps:
	@echo "$(CYAN)Updating dependencies...$(RESET)"
	@go get -u ./...
	@go mod tidy
	@go work sync
	@echo "$(GREEN)✅ Dependencies updated$(RESET)"

# Verify workspace
.PHONY: verify
verify:
	@echo "$(CYAN)Verifying workspace...$(RESET)"
	@go work sync
	@go mod verify
	@echo "$(GREEN)✅ Workspace verified$(RESET)"
