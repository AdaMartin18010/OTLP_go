.PHONY: all build test clean lint fmt vet coverage benchmark docker

# Default target
all: fmt vet build test

# Build all modules
build:
	@echo "Building all modules..."
	go build ./...
	go build OTLP_go/...

# Run all tests
test:
	@echo "Running tests..."
	go test -race ./...
	go test -race OTLP_go/...

# Run tests with coverage
coverage:
	@echo "Running tests with coverage..."
	go test -race -coverprofile=coverage.out ./...
	go tool cover -html=coverage.out -o coverage.html
	@echo "Coverage report generated: coverage.html"

# Run benchmarks
benchmark:
	@echo "Running benchmarks..."
	go test -bench=. -benchmem ./pkg/...

# Format code
fmt:
	@echo "Formatting code..."
	go fmt ./...

# Run go vet
vet:
	@echo "Running go vet..."
	go vet ./...

# Run linter (requires golangci-lint)
lint:
	@echo "Running linter..."
	golangci-lint run ./...

# Tidy all modules
tidy:
	@echo "Tidying modules..."
	go mod tidy
	go work sync

# Clean build artifacts
clean:
	@echo "Cleaning..."
	rm -f coverage.out coverage.html
	go clean -cache

# Build Docker image
docker:
	@echo "Building Docker image..."
	docker build -t otlp-go:latest .

# Run example
example-logs:
	@echo "Running logs example..."
	go run examples/logs-sdk/main.go

# Development mode with hot reload (requires air)
dev:
	@echo "Starting development server..."
	air

# Install dependencies
install:
	@echo "Installing dependencies..."
	go mod download
	go work sync

# Check project health
check:
	@echo "Checking project health..."
	@echo "1. Build check..."
	go build ./...
	@echo "2. Test check..."
	go test ./...
	@echo "3. Format check..."
	@test -z "$$(gofmt -l .)" || (echo "Code needs formatting:" && gofmt -l . && exit 1)
	@echo "4. Vet check..."
	go vet ./...
	@echo "✅ All checks passed!"

# Generate documentation
docs:
	@echo "Generating documentation..."
	godoc -http=:6060

# CI target (runs in CI/CD)
ci: fmt vet build test coverage
	@echo "CI pipeline completed"
