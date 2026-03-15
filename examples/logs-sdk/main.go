// Example: Logs SDK 使用示例
package main

import (
	"context"
	"log"

	"OTLP_go/pkg/logs"

	"go.opentelemetry.io/otel/attribute"
)

func main() {
	// 初始化 LoggerProvider
	provider, err := logs.InitLoggerProvider(&logs.LoggerConfig{
		Endpoint:       "localhost:4317",
		ServiceName:    "example-service",
		ServiceVersion: "1.0.0",
		Environment:    "production",
	})
	if err != nil {
		log.Fatalf("Failed to initialize logger: %v", err)
	}
	defer provider.Shutdown(context.Background())

	// 获取 Logger
	logger := provider.GetLogger("main")

	// 发送不同级别的日志
	ctx := context.Background()

	logger.Debug(ctx, "This is a debug message",
		attribute.String("component", "database"),
	)

	logger.Info(ctx, "Application started",
		attribute.String("version", "1.0.0"),
		attribute.Int("port", 8080),
	)

	logger.Warn(ctx, "High memory usage detected",
		attribute.Float64("memory_percent", 85.5),
	)

	logger.Error(ctx, "Failed to connect to database",
		attribute.String("error", "connection refused"),
		attribute.Int("retry_count", 3),
	)

	// 使用 WithAttributes 创建带默认属性的 Logger
	requestLogger := logger.WithAttributes(
		attribute.String("request_id", "req-12345"),
		attribute.String("user_id", "user-67890"),
	)

	requestLogger.Info(ctx, "Request processed",
		attribute.Int("duration_ms", 150),
		attribute.Int("status_code", 200),
	)

	// 确保所有日志被导出
	provider.ForceFlush(ctx)

	log.Println("Logs example completed")
}
