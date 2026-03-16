module github.com/OTLP_go/examples/quickstart

go 1.26

require (
	github.com/OTLP_go/pkg/logs v0.0.0
	github.com/OTLP_go/pkg/otel v0.0.0
)

replace (
	github.com/OTLP_go/pkg/logs => ../../pkg/logs
	github.com/OTLP_go/pkg/otel => ../../pkg/otel
)
