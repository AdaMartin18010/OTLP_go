module github.com/OTLP_go/examples/complete

go 1.26

require (
	github.com/OTLP_go/pkg/config v0.0.0
	github.com/OTLP_go/pkg/errors v0.0.0
	github.com/OTLP_go/pkg/logs v0.0.0
	github.com/OTLP_go/pkg/otel v0.0.0
	github.com/OTLP_go/pkg/performance v0.0.0
	github.com/OTLP_go/pkg/resource v0.0.0
	github.com/OTLP_go/pkg/shutdown v0.0.0
)

replace (
	github.com/OTLP_go/pkg/config => ../../pkg/config
	github.com/OTLP_go/pkg/errors => ../../pkg/errors
	github.com/OTLP_go/pkg/logs => ../../pkg/logs
	github.com/OTLP_go/pkg/otel => ../../pkg/otel
	github.com/OTLP_go/pkg/performance => ../../pkg/performance
	github.com/OTLP_go/pkg/resource => ../../pkg/resource
	github.com/OTLP_go/pkg/shutdown => ../../pkg/shutdown
)
