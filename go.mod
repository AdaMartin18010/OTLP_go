module OTLP_go

go 1.26

require (
	github.com/stretchr/testify v1.11.1
	go.opentelemetry.io/contrib/detectors/gcp v1.39.0
	go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp v0.46.1
	go.opentelemetry.io/otel v1.42.0
	go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc v1.42.0
	go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc v1.42.0
	go.opentelemetry.io/otel/exporters/stdout/stdouttrace v1.32.0
	go.opentelemetry.io/otel/sdk v1.42.0
	go.opentelemetry.io/otel/sdk/metric v1.42.0
	go.opentelemetry.io/otel/trace v1.42.0
	go.opentelemetry.io/proto/otlp v1.9.0
	go.uber.org/automaxprocs v1.6.0
	go.uber.org/goleak v1.3.0
	golang.org/x/sync v0.14.0
	google.golang.org/grpc v1.79.2
	google.golang.org/protobuf v1.36.6
)

require (
	cloud.google.com/go/compute/metadata v0.6.0 // indirect
	github.com/GoogleCloudPlatform/opentelemetry-operations-go/detectors/gcp v1.30.0 // indirect
	github.com/cenkalti/backoff/v4 v4.3.0 // indirect
	github.com/davecgh/go-spew v1.1.1 // indirect
	github.com/felixge/httpsnoop v1.0.4 // indirect
	github.com/go-logr/logr v1.4.2 // indirect
	github.com/go-logr/stdr v1.2.2 // indirect
	github.com/google/uuid v1.6.0 // indirect
	github.com/grpc-ecosystem/grpc-gateway/v2 v2.26.3 // indirect
	github.com/pmezard/go-difflib v1.0.0 // indirect
	go.opentelemetry.io/auto/sdk v1.1.0 // indirect
	go.opentelemetry.io/otel/log v0.11.0 // indirect
	go.opentelemetry.io/otel/metric v1.42.0 // indirect
	go.opentelemetry.io/otel/sdk/log v0.11.0 // indirect
	golang.org/x/net v0.51.0 // indirect
	golang.org/x/sys v0.41.0 // indirect
	golang.org/x/text v0.34.0 // indirect
	gopkg.in/yaml.v3 v3.0.1 // indirect
)

