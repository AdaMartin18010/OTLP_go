# Logs SDK Example

This example demonstrates how to use the OTLP Go Logs SDK.

## Features

- Structured logging with attributes
- Multiple severity levels (Debug, Info, Warn, Error, Fatal)
- Batch processing for high performance
- Console exporter for development

## Run

```bash
go run main.go
```

## Output

```
[14:30:45.123] DEBUG This is a debug message [{component {4 0 database <nil>}}]
[14:30:45.124] INFO  Application started [{version {4 0 1.0.0 <nil>}} {port {2 8080  <nil>}}]
[14:30:45.125] WARN  High memory usage detected [{memory_percent {3 4620692027124481024  <nil>}}]
[14:30:45.126] ERROR Failed to connect to database [{error {4 0 connection refused <nil>}} {retry_count {2 3  <nil>}}]
[14:30:45.127] INFO  Request processed [{request_id {4 0 req-12345 <nil>}} {user_id {4 0 user-67890 <nil>}} {duration_ms {2 150  <nil>}} {status_code {2 200  <nil>}}]
```
