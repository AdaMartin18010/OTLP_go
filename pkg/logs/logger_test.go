package logs

import (
	"bytes"
	"context"
	"encoding/json"
	"strings"
	"sync"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
)

func TestSeverityNumber_String(t *testing.T) {
	tests := []struct {
		severity SeverityNumber
		expected string
	}{
		{SeverityTrace, "TRACE"},
		{SeverityDebug, "DEBUG"},
		{SeverityInfo, "INFO"},
		{SeverityWarn, "WARN"},
		{SeverityError, "ERROR"},
		{SeverityFatal, "FATAL"},
		{SeverityNumber(999), "UNKNOWN"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			if got := tt.severity.String(); got != tt.expected {
				t.Errorf("SeverityNumber.String() = %v, want %v", got, tt.expected)
			}
		})
	}
}

func TestSeverityNumber_ToLevel(t *testing.T) {
	tests := []struct {
		severity SeverityNumber
		expected Level
	}{
		{SeverityTrace, LevelTrace},
		{SeverityDebug, LevelDebug},
		{SeverityInfo, LevelInfo},
		{SeverityWarn, LevelWarn},
		{SeverityError, LevelError},
		{SeverityFatal, LevelFatal},
		{SeverityNumber(999), LevelInfo},
	}

	for _, tt := range tests {
		t.Run(tt.severity.String(), func(t *testing.T) {
			if got := tt.severity.ToLevel(); got != tt.expected {
				t.Errorf("SeverityNumber.ToLevel() = %v, want %v", got, tt.expected)
			}
		})
	}
}

func TestNewLogger(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	if logger == nil {
		t.Fatal("NewLogger() returned nil")
	}
	if logger.GetLevel() != LevelInfo {
		t.Errorf("GetLevel() = %v, want LevelInfo", logger.GetLevel())
	}
}

func TestLogger_WithLevel(t *testing.T) {
	var buf bytes.Buffer
	logger := New("test", WithOutput(&buf), WithLevel(LevelWarn))

	if logger.GetLevel() != LevelWarn {
		t.Errorf("GetLevel() = %v, want LevelWarn", logger.GetLevel())
	}
}

func TestLogger_SetLevel(t *testing.T) {
	logger := NewLogger(Config{Level: LevelInfo})

	logger.SetLevel(LevelDebug)
	if logger.GetLevel() != LevelDebug {
		t.Errorf("After SetLevel(Debug), GetLevel() = %v", logger.GetLevel())
	}
}

func TestLogger_Enabled(t *testing.T) {
	logger := NewLogger(Config{Level: LevelWarn})

	if logger.Enabled(LevelDebug) {
		t.Error("Enabled(Debug) should be false when level is Warn")
	}
	if !logger.Enabled(LevelError) {
		t.Error("Enabled(Error) should be true when level is Warn")
	}
}

func TestLogger_Named(t *testing.T) {
	logger := New("parent")
	child := logger.Named("child")
	grandchild := child.Named("grandchild")

	// The named logger should have inherited properties
	if grandchild.GetLevel() != logger.GetLevel() {
		t.Error("Named logger should inherit level")
	}
}

func TestLogger_With(t *testing.T) {
	logger := NewLogger(Config{Level: LevelInfo})
	loggerWithFields := logger.With(String("key", "value"))

	// Original logger should not have the field
	if len(logger.fields) != 0 {
		t.Error("Original logger should not have fields")
	}

	// New logger should have the field
	if len(loggerWithFields.fields) != 1 {
		t.Errorf("With() logger should have 1 field, got %d", len(loggerWithFields.fields))
	}
}

func TestLogger_Info(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	logger.Info("test message", String("key", "value"))

	output := buf.String()
	if !strings.Contains(output, "test message") {
		t.Errorf("Log output missing message: %s", output)
	}
	if !strings.Contains(output, "key") {
		t.Errorf("Log output missing field key: %s", output)
	}
	if !strings.Contains(output, "value") {
		t.Errorf("Log output missing field value: %s", output)
	}
}

func TestLogger_Debug_Disabled(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo, // Debug is disabled
		Output: &buf,
	})

	logger.Debug("debug message")

	if buf.Len() > 0 {
		t.Errorf("Debug message should not be logged when level is Info: %s", buf.String())
	}
}

func TestLogger_LevelMethods(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelTrace,
		Output: &buf,
	})

	tests := []struct {
		name   string
		fn     func()
		level  string
	}{
		{"Trace", func() { logger.Trace("trace msg") }, "TRACE"},
		{"Debug", func() { logger.Debug("debug msg") }, "DEBUG"},
		{"Info", func() { logger.Info("info msg") }, "INFO"},
		{"Warn", func() { logger.Warn("warn msg") }, "WARN"},
		{"Error", func() { logger.Error("error msg") }, "ERROR"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			buf.Reset()
			tt.fn()
			if !strings.Contains(buf.String(), tt.level) {
				t.Errorf("Expected level %s in output: %s", tt.level, buf.String())
			}
		})
	}
}

func TestLogger_ContextMethods(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	ctx := context.Background()

	tests := []struct {
		name string
		fn   func()
	}{
		{"DebugContext", func() { logger.DebugContext(ctx, "debug") }},
		{"InfoContext", func() { logger.InfoContext(ctx, "info") }},
		{"WarnContext", func() { logger.WarnContext(ctx, "warn") }},
		{"ErrorContext", func() { logger.ErrorContext(ctx, "error") }},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			buf.Reset()
			tt.fn()
			if buf.Len() == 0 {
				t.Errorf("%s did not produce output", tt.name)
			}
		})
	}
}

func TestLogger_Emit(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	ctx := context.Background()
	logger.Emit(ctx, SeverityInfo, "emit message", attribute.String("key", "value"))

	if !strings.Contains(buf.String(), "emit message") {
		t.Errorf("Emit did not log message: %s", buf.String())
	}
}

func TestSamplerFunc(t *testing.T) {
	sampler := SamplerFunc(func(record *LogRecord) bool {
		return record.Severity == SeverityError
	})

	errorRecord := &LogRecord{Severity: SeverityError}
	infoRecord := &LogRecord{Severity: SeverityInfo}

	if !sampler.ShouldSample(errorRecord) {
		t.Error("ShouldSample should return true for error")
	}
	if sampler.ShouldSample(infoRecord) {
		t.Error("ShouldSample should return false for info")
	}
}

func TestAlwaysSample(t *testing.T) {
	record := &LogRecord{Severity: SeverityInfo}
	if !AlwaysSample.ShouldSample(record) {
		t.Error("AlwaysSample should always return true")
	}
}

func TestNeverSample(t *testing.T) {
	record := &LogRecord{Severity: SeverityFatal}
	if NeverSample.ShouldSample(record) {
		t.Error("NeverSample should always return false")
	}
}

func TestProbabilitySampler(t *testing.T) {
	t.Run("Zero", func(t *testing.T) {
		sampler := ProbabilitySampler(0)
		record := &LogRecord{Severity: SeverityInfo}
		if sampler.ShouldSample(record) {
			t.Error("ProbabilitySampler(0) should never sample")
		}
	})

	t.Run("One", func(t *testing.T) {
		sampler := ProbabilitySampler(1)
		record := &LogRecord{Severity: SeverityInfo}
		if !sampler.ShouldSample(record) {
			t.Error("ProbabilitySampler(1) should always sample")
		}
	})

	t.Run("FiftyPercent", func(t *testing.T) {
		sampler := ProbabilitySampler(0.5)
		// Just verify it doesn't panic and returns consistent results
		record := &LogRecord{
			Timestamp: time.Now(),
			Body:      "test",
		}
		_ = sampler.ShouldSample(record)
	})
}

func TestRateLimiter(t *testing.T) {
	limiter := NewRateLimiter(100 * time.Millisecond)

	record := &LogRecord{Severity: SeverityInfo}

	// First call should succeed
	if !limiter.ShouldSample(record) {
		t.Error("First call should sample")
	}

	// Immediate second call should fail
	if limiter.ShouldSample(record) {
		t.Error("Second immediate call should not sample")
	}
}

func TestRateLimiter_Concurrent(t *testing.T) {
	limiter := NewRateLimiter(10 * time.Millisecond)
	var wg sync.WaitGroup
	count := int32(0)

	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			record := &LogRecord{Severity: SeverityInfo}
			if limiter.ShouldSample(record) {
				count++
			}
		}()
	}

	wg.Wait()
	// Only one should succeed due to CAS
	if count != 1 {
		t.Errorf("Expected 1 sample, got %d", count)
	}
}

func TestNewJSONLogEncoder(t *testing.T) {
	encoder := NewJSONLogEncoder()
	if encoder == nil {
		t.Fatal("NewJSONLogEncoder() returned nil")
	}
}

func TestJSONEncoder_Encode(t *testing.T) {
	encoder := NewJSONLogEncoder()
	record := &LogRecord{
		Timestamp: time.Date(2024, 1, 1, 0, 0, 0, 0, time.UTC),
		Severity:  SeverityInfo,
		Body:      "test message",
	}
	fields := Fields{String("key", "value")}

	data, err := encoder.Encode(record, fields)
	if err != nil {
		t.Fatalf("Encode() error = %v", err)
	}

	output := string(data)
	if !strings.Contains(output, "test message") {
		t.Errorf("Encode() missing message: %s", output)
	}
	if !strings.Contains(output, "INFO") {
		t.Errorf("Encode() missing level: %s", output)
	}
}

func TestStdLogger(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})
	stdLogger := logger.StdLogger()

	tests := []struct {
		name string
		fn   func()
	}{
		{"Print", func() { stdLogger.Print("print message") }},
		{"Printf", func() { stdLogger.Printf("printf %s", "message") }},
		{"Println", func() { stdLogger.Println("println message") }},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			buf.Reset()
			tt.fn()
			if buf.Len() == 0 {
				t.Errorf("%s did not produce output", tt.name)
			}
		})
	}
}

func TestStdLogger_Panic(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})
	stdLogger := logger.StdLogger()

	t.Run("Panic", func(t *testing.T) {
		defer func() {
			if r := recover(); r == nil {
				t.Error("Panic() should have panicked")
			}
		}()
		stdLogger.Panic("panic message")
	})

	t.Run("Panicf", func(t *testing.T) {
		defer func() {
			if r := recover(); r == nil {
				t.Error("Panicf() should have panicked")
			}
		}()
		stdLogger.Panicf("panic %s", "message")
	})

	t.Run("Panicln", func(t *testing.T) {
		defer func() {
			if r := recover(); r == nil {
				t.Error("Panicln() should have panicked")
			}
		}()
		stdLogger.Panicln("panic message")
	})
}

func TestConsoleLogger(t *testing.T) {
	logger := NewConsoleLogger(LevelInfo)
	if logger == nil {
		t.Fatal("NewConsoleLogger() returned nil")
	}
}

func TestNopLogger(t *testing.T) {
	logger := NopLogger()
	if logger == nil {
		t.Fatal("NopLogger() returned nil")
	}
	if logger.Enabled(LevelFatal) {
		t.Error("NopLogger should not enable any level")
	}
}

func TestGlobalLogger(t *testing.T) {
	original := GetGlobalLogger()
	defer SetGlobalLogger(original)

	newLogger := NewLogger(Config{Level: LevelDebug})
	SetGlobalLogger(newLogger)

	if GetGlobalLogger() != newLogger {
		t.Error("SetGlobalLogger did not set the global logger")
	}

	if L() != newLogger {
		t.Error("L() did not return the global logger")
	}
}

func TestSugar(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})
	sugar := logger.Sugar()

	tests := []struct {
		name string
		fn   func()
	}{
		{"Debugf", func() { sugar.Debugf("debug %s", "message") }},
		{"Infof", func() { sugar.Infof("info %s", "message") }},
		{"Warnf", func() { sugar.Warnf("warn %s", "message") }},
		{"Errorf", func() { sugar.Errorf("error %s", "message") }},
		{"Debugw", func() { sugar.Debugw("debug", "key", "value") }},
		{"Infow", func() { sugar.Infow("info", "key", "value") }},
		{"Warnw", func() { sugar.Warnw("warn", "key", "value") }},
		{"Errorw", func() { sugar.Errorw("error", "key", "value") }},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			buf.Reset()
			tt.fn()
			// Note: Debug might be filtered based on level
		})
	}
}

func TestKVToFields(t *testing.T) {
	tests := []struct {
		name       string
		kv         []interface{}
		fieldCount int
	}{
		{"even pairs", []interface{}{"a", 1, "b", 2}, 2},
		{"odd pairs", []interface{}{"a", 1, "b"}, 2}, // adds "missing"
		{"non-string key", []interface{}{123, "value"}, 1},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			fields := kvToFields(tt.kv)
			if len(fields) != tt.fieldCount {
				t.Errorf("kvToFields() returned %d fields, want %d", len(fields), tt.fieldCount)
			}
		})
	}
}

func TestLogEntry_Parse(t *testing.T) {
	jsonData := `{
		"timestamp": "2024-01-01T00:00:00Z",
		"level": "INFO",
		"message": "test message",
		"logger": "test",
		"trace_id": "abc123",
		"span_id": "def456",
		"fields": {"key": "value"}
	}`

	entry, err := ParseLogEntry([]byte(jsonData))
	if err != nil {
		t.Fatalf("ParseLogEntry() error = %v", err)
	}

	if entry.Level != "INFO" {
		t.Errorf("Level = %v, want INFO", entry.Level)
	}
	if entry.Message != "test message" {
		t.Errorf("Message = %v, want 'test message'", entry.Message)
	}
}

func TestLoggerProvider(t *testing.T) {
	provider := NewLoggerProvider(nil)
	if provider == nil {
		t.Fatal("NewLoggerProvider() returned nil")
	}

	// Get logger
	logger1 := provider.GetLogger("test")
	logger2 := provider.GetLogger("test")

	// Should return same logger
	if logger1 != logger2 {
		t.Error("GetLogger should return cached logger")
	}

	// Get different logger
	logger3 := provider.GetLogger("other")
	if logger1 == logger3 {
		t.Error("GetLogger should return different loggers for different names")
	}

	// Shutdown
	ctx := context.Background()
	if err := provider.Shutdown(ctx); err != nil {
		t.Errorf("Shutdown() error = %v", err)
	}

	// Double shutdown should be safe
	if err := provider.Shutdown(ctx); err != nil {
		t.Errorf("Second Shutdown() error = %v", err)
	}
}

func TestLogger_Sync(t *testing.T) {
	logger := NewLogger(Config{Level: LevelInfo})
	if err := logger.Sync(); err != nil {
		t.Errorf("Sync() error = %v", err)
	}

	if err := logger.Shutdown(); err != nil {
		t.Errorf("Shutdown() error = %v", err)
	}
}

func TestLogger_Concurrent(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	var wg sync.WaitGroup
	for i := 0; i < 100; i++ {
		wg.Add(1)
		go func(n int) {
			defer wg.Done()
			logger.Info("concurrent", Int("n", n))
		}(i)
	}
	wg.Wait()

	// Count log entries
	count := strings.Count(buf.String(), "concurrent")
	if count != 100 {
		t.Errorf("Expected 100 log entries, got %d", count)
	}
}

func TestLogger_WithSampler(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:   LevelInfo,
		Output:  &buf,
		Sampler: NeverSample,
	})

	logger.Info("should not appear")
	if buf.Len() > 0 {
		t.Error("Log should not appear when using NeverSample")
	}
}

func TestLogRecord_JSONOutput(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	logger.Info("test message", String("key", "value"), Int("count", 42))

	output := buf.String()
	// Verify it's valid JSON
	var result map[string]interface{}
	if err := json.Unmarshal([]byte(output), &result); err != nil {
		t.Errorf("Output is not valid JSON: %v\nOutput: %s", err, output)
	}
}

func BenchmarkLogger_Info(b *testing.B) {
	logger := NopLogger()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			logger.Info("benchmark message", String("key", "value"))
		}
	})
}

func BenchmarkLogger_InfoWithSampler(b *testing.B) {
	logger := NewLogger(Config{
		Level:   LevelInfo,
		Sampler: AlwaysSample,
		Output:  &bytes.Buffer{},
	})
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			logger.Info("benchmark message", String("key", "value"))
		}
	})
}

func BenchmarkLogger_With(b *testing.B) {
	logger := NewLogger(Config{Level: LevelInfo})
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = logger.With(String("key", "value"))
	}
}

func BenchmarkLogger_Named(b *testing.B) {
	logger := NewLogger(Config{Level: LevelInfo})
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = logger.Named("child")
	}
}
