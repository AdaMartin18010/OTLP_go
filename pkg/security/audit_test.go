// Copyright The OpenTelemetry Authors
// SPDX-License-Identifier: Apache-2.0

package security

import (
	"bytes"
	"context"
	"errors"
	"io"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewAuditEvent(t *testing.T) {
	event := NewAuditEvent(AuditEventAuth, "login", "user123", "api")

	assert.NotEmpty(t, event.ID)
	assert.WithinDuration(t, time.Now().UTC(), event.Timestamp, time.Second)
	assert.Equal(t, AuditEventAuth, event.Type)
	assert.Equal(t, "login", event.Action)
	assert.Equal(t, "user123", event.Actor)
	assert.Equal(t, "api", event.Resource)
	assert.Equal(t, AuditLevelInfo, event.Level)
	assert.Equal(t, "pending", event.Status)
	assert.NotNil(t, event.Details)
}

func TestAuditEventWithMethods(t *testing.T) {
	event := NewAuditEvent(AuditEventAuth, "login", "user", "api").
		WithLevel(AuditLevelWarning).
		WithStatus("success").
		WithDetail("ip", "192.168.1.1").
		WithDetail("method", "POST").
		WithSourceIP("192.168.1.1").
		WithUserAgent("Mozilla/5.0").
		WithSessionID("session-123").
		WithCorrelationID("corr-456")

	assert.Equal(t, AuditLevelWarning, event.Level)
	assert.Equal(t, "success", event.Status)
	assert.Equal(t, "192.168.1.1", event.SourceIP)
	assert.Equal(t, "Mozilla/5.0", event.UserAgent)
	assert.Equal(t, "session-123", event.SessionID)
	assert.Equal(t, "corr-456", event.CorrelationID)
	assert.Equal(t, "192.168.1.1", event.Details["ip"])
	assert.Equal(t, "POST", event.Details["method"])

	// Test WithError separately
	event2 := NewAuditEvent(AuditEventAuth, "login", "user", "api").
		WithError(errors.New("test error"))
	assert.Equal(t, "test error", event2.Error)
	assert.Equal(t, "failure", event2.Status)
}

func TestAuditEventWithErrorNil(t *testing.T) {
	event := NewAuditEvent(AuditEventAuth, "login", "user", "api").
		WithError(nil)

	assert.Empty(t, event.Error)
	assert.Equal(t, "pending", event.Status)
}

func TestAuditEventToJSON(t *testing.T) {
	event := NewAuditEvent(AuditEventAuth, "login", "user", "api").
		WithStatus("success")

	data, err := event.ToJSON()
	require.NoError(t, err)

	assert.Contains(t, string(data), `"id"`)
	assert.Contains(t, string(data), `"type":"auth"`)
	assert.Contains(t, string(data), `"action":"login"`)
	assert.Contains(t, string(data), `"actor":"user"`)
	assert.Contains(t, string(data), `"resource":"api"`)
}

func TestAuditEventString(t *testing.T) {
	event := NewAuditEvent(AuditEventAuth, "login", "user", "api")
	str := event.String()

	assert.Contains(t, str, `"id"`)
	assert.Contains(t, str, `"type":"auth"`)
}

func TestNewAuditLogger(t *testing.T) {
	t.Run("default logger", func(t *testing.T) {
		logger := NewAuditLogger()
		assert.NotNil(t, logger)
		assert.Equal(t, os.Stdout, logger.writer)
		assert.Equal(t, AuditLevelInfo, logger.minLevel)
		assert.True(t, logger.enabled)
		assert.NotNil(t, logger.sanitizer)
	})

	t.Run("with custom writer", func(t *testing.T) {
		var buf bytes.Buffer
		logger := NewAuditLogger(WithWriter(&buf))
		assert.Equal(t, &buf, logger.writer)
	})

	t.Run("with min level", func(t *testing.T) {
		logger := NewAuditLogger(WithMinLevel(AuditLevelError))
		assert.Equal(t, AuditLevelError, logger.minLevel)
	})

	t.Run("with enabled false", func(t *testing.T) {
		logger := NewAuditLogger(WithEnabled(false))
		assert.False(t, logger.enabled)
	})

	t.Run("with sanitizer", func(t *testing.T) {
		sanitizer := NewSanitizer(nil)
		logger := NewAuditLogger(WithSanitizer(sanitizer))
		assert.Equal(t, sanitizer, logger.sanitizer)
	})
}

func TestAuditLoggerLog(t *testing.T) {
	t.Run("successful log", func(t *testing.T) {
		var buf bytes.Buffer
		logger := NewAuditLogger(WithWriter(&buf))

		event := NewAuditEvent(AuditEventAuth, "login", "user", "api").WithStatus("success")
		err := logger.Log(event)

		require.NoError(t, err)
		output := buf.String()
		assert.Contains(t, output, `"type":"auth"`)
		assert.Contains(t, output, `"action":"login"`)
	})

	t.Run("disabled logger", func(t *testing.T) {
		var buf bytes.Buffer
		logger := NewAuditLogger(
			WithWriter(&buf),
			WithEnabled(false),
		)

		event := NewAuditEvent(AuditEventAuth, "login", "user", "api")
		err := logger.Log(event)

		require.NoError(t, err)
		assert.Empty(t, buf.String())
	})

	t.Run("level filtering", func(t *testing.T) {
		var buf bytes.Buffer
		logger := NewAuditLogger(
			WithWriter(&buf),
			WithMinLevel(AuditLevelWarning),
		)

		// Debug event should be filtered
		debugEvent := NewAuditEvent(AuditEventAuth, "debug-action", "user", "api").
			WithLevel(AuditLevelDebug)
		err := logger.Log(debugEvent)
		require.NoError(t, err)
		assert.Empty(t, buf.String())

		// Warning event should be logged
		warningEvent := NewAuditEvent(AuditEventAuth, "warning-action", "user", "api").
			WithLevel(AuditLevelWarning)
		err = logger.Log(warningEvent)
		require.NoError(t, err)
		assert.Contains(t, buf.String(), `"level":"warning"`)
	})

	t.Run("sanitizes output", func(t *testing.T) {
		var buf bytes.Buffer
		logger := NewAuditLogger(WithWriter(&buf))

		event := NewAuditEvent(AuditEventAuth, "login", "user@example.com", "api").
			WithStatus("success")
		err := logger.Log(event)

		require.NoError(t, err)
		output := buf.String()
		// Email should be sanitized
		assert.NotContains(t, output, "user@example.com")
	})
}

func TestAuditLoggerLogAsync(t *testing.T) {
	var buf bytes.Buffer
	logger := NewAuditLogger(WithWriter(&buf))

	event := NewAuditEvent(AuditEventAuth, "login", "user", "api").WithStatus("success")
	logger.LogAsync(event)

	// Wait for async operation
	time.Sleep(100 * time.Millisecond)

	output := buf.String()
	assert.Contains(t, output, `"type":"auth"`)
}

func TestAuditLoggerLogEvent(t *testing.T) {
	var buf bytes.Buffer
	logger := NewAuditLogger(WithWriter(&buf))

	err := logger.LogEvent(AuditEventAuth, "login", "user", "api", AuditLevelInfo, "success")
	require.NoError(t, err)

	output := buf.String()
	assert.Contains(t, output, `"type":"auth"`)
	assert.Contains(t, output, `"action":"login"`)
	assert.Contains(t, output, `"actor":"user"`)
	assert.Contains(t, output, `"resource":"api"`)
	assert.Contains(t, output, `"level":"info"`)
	assert.Contains(t, output, `"status":"success"`)
}

func TestAuditLoggerClose(t *testing.T) {
	t.Run("with closer", func(t *testing.T) {
		tempFile, err := os.CreateTemp("", "audit-*.log")
		require.NoError(t, err)
		tempFile.Close()

		file, err := os.OpenFile(tempFile.Name(), os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0600)
		require.NoError(t, err)

		logger := NewAuditLogger(WithWriter(file))
		err = logger.Close()
		require.NoError(t, err)
	})

	t.Run("without closer", func(t *testing.T) {
		logger := NewAuditLogger(WithWriter(&bytes.Buffer{}))
		err := logger.Close()
		require.NoError(t, err)
	})
}

func TestAuditLoggerIsEnabled(t *testing.T) {
	logger := NewAuditLogger(WithEnabled(true))
	assert.True(t, logger.IsEnabled())

	logger = NewAuditLogger(WithEnabled(false))
	assert.False(t, logger.IsEnabled())
}

func TestGenerateEventID(t *testing.T) {
	id1 := generateEventID()
	time.Sleep(1 * time.Millisecond) // Ensure different timestamp
	id2 := generateEventID()

	assert.NotEmpty(t, id1)
	assert.NotEmpty(t, id2)
	// Note: In rare cases, IDs could be identical if generated in same nanosecond
	// with same process ID, but with 1ms sleep they should be different
	assert.NotEqual(t, id1, id2)
}

func TestWithAuditLogger(t *testing.T) {
	logger := NewAuditLogger()
	ctx := WithAuditLogger(context.Background(), logger)

	retrieved, ok := GetAuditLogger(ctx)
	assert.True(t, ok)
	assert.Equal(t, logger, retrieved)
}

func TestGetAuditLogger(t *testing.T) {
	t.Run("exists", func(t *testing.T) {
		logger := NewAuditLogger()
		ctx := WithAuditLogger(context.Background(), logger)

		retrieved, ok := GetAuditLogger(ctx)
		assert.True(t, ok)
		assert.Equal(t, logger, retrieved)
	})

	t.Run("not exists", func(t *testing.T) {
		retrieved, ok := GetAuditLogger(context.Background())
		assert.False(t, ok)
		assert.Nil(t, retrieved)
	})
}

func TestMustGetAuditLogger(t *testing.T) {
	t.Run("exists", func(t *testing.T) {
		logger := NewAuditLogger()
		ctx := WithAuditLogger(context.Background(), logger)

		retrieved := MustGetAuditLogger(ctx)
		assert.Equal(t, logger, retrieved)
	})

	t.Run("panic on not exists", func(t *testing.T) {
		assert.Panics(t, func() {
			MustGetAuditLogger(context.Background())
		})
	})
}

func TestLogFromContext(t *testing.T) {
	t.Run("success", func(t *testing.T) {
		var buf bytes.Buffer
		logger := NewAuditLogger(WithWriter(&buf))
		ctx := WithAuditLogger(context.Background(), logger)

		event := NewAuditEvent(AuditEventAuth, "login", "user", "api")
		err := LogFromContext(ctx, event)

		require.NoError(t, err)
		assert.Contains(t, buf.String(), `"type":"auth"`)
	})

	t.Run("no logger", func(t *testing.T) {
		event := NewAuditEvent(AuditEventAuth, "login", "user", "api")
		err := LogFromContext(context.Background(), event)

		assert.Error(t, err)
		assert.Contains(t, err.Error(), "no audit logger in context")
	})
}

func TestFileAuditLogger(t *testing.T) {
	tempDir := t.TempDir()
	logPath := filepath.Join(tempDir, "audit.log")

	logger, err := FileAuditLogger(logPath)
	require.NoError(t, err)
	assert.NotNil(t, logger)

	event := NewAuditEvent(AuditEventAuth, "login", "user", "api").WithStatus("success")
	err = logger.Log(event)
	require.NoError(t, err)

	err = logger.Close()
	require.NoError(t, err)

	// Verify file contents
	content, err := os.ReadFile(logPath)
	require.NoError(t, err)
	assert.Contains(t, string(content), `"type":"auth"`)
}

func TestFileAuditLoggerError(t *testing.T) {
	// Try to create logger in non-existent directory with bad permissions
	logger, err := FileAuditLogger("/nonexistent/path/audit.log")
	assert.Error(t, err)
	assert.Nil(t, logger)
}

func TestMultiAuditLogger(t *testing.T) {
	var buf1, buf2 bytes.Buffer

	logger := MultiAuditLogger(&buf1, &buf2)
	assert.NotNil(t, logger)

	event := NewAuditEvent(AuditEventAuth, "login", "user", "api").WithStatus("success")
	err := logger.Log(event)
	require.NoError(t, err)

	// Both buffers should have the output
	assert.Contains(t, buf1.String(), `"type":"auth"`)
	assert.Contains(t, buf2.String(), `"type":"auth"`)
}

func TestNullAuditLogger(t *testing.T) {
	logger := NullAuditLogger()
	assert.NotNil(t, logger)
	assert.False(t, logger.IsEnabled())

	event := NewAuditEvent(AuditEventAuth, "login", "user", "api")
	err := logger.Log(event)
	require.NoError(t, err) // Should not error, just discard
}

func TestAuditFilter(t *testing.T) {
	t.Run("empty filter matches all", func(t *testing.T) {
		filter := NewAuditFilter()
		event := NewAuditEvent(AuditEventAuth, "login", "user", "api")
		assert.True(t, filter.Match(event))
	})

	t.Run("filter by type", func(t *testing.T) {
		filter := NewAuditFilter().WithTypes(AuditEventAuth, AuditEventAccess)

		authEvent := NewAuditEvent(AuditEventAuth, "login", "user", "api")
		assert.True(t, filter.Match(authEvent))

		systemEvent := NewAuditEvent(AuditEventSystem, "startup", "system", "server")
		assert.False(t, filter.Match(systemEvent))
	})

	t.Run("filter by level", func(t *testing.T) {
		filter := NewAuditFilter().WithLevels(AuditLevelWarning, AuditLevelError)

		warningEvent := NewAuditEvent(AuditEventAuth, "failed", "user", "api").
			WithLevel(AuditLevelWarning)
		assert.True(t, filter.Match(warningEvent))

		infoEvent := NewAuditEvent(AuditEventAuth, "login", "user", "api").
			WithLevel(AuditLevelInfo)
		assert.False(t, filter.Match(infoEvent))
	})

	t.Run("filter by actor", func(t *testing.T) {
		filter := NewAuditFilter().WithActors("admin", "system")

		adminEvent := NewAuditEvent(AuditEventAuth, "login", "admin", "api")
		assert.True(t, filter.Match(adminEvent))

		userEvent := NewAuditEvent(AuditEventAuth, "login", "user123", "api")
		assert.False(t, filter.Match(userEvent))
	})

	t.Run("combined filters", func(t *testing.T) {
		filter := NewAuditFilter().
			WithTypes(AuditEventAuth).
			WithLevels(AuditLevelError).
			WithActors("admin")

		// Matches all criteria
		matchingEvent := NewAuditEvent(AuditEventAuth, "failed", "admin", "api").
			WithLevel(AuditLevelError)
		assert.True(t, filter.Match(matchingEvent))

		// Wrong type
		wrongType := NewAuditEvent(AuditEventSystem, "failed", "admin", "api").
			WithLevel(AuditLevelError)
		assert.False(t, filter.Match(wrongType))

		// Wrong level
		wrongLevel := NewAuditEvent(AuditEventAuth, "failed", "admin", "api").
			WithLevel(AuditLevelWarning)
		assert.False(t, filter.Match(wrongLevel))

		// Wrong actor
		wrongActor := NewAuditEvent(AuditEventAuth, "failed", "user", "api").
			WithLevel(AuditLevelError)
		assert.False(t, filter.Match(wrongActor))
	})
}

func TestShouldLog(t *testing.T) {
	logger := NewAuditLogger(WithMinLevel(AuditLevelWarning))

	assert.False(t, logger.shouldLog(AuditLevelDebug))
	assert.False(t, logger.shouldLog(AuditLevelInfo))
	assert.True(t, logger.shouldLog(AuditLevelWarning))
	assert.True(t, logger.shouldLog(AuditLevelError))
	assert.True(t, logger.shouldLog(AuditLevelCritical))
}

func TestAuditLoggerSanitizeEvent(t *testing.T) {
	var buf bytes.Buffer
	logger := NewAuditLogger(WithWriter(&buf))

	event := &AuditEvent{
		ID:        "test-id",
		Timestamp: time.Now(),
		Type:      AuditEventAuth,
		Action:    "login",
		Actor:     "user@example.com",
		Resource:  "api",
		Level:     AuditLevelInfo,
		Status:    "success",
		Error:     "error for user@example.com",
		Details: map[string]interface{}{
			"email": "detail@example.com",
		},
	}

	sanitized := logger.sanitizeEvent(event)

	// Sensitive data should be sanitized
	assert.NotContains(t, sanitized.Actor, "user@example.com")
	assert.NotContains(t, sanitized.Error, "user@example.com")
}

// Verify interface implementations
var _ io.Writer = &bytes.Buffer{}
