// Copyright The OpenTelemetry Authors
// SPDX-License-Identifier: Apache-2.0

package security

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"sync"
	"time"
)

// AuditLevel represents the severity level of an audit event.
type AuditLevel string

const (
	// AuditLevelDebug is for detailed debugging information.
	AuditLevelDebug AuditLevel = "debug"
	// AuditLevelInfo is for general informational events.
	AuditLevelInfo AuditLevel = "info"
	// AuditLevelWarning is for warning events.
	AuditLevelWarning AuditLevel = "warning"
	// AuditLevelError is for error events.
	AuditLevelError AuditLevel = "error"
	// AuditLevelCritical is for critical security events.
	AuditLevelCritical AuditLevel = "critical"
)

// AuditEventType represents the type of audit event.
type AuditEventType string

const (
	// AuditEventAuth represents authentication events.
	AuditEventAuth AuditEventType = "auth"
	// AuditEventAccess represents access control events.
	AuditEventAccess AuditEventType = "access"
	// AuditEventData represents data-related events.
	AuditEventData AuditEventType = "data"
	// AuditEventConfig represents configuration change events.
	AuditEventConfig AuditEventType = "config"
	// AuditEventSecurity represents security-related events.
	AuditEventSecurity AuditEventType = "security"
	// AuditEventSystem represents system events.
	AuditEventSystem AuditEventType = "system"
)

// AuditEvent represents a single audit event.
type AuditEvent struct {
	// ID is a unique identifier for the event.
	ID string `json:"id"`
	// Timestamp is when the event occurred.
	Timestamp time.Time `json:"timestamp"`
	// Level is the severity level.
	Level AuditLevel `json:"level"`
	// Type is the event type.
	Type AuditEventType `json:"type"`
	// Action describes what happened.
	Action string `json:"action"`
	// Actor is the entity that performed the action.
	Actor string `json:"actor"`
	// Resource is the target of the action.
	Resource string `json:"resource"`
	// Status indicates success or failure.
	Status string `json:"status"`
	// Details contains additional event details.
	Details map[string]interface{} `json:"details,omitempty"`
	// SourceIP is the IP address of the actor.
	SourceIP string `json:"source_ip,omitempty"`
	// UserAgent is the user agent string.
	UserAgent string `json:"user_agent,omitempty"`
	// SessionID is the session identifier.
	SessionID string `json:"session_id,omitempty"`
	// CorrelationID links related events.
	CorrelationID string `json:"correlation_id,omitempty"`
	// Error contains error information if the action failed.
	Error string `json:"error,omitempty"`
}

// NewAuditEvent creates a new audit event with default values.
//
// Example:
//
//	event := security.NewAuditEvent(
//	    security.AuditEventAuth,
//	    "login",
//	    "user123",
//	    "api",
//	)
func NewAuditEvent(eventType AuditEventType, action, actor, resource string) *AuditEvent {
	return &AuditEvent{
		ID:        generateEventID(),
		Timestamp: time.Now().UTC(),
		Type:      eventType,
		Action:    action,
		Actor:     actor,
		Resource:  resource,
		Level:     AuditLevelInfo,
		Status:    "pending",
		Details:   make(map[string]interface{}),
	}
}

// WithLevel sets the audit level.
func (e *AuditEvent) WithLevel(level AuditLevel) *AuditEvent {
	e.Level = level
	return e
}

// WithStatus sets the status.
func (e *AuditEvent) WithStatus(status string) *AuditEvent {
	e.Status = status
	return e
}

// WithDetail adds a detail to the event.
func (e *AuditEvent) WithDetail(key string, value interface{}) *AuditEvent {
	if e.Details == nil {
		e.Details = make(map[string]interface{})
	}
	e.Details[key] = value
	return e
}

// WithSourceIP sets the source IP.
func (e *AuditEvent) WithSourceIP(ip string) *AuditEvent {
	e.SourceIP = ip
	return e
}

// WithUserAgent sets the user agent.
func (e *AuditEvent) WithUserAgent(ua string) *AuditEvent {
	e.UserAgent = ua
	return e
}

// WithSessionID sets the session ID.
func (e *AuditEvent) WithSessionID(id string) *AuditEvent {
	e.SessionID = id
	return e
}

// WithCorrelationID sets the correlation ID.
func (e *AuditEvent) WithCorrelationID(id string) *AuditEvent {
	e.CorrelationID = id
	return e
}

// WithError sets the error message.
func (e *AuditEvent) WithError(err error) *AuditEvent {
	if err != nil {
		e.Error = err.Error()
		e.Status = "failure"
	}
	return e
}

// ToJSON converts the event to JSON.
func (e *AuditEvent) ToJSON() ([]byte, error) {
	return json.Marshal(e)
}

// String returns a string representation of the event.
func (e *AuditEvent) String() string {
	data, err := e.ToJSON()
	if err != nil {
		return fmt.Sprintf("AuditEvent{ID: %s, Error: %v}", e.ID, err)
	}
	return string(data)
}

// AuditLogger provides audit logging capabilities.
type AuditLogger struct {
	writer    io.Writer
	minLevel  AuditLevel
	enabled   bool
	sanitizer *Sanitizer
	mu        sync.RWMutex
}

// AuditLoggerOption is a functional option for configuring the audit logger.
type AuditLoggerOption func(*AuditLogger)

// WithWriter sets the output writer for the audit logger.
func WithWriter(w io.Writer) AuditLoggerOption {
	return func(l *AuditLogger) {
		l.writer = w
	}
}

// WithMinLevel sets the minimum log level.
func WithMinLevel(level AuditLevel) AuditLoggerOption {
	return func(l *AuditLogger) {
		l.minLevel = level
	}
}

// WithEnabled enables or disables the audit logger.
func WithEnabled(enabled bool) AuditLoggerOption {
	return func(l *AuditLogger) {
		l.enabled = enabled
	}
}

// WithSanitizer sets the sanitizer for the audit logger.
func WithSanitizer(s *Sanitizer) AuditLoggerOption {
	return func(l *AuditLogger) {
		l.sanitizer = s
	}
}

// NewAuditLogger creates a new audit logger.
//
// Example:
//
//	file, _ := os.Create("audit.log")
//	logger := security.NewAuditLogger(
//	    security.WithWriter(file),
//	    security.WithMinLevel(security.AuditLevelInfo),
//	)
func NewAuditLogger(opts ...AuditLoggerOption) *AuditLogger {
	logger := &AuditLogger{
		writer:    os.Stdout,
		minLevel:  AuditLevelInfo,
		enabled:   true,
		sanitizer: NewSanitizer(nil),
	}

	for _, opt := range opts {
		opt(logger)
	}

	return logger
}

// Log logs an audit event.
//
// Example:
//
//	event := security.NewAuditEvent(
//	    security.AuditEventAuth,
//	    "login",
//	    "user123",
//	    "api",
//	).WithStatus("success")
//	err := logger.Log(event)
func (l *AuditLogger) Log(event *AuditEvent) error {
	if !l.isEnabled() {
		return nil
	}

	if !l.shouldLog(event.Level) {
		return nil
	}

	// Sanitize sensitive data in the event
	sanitizedEvent := l.sanitizeEvent(event)

	data, err := sanitizedEvent.ToJSON()
	if err != nil {
		return fmt.Errorf("failed to marshal audit event: %w", err)
	}

	l.mu.Lock()
	defer l.mu.Unlock()

	_, err = fmt.Fprintln(l.writer, string(data))
	if err != nil {
		return fmt.Errorf("failed to write audit event: %w", err)
	}

	return nil
}

// LogAsync logs an audit event asynchronously.
func (l *AuditLogger) LogAsync(event *AuditEvent) {
	go func() {
		_ = l.Log(event)
	}()
}

// LogEvent creates and logs an event in one call.
//
// Example:
//
//	err := logger.LogEvent(
//	    security.AuditEventAuth,
//	    "login",
//	    "user123",
//	    "api",
//	    security.AuditLevelInfo,
//	    "success",
//	)
func (l *AuditLogger) LogEvent(eventType AuditEventType, action, actor, resource string, level AuditLevel, status string) error {
	event := NewAuditEvent(eventType, action, actor, resource).
		WithLevel(level).
		WithStatus(status)
	return l.Log(event)
}

// Close closes the audit logger.
func (l *AuditLogger) Close() error {
	if closer, ok := l.writer.(io.Closer); ok {
		return closer.Close()
	}
	return nil
}

// IsEnabled returns whether the logger is enabled.
func (l *AuditLogger) IsEnabled() bool {
	return l.isEnabled()
}

// isEnabled returns whether the logger is enabled (thread-safe).
func (l *AuditLogger) isEnabled() bool {
	l.mu.RLock()
	defer l.mu.RUnlock()
	return l.enabled
}

// shouldLog checks if the given level should be logged.
func (l *AuditLogger) shouldLog(level AuditLevel) bool {
	levelOrder := map[AuditLevel]int{
		AuditLevelDebug:    0,
		AuditLevelInfo:     1,
		AuditLevelWarning:  2,
		AuditLevelError:    3,
		AuditLevelCritical: 4,
	}

	return levelOrder[level] >= levelOrder[l.minLevel]
}

// sanitizeEvent sanitizes sensitive data in an audit event.
func (l *AuditLogger) sanitizeEvent(event *AuditEvent) *AuditEvent {
	if l.sanitizer == nil {
		return event
	}

	sanitized := *event
	sanitized.Actor = l.sanitizer.Sanitize(event.Actor)
	sanitized.Resource = l.sanitizer.Sanitize(event.Resource)
	sanitized.Error = l.sanitizer.Sanitize(event.Error)

	if event.Details != nil {
		sanitized.Details = l.sanitizer.SanitizeMap(event.Details)
	}

	return &sanitized
}

// GenerateEventID generates a unique event ID.
func generateEventID() string {
	return fmt.Sprintf("%d-%d", time.Now().UnixNano(), os.Getpid())
}

// AuditContextKey is the key for storing audit logger in context.
type auditContextKey struct{}

// WithAuditLogger adds an audit logger to the context.
//
// Example:
//
//	logger := security.NewAuditLogger()
//	ctx := security.WithAuditLogger(context.Background(), logger)
func WithAuditLogger(ctx context.Context, logger *AuditLogger) context.Context {
	return context.WithValue(ctx, auditContextKey{}, logger)
}

// GetAuditLogger retrieves the audit logger from context.
func GetAuditLogger(ctx context.Context) (*AuditLogger, bool) {
	logger, ok := ctx.Value(auditContextKey{}).(*AuditLogger)
	return logger, ok
}

// MustGetAuditLogger retrieves the audit logger from context, panics if not found.
func MustGetAuditLogger(ctx context.Context) *AuditLogger {
	logger, ok := GetAuditLogger(ctx)
	if !ok {
		panic("audit logger not found in context")
	}
	return logger
}

// LogFromContext logs an event using the audit logger from context.
//
// Example:
//
//	event := security.NewAuditEvent(security.AuditEventAuth, "login", "user", "api")
//	err := security.LogFromContext(ctx, event)
func LogFromContext(ctx context.Context, event *AuditEvent) error {
	logger, ok := GetAuditLogger(ctx)
	if !ok {
		return fmt.Errorf("no audit logger in context")
	}
	return logger.Log(event)
}

// FileAuditLogger creates an audit logger that writes to a file.
//
// Example:
//
//	logger, err := security.FileAuditLogger("/var/log/audit.log")
//	if err != nil {
//	    log.Fatal(err)
//	}
func FileAuditLogger(filepath string) (*AuditLogger, error) {
	file, err := os.OpenFile(filepath, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0600)
	if err != nil {
		return nil, fmt.Errorf("failed to open audit log file: %w", err)
	}

	return NewAuditLogger(
		WithWriter(file),
		WithMinLevel(AuditLevelInfo),
	), nil
}

// MultiAuditLogger creates an audit logger that writes to multiple destinations.
//
// Example:
//
//	file, _ := os.Create("audit.log")
//	logger := security.MultiAuditLogger(os.Stdout, file)
func MultiAuditLogger(writers ...io.Writer) *AuditLogger {
	return NewAuditLogger(WithWriter(io.MultiWriter(writers...)))
}

// NullAuditLogger creates a no-op audit logger for testing.
func NullAuditLogger() *AuditLogger {
	return NewAuditLogger(
		WithWriter(io.Discard),
		WithEnabled(false),
	)
}

// AuditFilter provides filtering capabilities for audit events.
type AuditFilter struct {
	types  []AuditEventType
	levels []AuditLevel
	actors []string
}

// NewAuditFilter creates a new audit filter.
func NewAuditFilter() *AuditFilter {
	return &AuditFilter{}
}

// WithTypes filters by event types.
func (f *AuditFilter) WithTypes(types ...AuditEventType) *AuditFilter {
	f.types = types
	return f
}

// WithLevels filters by levels.
func (f *AuditFilter) WithLevels(levels ...AuditLevel) *AuditFilter {
	f.levels = levels
	return f
}

// WithActors filters by actors.
func (f *AuditFilter) WithActors(actors ...string) *AuditFilter {
	f.actors = actors
	return f
}

// Match checks if an event matches the filter.
func (f *AuditFilter) Match(event *AuditEvent) bool {
	if len(f.types) > 0 {
		found := false
		for _, t := range f.types {
			if event.Type == t {
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}

	if len(f.levels) > 0 {
		found := false
		for _, l := range f.levels {
			if event.Level == l {
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}

	if len(f.actors) > 0 {
		found := false
		for _, a := range f.actors {
			if event.Actor == a {
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}

	return true
}
