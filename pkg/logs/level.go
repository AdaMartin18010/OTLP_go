// Package logs provides OpenTelemetry Logs API implementation for the OTLP Go SDK.
//
// This file contains log level management functionality.
package logs

import (
	"fmt"
	"strings"
	"sync/atomic"
)

// Level represents a logging level.
type Level int32

const (
	// LevelTrace is the most verbose logging level.
	LevelTrace Level = iota
	// LevelDebug is for debugging information.
	LevelDebug
	// LevelInfo is for informational messages.
	LevelInfo
	// LevelWarn is for warning messages.
	LevelWarn
	// LevelError is for error messages.
	LevelError
	// LevelFatal is for fatal error messages.
	LevelFatal
	// LevelNone disables all logging.
	LevelNone
)

var levelNames = map[Level]string{
	LevelTrace: "TRACE",
	LevelDebug: "DEBUG",
	LevelInfo:  "INFO",
	LevelWarn:  "WARN",
	LevelError: "ERROR",
	LevelFatal: "FATAL",
	LevelNone:  "NONE",
}

var levelValues = map[string]Level{
	"TRACE": LevelTrace,
	"DEBUG": LevelDebug,
	"INFO":  LevelInfo,
	"WARN":  LevelWarn,
	"WARNING": LevelWarn,
	"ERROR": LevelError,
	"FATAL": LevelFatal,
	"NONE":  LevelNone,
}

// String returns the string representation of the level.
func (l Level) String() string {
	if name, ok := levelNames[l]; ok {
		return name
	}
	return fmt.Sprintf("LEVEL(%d)", l)
}

// Enabled returns true if the given level is enabled at the current level.
// A level is enabled if it is greater than or equal to the current level.
func (l Level) Enabled(other Level) bool {
	return other >= l
}

// MarshalJSON implements json.Marshaler.
func (l Level) MarshalJSON() ([]byte, error) {
	return []byte(`"` + l.String() + `"`), nil
}

// UnmarshalJSON implements json.Unmarshaler.
func (l *Level) UnmarshalJSON(data []byte) error {
	str := strings.Trim(string(data), `"`)
	if level, ok := levelValues[strings.ToUpper(str)]; ok {
		*l = level
		return nil
	}
	return fmt.Errorf("unknown log level: %s", str)
}

// MarshalText implements encoding.TextMarshaler.
func (l Level) MarshalText() ([]byte, error) {
	return []byte(l.String()), nil
}

// UnmarshalText implements encoding.TextUnmarshaler.
func (l *Level) UnmarshalText(text []byte) error {
	str := strings.ToUpper(string(text))
	if level, ok := levelValues[str]; ok {
		*l = level
		return nil
	}
	return fmt.Errorf("unknown log level: %s", str)
}

// ParseLevel parses a level string into a Level.
// Returns LevelInfo and an error if the string is unknown.
func ParseLevel(s string) (Level, error) {
	str := strings.ToUpper(strings.TrimSpace(s))
	if level, ok := levelValues[str]; ok {
		return level, nil
	}
	return LevelInfo, fmt.Errorf("unknown log level: %s", s)
}

// MustParseLevel parses a level string and panics on error.
func MustParseLevel(s string) Level {
	level, err := ParseLevel(s)
	if err != nil {
		panic(err)
	}
	return level
}

// LevelManager provides thread-safe level management.
type LevelManager struct {
	level atomic.Int32
}

// NewLevelManager creates a new LevelManager with the given initial level.
func NewLevelManager(level Level) *LevelManager {
	lm := &LevelManager{}
	lm.level.Store(int32(level))
	return lm
}

// Set sets the current logging level atomically.
func (lm *LevelManager) Set(level Level) {
	lm.level.Store(int32(level))
}

// Get returns the current logging level.
func (lm *LevelManager) Get() Level {
	return Level(lm.level.Load())
}

// Enabled returns true if the given level is enabled.
func (lm *LevelManager) Enabled(level Level) bool {
	return level >= lm.Get()
}

// CompareAndSet atomically sets the level if the current level equals old.
// Returns true if the swap was successful.
func (lm *LevelManager) CompareAndSet(old, new Level) bool {
	return lm.level.CompareAndSwap(int32(old), int32(new))
}

// DynamicLevel is an interface for types that support dynamic level changes.
type DynamicLevel interface {
	SetLevel(level Level)
	GetLevel() Level
	IsEnabled(level Level) bool
}

// Ensure LevelManager implements DynamicLevel.
var _ DynamicLevel = (*LevelManager)(nil)

// SetLevel sets the logging level.
func (lm *LevelManager) SetLevel(level Level) {
	lm.Set(level)
}

// GetLevel returns the current logging level.
func (lm *LevelManager) GetLevel() Level {
	return lm.Get()
}

// IsEnabled returns true if the given level is enabled.
func (lm *LevelManager) IsEnabled(level Level) bool {
	return lm.Enabled(level)
}

// LevelEnabler is a function that determines if a level is enabled.
type LevelEnabler func(Level) bool

// LevelEnablerFunc adapts a function to LevelEnabler.
type LevelEnablerFunc func(Level) bool

// Enabled implements LevelEnabler.
func (f LevelEnablerFunc) Enabled(level Level) bool {
	return f(level)
}

// FixedLevelEnabler returns a LevelEnabler that always returns the same result.
func FixedLevelEnabler(enabled bool) LevelEnablerFunc {
	return func(Level) bool { return enabled }
}

// LevelRange returns a LevelEnabler that enables levels in the given range [min, max].
func LevelRange(min, max Level) LevelEnablerFunc {
	return func(level Level) bool {
		return level >= min && level <= max
	}
}
