package logs

import (
	"encoding/json"
	"testing"
)

func TestLevel_String(t *testing.T) {
	tests := []struct {
		level    Level
		expected string
	}{
		{LevelTrace, "TRACE"},
		{LevelDebug, "DEBUG"},
		{LevelInfo, "INFO"},
		{LevelWarn, "WARN"},
		{LevelError, "ERROR"},
		{LevelFatal, "FATAL"},
		{LevelNone, "NONE"},
		{Level(999), "LEVEL(999)"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			if got := tt.level.String(); got != tt.expected {
				t.Errorf("Level.String() = %v, want %v", got, tt.expected)
			}
		})
	}
}

func TestLevel_Enabled(t *testing.T) {
	tests := []struct {
		current  Level
		other    Level
		expected bool
	}{
		{LevelInfo, LevelDebug, false},
		{LevelInfo, LevelInfo, true},
		{LevelInfo, LevelWarn, true},
		{LevelInfo, LevelError, true},
		{LevelDebug, LevelTrace, false},
		{LevelDebug, LevelDebug, true},
		{LevelError, LevelDebug, false},
		{LevelError, LevelError, true},
		{LevelError, LevelFatal, true},
	}

	for _, tt := range tests {
		t.Run(tt.current.String()+"_"+tt.other.String(), func(t *testing.T) {
			if got := tt.current.Enabled(tt.other); got != tt.expected {
				t.Errorf("Level.Enabled() = %v, want %v", got, tt.expected)
			}
		})
	}
}

func TestLevel_MarshalJSON(t *testing.T) {
	tests := []struct {
		level    Level
		expected string
	}{
		{LevelTrace, `"TRACE"`},
		{LevelDebug, `"DEBUG"`},
		{LevelInfo, `"INFO"`},
		{LevelWarn, `"WARN"`},
		{LevelError, `"ERROR"`},
		{LevelFatal, `"FATAL"`},
	}

	for _, tt := range tests {
		t.Run(tt.level.String(), func(t *testing.T) {
			got, err := tt.level.MarshalJSON()
			if err != nil {
				t.Fatalf("MarshalJSON() error = %v", err)
			}
			if string(got) != tt.expected {
				t.Errorf("MarshalJSON() = %s, want %s", string(got), tt.expected)
			}
		})
	}
}

func TestLevel_UnmarshalJSON(t *testing.T) {
	tests := []struct {
		input    string
		expected Level
		wantErr  bool
	}{
		{`"TRACE"`, LevelTrace, false},
		{`"DEBUG"`, LevelDebug, false},
		{`"INFO"`, LevelInfo, false},
		{`"WARN"`, LevelWarn, false},
		{`"WARNING"`, LevelWarn, false},
		{`"ERROR"`, LevelError, false},
		{`"FATAL"`, LevelFatal, false},
		{`"NONE"`, LevelNone, false},
		{`"unknown"`, LevelInfo, true},
		{`"debug"`, LevelDebug, false}, // case insensitive
	}

	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			var level Level
			err := level.UnmarshalJSON([]byte(tt.input))
			if (err != nil) != tt.wantErr {
				t.Errorf("UnmarshalJSON() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if !tt.wantErr && level != tt.expected {
				t.Errorf("UnmarshalJSON() level = %v, want %v", level, tt.expected)
			}
		})
	}
}

func TestLevel_MarshalText(t *testing.T) {
	level := LevelInfo
	got, err := level.MarshalText()
	if err != nil {
		t.Fatalf("MarshalText() error = %v", err)
	}
	if string(got) != "INFO" {
		t.Errorf("MarshalText() = %s, want INFO", string(got))
	}
}

func TestLevel_UnmarshalText(t *testing.T) {
	var level Level
	err := level.UnmarshalText([]byte("WARN"))
	if err != nil {
		t.Fatalf("UnmarshalText() error = %v", err)
	}
	if level != LevelWarn {
		t.Errorf("UnmarshalText() level = %v, want LevelWarn", level)
	}
}

func TestParseLevel(t *testing.T) {
	tests := []struct {
		input       string
		expected    Level
		expectError bool
	}{
		{"trace", LevelTrace, false},
		{"DEBUG", LevelDebug, false},
		{"Info", LevelInfo, false},
		{"WARN", LevelWarn, false},
		{"WARNING", LevelWarn, false},
		{"error", LevelError, false},
		{"fatal", LevelFatal, false},
		{"none", LevelNone, false},
		{"unknown", LevelInfo, true},
		{"  INFO  ", LevelInfo, false}, // with whitespace
	}

	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			got, err := ParseLevel(tt.input)
			if (err != nil) != tt.expectError {
				t.Errorf("ParseLevel() error = %v, expectError %v", err, tt.expectError)
				return
			}
			if got != tt.expected {
				t.Errorf("ParseLevel() = %v, want %v", got, tt.expected)
			}
		})
	}
}

func TestMustParseLevel(t *testing.T) {
	// Test valid level
	level := MustParseLevel("INFO")
	if level != LevelInfo {
		t.Errorf("MustParseLevel() = %v, want LevelInfo", level)
	}

	// Test panic on invalid level
	defer func() {
		if r := recover(); r == nil {
			t.Error("MustParseLevel() expected panic for invalid level")
		}
	}()
	MustParseLevel("invalid")
}

func TestLevelManager(t *testing.T) {
	lm := NewLevelManager(LevelInfo)

	// Test Get
	if got := lm.Get(); got != LevelInfo {
		t.Errorf("Get() = %v, want LevelInfo", got)
	}

	// Test Set
	lm.Set(LevelDebug)
	if got := lm.Get(); got != LevelDebug {
		t.Errorf("After Set(), Get() = %v, want LevelDebug", got)
	}

	// Test Enabled
	if !lm.Enabled(LevelDebug) {
		t.Error("Enabled(LevelDebug) = false, want true")
	}
	if lm.Enabled(LevelTrace) {
		t.Error("Enabled(LevelTrace) = true, want false")
	}
	if !lm.Enabled(LevelError) {
		t.Error("Enabled(LevelError) = false, want true")
	}
}

func TestLevelManager_CompareAndSet(t *testing.T) {
	lm := NewLevelManager(LevelInfo)

	// Successful swap
	if !lm.CompareAndSet(LevelInfo, LevelDebug) {
		t.Error("CompareAndSet(LevelInfo, LevelDebug) = false, want true")
	}
	if lm.Get() != LevelDebug {
		t.Errorf("Get() = %v, want LevelDebug", lm.Get())
	}

	// Failed swap (old value doesn't match)
	if lm.CompareAndSet(LevelInfo, LevelError) {
		t.Error("CompareAndSet(LevelInfo, LevelError) = true, want false")
	}
	if lm.Get() != LevelDebug {
		t.Errorf("Get() = %v, want LevelDebug", lm.Get())
	}
}

func TestLevelManager_DynamicLevel(t *testing.T) {
	var _ DynamicLevel = (*LevelManager)(nil)

	lm := NewLevelManager(LevelInfo)

	// Test SetLevel
	lm.SetLevel(LevelWarn)
	if lm.GetLevel() != LevelWarn {
		t.Errorf("GetLevel() = %v, want LevelWarn", lm.GetLevel())
	}

	// Test IsEnabled
	if !lm.IsEnabled(LevelError) {
		t.Error("IsEnabled(LevelError) = false, want true")
	}
	if lm.IsEnabled(LevelDebug) {
		t.Error("IsEnabled(LevelDebug) = true, want false")
	}
}

func TestLevelEnablerFunc(t *testing.T) {
	// Test FixedLevelEnabler true
	alwaysTrue := FixedLevelEnabler(true)
	if !alwaysTrue.Enabled(LevelDebug) {
		t.Error("FixedLevelEnabler(true).Enabled() = false, want true")
	}

	// Test FixedLevelEnabler false
	alwaysFalse := FixedLevelEnabler(false)
	if alwaysFalse.Enabled(LevelError) {
		t.Error("FixedLevelEnabler(false).Enabled() = true, want false")
	}

	// Test custom function
	enabler := LevelEnablerFunc(func(l Level) bool {
		return l >= LevelWarn
	})
	if !enabler.Enabled(LevelError) {
		t.Error("custom enabler.Enabled(LevelError) = false, want true")
	}
	if enabler.Enabled(LevelInfo) {
		t.Error("custom enabler.Enabled(LevelInfo) = true, want false")
	}
}

func TestLevelRange(t *testing.T) {
	enabler := LevelRange(LevelInfo, LevelError)

	tests := []struct {
		level    Level
		expected bool
	}{
		{LevelDebug, false},
		{LevelInfo, true},
		{LevelWarn, true},
		{LevelError, true},
		{LevelFatal, false},
	}

	for _, tt := range tests {
		t.Run(tt.level.String(), func(t *testing.T) {
			if got := enabler.Enabled(tt.level); got != tt.expected {
				t.Errorf("LevelRange.Enabled(%v) = %v, want %v", tt.level, got, tt.expected)
			}
		})
	}
}

func TestLevel_JSONRoundTrip(t *testing.T) {
	type TestStruct struct {
		Level Level `json:"level"`
	}

	original := TestStruct{Level: LevelWarn}
	data, err := json.Marshal(original)
	if err != nil {
		t.Fatalf("Marshal() error = %v", err)
	}

	var decoded TestStruct
	if err := json.Unmarshal(data, &decoded); err != nil {
		t.Fatalf("Unmarshal() error = %v", err)
	}

	if decoded.Level != original.Level {
		t.Errorf("Round trip failed: got %v, want %v", decoded.Level, original.Level)
	}
}

func BenchmarkLevelManager_Get(b *testing.B) {
	lm := NewLevelManager(LevelInfo)
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_ = lm.Get()
		}
	})
}

func BenchmarkLevelManager_Set(b *testing.B) {
	lm := NewLevelManager(LevelInfo)
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			lm.Set(LevelDebug)
		}
	})
}

func BenchmarkLevelManager_Enabled(b *testing.B) {
	lm := NewLevelManager(LevelInfo)
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_ = lm.Enabled(LevelDebug)
		}
	})
}
