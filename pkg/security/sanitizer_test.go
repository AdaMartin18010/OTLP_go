// Copyright The OpenTelemetry Authors
// SPDX-License-Identifier: Apache-2.0

package security

import (
	"errors"
	"regexp"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestDefaultSanitizerConfig(t *testing.T) {
	config := DefaultSanitizerConfig()

	assert.NotNil(t, config)
	assert.Equal(t, ActionMask, config.DefaultAction)
	assert.NotNil(t, config.EnabledPIITypes)
	assert.Contains(t, config.EnabledPIITypes, PIITypeEmail)
	assert.Contains(t, config.EnabledPIITypes, PIITypePhone)
	assert.Contains(t, config.EnabledPIITypes, PIITypeSSN)
	assert.NotNil(t, config.SensitiveFields)
	assert.Contains(t, config.SensitiveFields, "password")
	assert.Contains(t, config.SensitiveFields, "token")
}

func TestNewSanitizer(t *testing.T) {
	t.Run("with nil config", func(t *testing.T) {
		sanitizer := NewSanitizer(nil)
		assert.NotNil(t, sanitizer)
		assert.NotNil(t, sanitizer.config)
		assert.NotNil(t, sanitizer.patterns)
	})

	t.Run("with custom config", func(t *testing.T) {
		config := &SanitizerConfig{
			EnabledPIITypes: []PIIType{PIITypeEmail},
			DefaultAction:   ActionHash,
			CustomPatterns: map[PIIType]*regexp.Regexp{
				PIITypeCustom: regexp.MustCompile(`custom-\d+`),
			},
		}
		sanitizer := NewSanitizer(config)
		assert.NotNil(t, sanitizer)
		assert.Equal(t, ActionHash, sanitizer.config.DefaultAction)
	})
}

func TestSanitizerSanitize(t *testing.T) {
	sanitizer := NewSanitizer(nil)

	tests := []struct {
		name     string
		input    string
		contains string // Check if output contains this (masking varies by length)
		checkFn  func(t *testing.T, result string)
	}{
		{
			name:     "empty string",
			input:    "",
			contains: "",
		},
		{
			name:     "email",
			input:    "Contact: user@example.com",
			contains: "Contact:",
			checkFn: func(t *testing.T, result string) {
				assert.NotContains(t, result, "user@example.com")
				assert.Contains(t, result, "***")
			},
		},
		{
			name:     "phone number",
			input:    "Call: 123-456-7890",
			contains: "Call:",
			checkFn: func(t *testing.T, result string) {
				assert.NotContains(t, result, "123-456-7890")
			},
		},
		{
			name:     "SSN",
			input:    "SSN: 123-45-6789",
			contains: "SSN:",
			checkFn: func(t *testing.T, result string) {
				assert.NotContains(t, result, "123-45-6789")
			},
		},
		{
			name:     "credit card",
			input:    "Card: 1234-5678-9012-3456",
			contains: "Card:",
			checkFn: func(t *testing.T, result string) {
				assert.NotContains(t, result, "1234-5678-9012-3456")
			},
		},
		{
			name:     "IP address",
			input:    "IP: 192.168.1.1",
			contains: "IP:",
			checkFn: func(t *testing.T, result string) {
				assert.NotContains(t, result, "192.168.1.1")
			},
		},
		{
			name:     "MAC address",
			input:    "MAC: 00:1A:2B:3C:4D:5E",
			contains: "MAC:",
			checkFn: func(t *testing.T, result string) {
				assert.NotContains(t, result, "00:1A:2B:3C:4D:5E")
			},
		},
		{
			name:     "no PII",
			input:    "Hello World",
			contains: "Hello World",
		},
		{
			name:     "multiple emails",
			input:    "From: user1@test.com To: user2@example.org",
			contains: "From:",
			checkFn: func(t *testing.T, result string) {
				assert.NotContains(t, result, "user1@test.com")
				assert.NotContains(t, result, "user2@example.org")
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := sanitizer.Sanitize(tt.input)
			assert.Contains(t, result, tt.contains)
			if tt.checkFn != nil {
				tt.checkFn(t, result)
			}
		})
	}
}

func TestSanitizerSanitizeWithAction(t *testing.T) {
	sanitizer := NewSanitizer(nil)

	t.Run("mask action", func(t *testing.T) {
		result := sanitizer.SanitizeWithAction("Email: user@example.com", ActionMask)
		assert.NotContains(t, result, "user@example.com")
		assert.Contains(t, result, "***")
	})

	t.Run("hash action", func(t *testing.T) {
		result := sanitizer.SanitizeWithAction("Email: user@example.com", ActionHash)
		assert.NotContains(t, result, "user@example.com")
		assert.Contains(t, result, "sha256:")
	})

	t.Run("remove action", func(t *testing.T) {
		result := sanitizer.SanitizeWithAction("Email: user@example.com end", ActionRemove)
		assert.NotContains(t, result, "user@example.com")
		assert.Equal(t, "Email:  end", result)
	})

	t.Run("redact action", func(t *testing.T) {
		result := sanitizer.SanitizeWithAction("Email: user@example.com", ActionRedact)
		assert.Contains(t, result, "[EMAIL]")
		assert.NotContains(t, result, "user@example.com")
	})
}

func TestSanitizerSanitizeMap(t *testing.T) {
	sanitizer := NewSanitizer(nil)

	t.Run("nil map", func(t *testing.T) {
		result := sanitizer.SanitizeMap(nil)
		assert.Nil(t, result)
	})

	t.Run("normal values", func(t *testing.T) {
		data := map[string]string{
			"email": "user@example.com",
			"name":  "John",
		}
		result := sanitizer.SanitizeMap(data)
		assert.NotContains(t, result["email"], "user@example.com")
		assert.Equal(t, "John", result["name"])
	})

	t.Run("sensitive fields", func(t *testing.T) {
		data := map[string]string{
			"username": "john",
			"password": "secret123",
		}
		result := sanitizer.SanitizeMap(data)
		assert.Equal(t, "john", result["username"])
		assert.NotEqual(t, "secret123", result["password"])
		assert.NotContains(t, result["password"], "secret")
	})
}

func TestDetectPII(t *testing.T) {
	sanitizer := NewSanitizer(nil)

	tests := []struct {
		name          string
		input         string
		expectedTypes []PIIType
	}{
		{
			name:          "email",
			input:         "Contact: user@example.com",
			expectedTypes: []PIIType{PIITypeEmail},
		},
		{
			name:          "phone",
			input:         "Call: 123-456-7890",
			expectedTypes: []PIIType{PIITypePhone},
		},
		{
			name:          "SSN",
			input:         "SSN: 123-45-6789",
			expectedTypes: []PIIType{PIITypeSSN},
		},
		{
			name:          "multiple PII",
			input:         "Email: user@example.com, Phone: 123-456-7890",
			expectedTypes: []PIIType{PIITypeEmail, PIITypePhone},
		},
		{
			name:          "no PII",
			input:         "Hello World",
			expectedTypes: nil,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			detected := sanitizer.DetectPII(tt.input)
			if tt.expectedTypes == nil {
				assert.Empty(t, detected)
			} else {
				for _, expected := range tt.expectedTypes {
					assert.Contains(t, detected, expected)
				}
			}
		})
	}
}

func TestHasPII(t *testing.T) {
	sanitizer := NewSanitizer(nil)

	assert.True(t, sanitizer.HasPII("Email: user@example.com"))
	assert.True(t, sanitizer.HasPII("Phone: 123-456-7890"))
	assert.False(t, sanitizer.HasPII("Hello World"))
	assert.False(t, sanitizer.HasPII(""))
}

func TestSanitizerAddRemovePattern(t *testing.T) {
	sanitizer := NewSanitizer(nil)

	// Add custom pattern
	customPattern := regexp.MustCompile(`order-\d+`)
	sanitizer.AddPattern(PIITypeCustom, customPattern)

	// Should detect custom pattern
	detected := sanitizer.DetectPII("Order: order-12345")
	assert.Contains(t, detected, PIITypeCustom)

	// Remove pattern
	sanitizer.RemovePattern(PIITypeCustom)

	// Should no longer detect
	detected = sanitizer.DetectPII("Order: order-12345")
	assert.NotContains(t, detected, PIITypeCustom)
}

func TestQuickSanitize(t *testing.T) {
	result := QuickSanitize("Email: user@example.com")
	assert.NotContains(t, result, "user@example.com")
	assert.Contains(t, result, "***")
}

func TestSanitizeError(t *testing.T) {
	t.Run("nil error", func(t *testing.T) {
		result := SanitizeError(nil)
		assert.Nil(t, result)
	})

	t.Run("error with email", func(t *testing.T) {
		original := errors.New("Failed to send to user@example.com")
		result := SanitizeError(original)
		assert.NotNil(t, result)
		assert.NotContains(t, result.Error(), "user@example.com")
	})
}

func TestMaskBytes(t *testing.T) {
	tests := []struct {
		name     string
		input    []byte
		expected []byte
	}{
		{
			name:     "empty",
			input:    []byte{},
			expected: []byte{},
		},
		{
			name:     "short",
			input:    []byte("ab"),
			expected: []byte("**"),
		},
		{
			name:     "normal",
			input:    []byte("sensitive data"),
			expected: []byte("se********ta"),
		},
		{
			name:     "exactly 4",
			input:    []byte("abcd"),
			expected: []byte("abcd"),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := MaskBytes(tt.input)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestMaskString(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"", ""},
		{"ab", "**"},
		{"abcd", "****"},
		{"abcde", "ab*de"},
		{"hello world", "he*******ld"},
	}

	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			result := maskString(tt.input)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestHashString(t *testing.T) {
	input := "test data"
	result := hashString(input, "salt")

	// Should start with sha256:
	assert.Contains(t, result, "sha256:")
	// Should be masked to 16 chars after prefix
	assert.Len(t, result, 22) // "sha256:" + 16 chars
}

func TestSanitizeSensitiveFields(t *testing.T) {
	sanitizer := NewSanitizer(nil)

	input := "password=secret123 token=abc456 secret=mysecret"
	result := sanitizer.sanitizeSensitiveFields(input)

	assert.NotContains(t, result, "secret123")
	assert.NotContains(t, result, "abc456")
	assert.NotContains(t, result, "mysecret")
}

func TestIsSensitiveField(t *testing.T) {
	sanitizer := NewSanitizer(nil)

	assert.True(t, sanitizer.isSensitiveField("password"))
	assert.True(t, sanitizer.isSensitiveField("api_key"))
	assert.True(t, sanitizer.isSensitiveField("myToken"))
	assert.True(t, sanitizer.isSensitiveField("Authorization"))
	assert.False(t, sanitizer.isSensitiveField("username"))
	assert.False(t, sanitizer.isSensitiveField("email"))
}

func TestSanitizeStruct(t *testing.T) {
	sanitizer := NewSanitizer(nil)

	// This is a simplified implementation that just returns the input
	input := map[string]string{"key": "value"}
	result := sanitizer.SanitizeStruct(input)
	assert.Equal(t, input, result)
}
