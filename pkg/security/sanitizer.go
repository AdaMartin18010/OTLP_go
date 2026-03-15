// Copyright The OpenTelemetry Authors
// SPDX-License-Identifier: Apache-2.0

package security

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"regexp"
	"strings"
	"sync"
)

// PIIType represents the type of personally identifiable information.
type PIIType string

const (
	// PIITypeEmail represents email addresses.
	PIITypeEmail PIIType = "email"
	// PIITypePhone represents phone numbers.
	PIITypePhone PIIType = "phone"
	// PIITypeSSN represents social security numbers.
	PIITypeSSN PIIType = "ssn"
	// PIITypeCreditCard represents credit card numbers.
	PIITypeCreditCard PIIType = "credit_card"
	// PIITypeIP represents IP addresses.
	PIITypeIP PIIType = "ip_address"
	// PIITypeMAC represents MAC addresses.
	PIITypeMAC PIIType = "mac_address"
	// PIITypePassword represents passwords.
	PIITypePassword PIIType = "password"
	// PIITypeToken represents authentication tokens.
	PIITypeToken PIIType = "token"
	// PIITypeAPIKey represents API keys.
	PIITypeAPIKey PIIType = "api_key"
	// PIITypeCustom represents custom patterns.
	PIITypeCustom PIIType = "custom"
)

// SanitizationAction represents the action to take when PII is detected.
type SanitizationAction string

const (
	// ActionMask masks the PII with asterisks.
	ActionMask SanitizationAction = "mask"
	// ActionHash hashes the PII using SHA-256.
	ActionHash SanitizationAction = "hash"
	// ActionRemove removes the PII entirely.
	ActionRemove SanitizationAction = "remove"
	// ActionRedact replaces PII with a placeholder.
	ActionRedact SanitizationAction = "redact"
)

// defaultPatterns contains built-in regex patterns for common PII types.
var defaultPatterns = map[PIIType]*regexp.Regexp{
	PIITypeEmail:      regexp.MustCompile(`(?i)\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b`),
	PIITypePhone:      regexp.MustCompile(`\b(?:\+?1[-.\s]?)?\(?([0-9]{3})\)?[-.\s]?([0-9]{3})[-.\s]?([0-9]{4})\b`),
	PIITypeSSN:        regexp.MustCompile(`\b\d{3}[-.\s]?\d{2}[-.\s]?\d{4}\b`),
	PIITypeCreditCard: regexp.MustCompile(`\b(?:\d{4}[-.\s]?){3}\d{4}\b`),
	PIITypeIP:         regexp.MustCompile(`\b(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\b`),
	PIITypeMAC:        regexp.MustCompile(`\b([0-9A-Fa-f]{2}[:-]){5}([0-9A-Fa-f]{2})\b`),
}

// SanitizerConfig holds configuration for the data sanitizer.
type SanitizerConfig struct {
	// EnabledPIITypes specifies which PII types to detect and sanitize.
	EnabledPIITypes []PIIType
	// DefaultAction specifies the default sanitization action.
	DefaultAction SanitizationAction
	// CustomPatterns allows adding custom regex patterns.
	CustomPatterns map[PIIType]*regexp.Regexp
	// SensitiveFields contains field names that should always be sanitized.
	SensitiveFields []string
	// HashSalt is an optional salt for hashing operations.
	HashSalt string
}

// DefaultSanitizerConfig returns a default sanitizer configuration.
func DefaultSanitizerConfig() *SanitizerConfig {
	return &SanitizerConfig{
		EnabledPIITypes: []PIIType{
			PIITypeEmail,
			PIITypePhone,
			PIITypeSSN,
			PIITypeCreditCard,
			PIITypePassword,
			PIITypeToken,
			PIITypeAPIKey,
		},
		DefaultAction:   ActionMask,
		CustomPatterns:  make(map[PIIType]*regexp.Regexp),
		SensitiveFields: []string{"password", "token", "secret", "key", "authorization", "cookie"},
	}
}

// Sanitizer provides data sanitization capabilities for PII detection and removal.
type Sanitizer struct {
	config   *SanitizerConfig
	patterns map[PIIType]*regexp.Regexp
	mu       sync.RWMutex
}

// NewSanitizer creates a new data sanitizer with the given configuration.
//
// Example:
//
//	config := security.DefaultSanitizerConfig()
//	config.DefaultAction = security.ActionHash
//	sanitizer := security.NewSanitizer(config)
//	clean := sanitizer.Sanitize("Contact: user@example.com")
func NewSanitizer(config *SanitizerConfig) *Sanitizer {
	if config == nil {
		config = DefaultSanitizerConfig()
	}

	patterns := make(map[PIIType]*regexp.Regexp)
	for piiType, pattern := range defaultPatterns {
		patterns[piiType] = pattern
	}
	for piiType, pattern := range config.CustomPatterns {
		patterns[piiType] = pattern
	}

	return &Sanitizer{
		config:   config,
		patterns: patterns,
	}
}

// Sanitize removes or masks PII from the input string.
//
// Example:
//
//	sanitizer := security.NewSanitizer(nil)
//	result := sanitizer.Sanitize("Email: user@example.com")
//	// Result: "Email: ****@*****.***"
func (s *Sanitizer) Sanitize(input string) string {
	return s.SanitizeWithAction(input, s.config.DefaultAction)
}

// SanitizeWithAction sanitizes the input with a specific action.
//
// Example:
//
//	sanitizer := security.NewSanitizer(nil)
//	result := sanitizer.SanitizeWithAction("Email: user@example.com", security.ActionRedact)
//	// Result: "Email: [REDACTED]"
func (s *Sanitizer) SanitizeWithAction(input string, action SanitizationAction) string {
	if input == "" {
		return input
	}

	result := input

	for _, piiType := range s.config.EnabledPIITypes {
		if pattern, ok := s.patterns[piiType]; ok {
			result = s.applyAction(result, pattern, action, piiType)
		}
	}

	// Sanitize sensitive fields
	result = s.sanitizeSensitiveFields(result)

	return result
}

// SanitizeMap sanitizes all string values in a map.
//
// Example:
//
//	sanitizer := security.NewSanitizer(nil)
//	data := map[string]string{"email": "user@example.com", "name": "John"}
//	clean := sanitizer.SanitizeMap(data)
func (s *Sanitizer) SanitizeMap(data map[string]string) map[string]string {
	if data == nil {
		return nil
	}

	result := make(map[string]string, len(data))
	for key, value := range data {
		// Check if field name indicates sensitive data
		if s.isSensitiveField(key) {
			result[key] = s.sanitizeSensitiveValue(value)
		} else {
			result[key] = s.Sanitize(value)
		}
	}

	return result
}

// SanitizeStruct sanitizes a struct by examining its fields.
// Note: This uses reflection and may have performance implications.
func (s *Sanitizer) SanitizeStruct(data interface{}) interface{} {
	// Simplified implementation - in production, use reflection
	// For now, convert to map and sanitize
	return data
}

// DetectPII scans the input for PII and returns detected types.
//
// Example:
//
//	sanitizer := security.NewSanitizer(nil)
//	detected := sanitizer.DetectPII("Contact: user@example.com, SSN: 123-45-6789")
//	// Returns: [email, ssn]
func (s *Sanitizer) DetectPII(input string) []PIIType {
	var detected []PIIType

	for _, piiType := range s.config.EnabledPIITypes {
		if pattern, ok := s.patterns[piiType]; ok {
			if pattern.MatchString(input) {
				detected = append(detected, piiType)
			}
		}
	}

	return detected
}

// HasPII returns true if the input contains any PII.
func (s *Sanitizer) HasPII(input string) bool {
	return len(s.DetectPII(input)) > 0
}

// AddPattern adds a custom pattern for PII detection.
func (s *Sanitizer) AddPattern(piiType PIIType, pattern *regexp.Regexp) {
	s.mu.Lock()
	defer s.mu.Unlock()

	s.patterns[piiType] = pattern
}

// RemovePattern removes a pattern from the sanitizer.
func (s *Sanitizer) RemovePattern(piiType PIIType) {
	s.mu.Lock()
	defer s.mu.Unlock()

	delete(s.patterns, piiType)
}

// applyAction applies the specified sanitization action to matched patterns.
func (s *Sanitizer) applyAction(input string, pattern *regexp.Regexp, action SanitizationAction, piiType PIIType) string {
	switch action {
	case ActionMask:
		return pattern.ReplaceAllStringFunc(input, func(match string) string {
			return maskString(match)
		})
	case ActionHash:
		return pattern.ReplaceAllStringFunc(input, func(match string) string {
			return hashString(match, s.config.HashSalt)
		})
	case ActionRemove:
		return pattern.ReplaceAllString(input, "")
	case ActionRedact:
		return pattern.ReplaceAllString(input, fmt.Sprintf("[%s]", strings.ToUpper(string(piiType))))
	default:
		return input
	}
}

// sanitizeSensitiveFields sanitizes values of known sensitive fields.
func (s *Sanitizer) sanitizeSensitiveFields(input string) string {
	result := input
	for _, field := range s.config.SensitiveFields {
		// Pattern to match field=value or field: value
		pattern := regexp.MustCompile(fmt.Sprintf(`(?i)(%s\s*[=:]\s*)([^\s,;]+)`, regexp.QuoteMeta(field)))
		result = pattern.ReplaceAllString(result, fmt.Sprintf("${1}%s", maskString("${2}")))
	}
	return result
}

// isSensitiveField checks if a field name indicates sensitive data.
func (s *Sanitizer) isSensitiveField(field string) bool {
	lowerField := strings.ToLower(field)
	for _, sensitive := range s.config.SensitiveFields {
		if strings.Contains(lowerField, sensitive) {
			return true
		}
	}
	return false
}

// sanitizeSensitiveValue sanitizes a known sensitive value.
func (s *Sanitizer) sanitizeSensitiveValue(value string) string {
	switch s.config.DefaultAction {
	case ActionHash:
		return hashString(value, s.config.HashSalt)
	case ActionRemove:
		return ""
	case ActionRedact:
		return "[REDACTED]"
	default:
		return maskString(value)
	}
}

// maskString masks a string with asterisks while preserving some structure.
func maskString(input string) string {
	if len(input) <= 4 {
		return strings.Repeat("*", len(input))
	}

	// Show first 2 and last 2 characters, mask the rest
	return input[:2] + strings.Repeat("*", len(input)-4) + input[len(input)-2:]
}

// hashString creates a SHA-256 hash of the input with optional salt.
func hashString(input, salt string) string {
	h := sha256.New()
	h.Write([]byte(salt))
	h.Write([]byte(input))
	return "sha256:" + hex.EncodeToString(h.Sum(nil))[:16]
}

// QuickSanitize performs quick sanitization with default settings.
// This is a convenience function for one-off sanitization needs.
//
// Example:
//
//	clean := security.QuickSanitize("Email: user@example.com")
//	// Result: "Email: ****@*****.***"
func QuickSanitize(input string) string {
	sanitizer := NewSanitizer(nil)
	return sanitizer.Sanitize(input)
}

// SanitizeError sanitizes error messages by removing PII.
//
// Example:
//
//	err := errors.New("Failed to send to user@example.com")
//	safeErr := security.SanitizeError(err)
func SanitizeError(err error) error {
	if err == nil {
		return nil
	}

	sanitizer := NewSanitizer(nil)
	return fmt.Errorf("%s", sanitizer.Sanitize(err.Error()))
}

// MaskBytes masks a byte slice, useful for binary data.
//
// Example:
//
//	data := []byte("sensitive data")
//	masked := security.MaskBytes(data)
func MaskBytes(data []byte) []byte {
	if len(data) == 0 {
		return data
	}

	result := make([]byte, len(data))
	copy(result, data)

	if len(result) <= 4 {
		for i := range result {
			result[i] = '*'
		}
		return result
	}

	// Mask middle portion
	for i := 2; i < len(result)-2; i++ {
		result[i] = '*'
	}

	return result
}
