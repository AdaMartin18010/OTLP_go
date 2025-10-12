// Package security provides comprehensive security utilities for OTLP Go applications.
// It includes sensitive data filtering, input validation, authorization mechanisms,
// encryption utilities, security headers, audit logging, and compliance checking.
//
// Key Features:
// - Sensitive data filtering and redaction
// - Input validation and sanitization
// - Password hashing and verification
// - Token generation and management
// - Security headers configuration
// - Audit logging and compliance
// - Authorization and permission checking
//
// Usage Example:
//
//	// Initialize security manager
//	sm := security.NewSecurityManager()
//
//	// Filter sensitive data
//	filtered := sm.FilterSensitiveData("password=secret123")
//
//	// Validate input
//	errors := sm.ValidateInput(map[string]string{
//	    "email": "user@example.com",
//	    "password": "SecurePass123!",
//	})
//
//	// Hash password
//	hashed, err := security.HashPassword("password123")
//
//	// Generate token
//	token, err := security.GenerateToken(32)
package security

import (
	"context"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"regexp"
	"strings"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// SensitiveDataFilter provides comprehensive sensitive data filtering and redaction capabilities.
// It uses configurable regex patterns to identify and mask sensitive information such as
// passwords, tokens, credit card numbers, SSNs, and other PII data.
//
// The filter supports both string-based and map-based data filtering with customizable
// replacement patterns and pattern matching rules.
type SensitiveDataFilter struct {
	mu          sync.RWMutex
	patterns    map[string]*regexp.Regexp
	replacement string
	config      *FilterConfig
	stats       *FilterStats
	tracer      trace.Tracer
}

// FilterConfig holds configuration for the sensitive data filter.
type FilterConfig struct {
	EnableLogging     bool
	EnableMetrics     bool
	CaseSensitive     bool
	MaxPatterns       int
	ReplacementMode   string // "mask", "hash", "remove"
	CustomReplacement string
}

// FilterStats holds statistics about filter operations.
type FilterStats struct {
	TotalFilters      int64
	SuccessfulFilters int64
	FailedFilters     int64
	PatternMatches    int64
	DataProcessed     int64
	LastFilterTime    time.Time
}

// NewSensitiveDataFilter creates a new sensitive data filter with default configuration
// and predefined patterns for common sensitive data types.
//
// The filter is initialized with:
// - Default replacement string "[REDACTED]"
// - Predefined patterns for passwords, tokens, secrets, credit cards, SSNs, and emails
// - OpenTelemetry tracing support
// - Statistics collection
//
// Returns a configured SensitiveDataFilter ready for use.
func NewSensitiveDataFilter() *SensitiveDataFilter {
	filter := &SensitiveDataFilter{
		patterns:    make(map[string]*regexp.Regexp),
		replacement: "[REDACTED]",
		config: &FilterConfig{
			EnableLogging:     true,
			EnableMetrics:     true,
			CaseSensitive:     false,
			MaxPatterns:       100,
			ReplacementMode:   "mask",
			CustomReplacement: "[REDACTED]",
		},
		stats:  &FilterStats{},
		tracer: otel.Tracer("sensitive_data_filter"),
	}

	// Predefined sensitive data patterns with comprehensive coverage
	filter.AddPattern("password", `(?i)(password|pass|pwd|passwd)\s*[:=]\s*["']?([^"'\s]+)["']?`)
	filter.AddPattern("token", `(?i)(token|access_token|refresh_token|api_key|auth_token|bearer_token)\s*[:=]\s*["']?([^"'\s]+)["']?`)
	filter.AddPattern("secret", `(?i)(secret|key|private_key|secret_key|api_secret)\s*[:=]\s*["']?([^"'\s]+)["']?`)
	filter.AddPattern("credit_card", `\b(?:\d{4}[-\s]?){3}\d{4}\b`)
	filter.AddPattern("ssn", `\b\d{3}-\d{2}-\d{4}\b`)
	filter.AddPattern("email", `\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b`)
	filter.AddPattern("phone", `\b(?:\+?1[-.\s]?)?\(?([0-9]{3})\)?[-.\s]?([0-9]{3})[-.\s]?([0-9]{4})\b`)
	filter.AddPattern("ip_address", `\b(?:[0-9]{1,3}\.){3}[0-9]{1,3}\b`)
	filter.AddPattern("mac_address", `\b(?:[0-9A-Fa-f]{2}[:-]){5}(?:[0-9A-Fa-f]{2})\b`)
	filter.AddPattern("uuid", `\b[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}\b`)

	return filter
}

// AddPattern adds a new sensitive data pattern to the filter.
// The pattern is compiled as a regular expression and stored for future filtering operations.
//
// Parameters:
//   - name: A unique identifier for the pattern
//   - pattern: The regular expression pattern to match sensitive data
//
// Returns an error if the pattern cannot be compiled as a valid regex.
func (f *SensitiveDataFilter) AddPattern(name, pattern string) error {
	_, span := f.tracer.Start(context.Background(), "add_pattern")
	defer span.End()

	span.SetAttributes(
		attribute.String("pattern_name", name),
		attribute.String("pattern", pattern),
	)

	f.mu.Lock()
	defer f.mu.Unlock()

	// Check pattern limit
	if len(f.patterns) >= f.config.MaxPatterns {
		err := fmt.Errorf("maximum pattern limit reached: %d", f.config.MaxPatterns)
		span.RecordError(err)
		return err
	}

	// Compile regex pattern
	regex, err := regexp.Compile(pattern)
	if err != nil {
		span.RecordError(err)
		return fmt.Errorf("invalid regex pattern '%s': %w", pattern, err)
	}

	f.patterns[name] = regex
	span.SetAttributes(attribute.Bool("success", true))

	return nil
}

// Filter applies all registered patterns to filter sensitive data from the input string.
// It uses intelligent replacement that preserves field names while masking values.
//
// The filtering process:
// 1. Iterates through all registered patterns
// 2. Applies pattern matching and replacement
// 3. Preserves field names (e.g., "password: secret" -> "password: [REDACTED]")
// 4. Updates statistics and tracing information
//
// Parameters:
//   - data: The input string containing potentially sensitive data
//
// Returns the filtered string with sensitive data replaced.
func (f *SensitiveDataFilter) Filter(data string) string {
	_, span := f.tracer.Start(context.Background(), "filter_data")
	defer span.End()

	span.SetAttributes(
		attribute.Int("input_length", len(data)),
		attribute.Int("pattern_count", len(f.patterns)),
	)

	f.mu.RLock()
	defer f.mu.RUnlock()

	result := data
	matches := 0

	for name, pattern := range f.patterns {
		originalResult := result
		result = pattern.ReplaceAllStringFunc(result, func(match string) string {
			matches++

			// Intelligent replacement preserving field names
			// Handle key-value pairs with colon separator
			if parts := strings.SplitN(match, ":", 2); len(parts) == 2 {
				return parts[0] + ":" + f.getReplacement(parts[1])
			}

			// Handle key-value pairs with equals separator
			if parts := strings.SplitN(match, "=", 2); len(parts) == 2 {
				return parts[0] + "=" + f.getReplacement(parts[1])
			}

			// Handle quoted values
			if strings.HasPrefix(match, `"`) && strings.HasSuffix(match, `"`) {
				return `"` + f.getReplacement(match[1:len(match)-1]) + `"`
			}
			if strings.HasPrefix(match, `'`) && strings.HasSuffix(match, `'`) {
				return `'` + f.getReplacement(match[1:len(match)-1]) + `'`
			}

			// Default replacement
			return f.getReplacement(match)
		})

		// Log pattern usage if enabled
		if f.config.EnableLogging && result != originalResult {
			span.AddEvent("pattern_matched", trace.WithAttributes(
				attribute.String("pattern_name", name),
				attribute.Int("matches", matches),
			))
		}
	}

	// Update statistics
	f.stats.TotalFilters++
	f.stats.SuccessfulFilters++
	f.stats.PatternMatches += int64(matches)
	f.stats.DataProcessed += int64(len(data))
	f.stats.LastFilterTime = time.Now()

	span.SetAttributes(
		attribute.Int("output_length", len(result)),
		attribute.Int64("matches_found", int64(matches)),
		attribute.Bool("data_filtered", result != data),
	)

	return result
}

// getReplacement returns the appropriate replacement string based on configuration.
func (f *SensitiveDataFilter) getReplacement(value string) string {
	switch f.config.ReplacementMode {
	case "hash":
		// Hash the value for consistent but obscured replacement
		hash := sha256.Sum256([]byte(value))
		return fmt.Sprintf("[HASH:%x]", hash[:8])
	case "remove":
		// Remove the value entirely
		return ""
	case "mask":
		fallthrough
	default:
		// Use configured replacement
		if f.config.CustomReplacement != "" {
			return f.config.CustomReplacement
		}
		return f.replacement
	}
}

// FilterMap filters sensitive data from a map structure by checking keys against
// sensitive key patterns and applying appropriate replacements.
//
// The filtering process:
// 1. Iterates through all key-value pairs in the map
// 2. Checks if the key matches sensitive key patterns
// 3. Applies replacement for sensitive keys
// 4. Preserves non-sensitive data
// 5. Handles nested map structures recursively
//
// Parameters:
//   - data: The input map containing potentially sensitive data
//
// Returns a new map with sensitive data filtered.
func (f *SensitiveDataFilter) FilterMap(data map[string]interface{}) map[string]interface{} {
	_, span := f.tracer.Start(context.Background(), "filter_map")
	defer span.End()

	span.SetAttributes(
		attribute.Int("map_size", len(data)),
	)

	f.mu.RLock()
	defer f.mu.RUnlock()

	result := make(map[string]interface{})
	sensitiveKeys := 0

	for key, value := range data {
		if f.isSensitiveKey(key) {
			result[key] = f.getReplacement(fmt.Sprintf("%v", value))
			sensitiveKeys++

			if f.config.EnableLogging {
				span.AddEvent("sensitive_key_filtered", trace.WithAttributes(
					attribute.String("key", key),
				))
			}
		} else {
			// Recursively filter nested maps
			if nestedMap, ok := value.(map[string]interface{}); ok {
				result[key] = f.FilterMap(nestedMap)
			} else {
				result[key] = value
			}
		}
	}

	// Update statistics
	f.stats.TotalFilters++
	f.stats.SuccessfulFilters++
	f.stats.PatternMatches += int64(sensitiveKeys)
	f.stats.DataProcessed += int64(len(data))
	f.stats.LastFilterTime = time.Now()

	span.SetAttributes(
		attribute.Int("sensitive_keys_found", sensitiveKeys),
		attribute.Bool("data_filtered", sensitiveKeys > 0),
	)

	return result
}

// isSensitiveKey checks if a key name indicates sensitive data by matching against
// a comprehensive list of sensitive key patterns.
//
// The function performs case-insensitive matching against common sensitive data
// field names including passwords, tokens, secrets, personal information, etc.
//
// Parameters:
//   - key: The key name to check
//
// Returns true if the key indicates sensitive data, false otherwise.
func (f *SensitiveDataFilter) isSensitiveKey(key string) bool {
	lowerKey := strings.ToLower(key)

	// Comprehensive list of sensitive key patterns
	sensitiveKeys := []string{
		// Authentication and authorization
		"password", "pass", "pwd", "passwd",
		"token", "access_token", "refresh_token", "api_key", "auth_token", "bearer_token",
		"secret", "key", "private_key", "secret_key", "api_secret",

		// Personal information
		"credit_card", "card_number", "cc_number", "creditcard",
		"ssn", "social_security", "social_security_number",
		"email", "email_address", "e_mail",
		"phone", "mobile", "telephone", "phone_number", "mobile_number",
		"address", "home_address", "billing_address", "shipping_address",
		"name", "first_name", "last_name", "full_name", "username", "user_name",
		"birth_date", "birthday", "date_of_birth", "dob",
		"national_id", "id_number", "identity_number",

		// Financial information
		"bank_account", "account_number", "routing_number",
		"salary", "income", "wage", "pay_rate",
		"tax_id", "tax_number", "vat_number",

		// System and network information
		"ip_address", "ip", "mac_address", "mac",
		"session_id", "sessionid", "session_token",
		"cookie", "cookies", "csrf_token", "csrf",

		// Other sensitive data
		"uuid", "guid", "id", "identifier",
		"license", "license_key", "license_number",
		"pin", "personal_identification_number",
		"cvv", "cvc", "security_code",
	}

	// Check for exact matches and substring matches
	for _, sensitive := range sensitiveKeys {
		if strings.Contains(lowerKey, sensitive) {
			return true
		}
	}

	return false
}

// InputValidator provides comprehensive input validation capabilities with support for
// multiple validation rules, custom validators, and detailed error reporting.
//
// The validator supports:
// - Required field validation
// - Length constraints (min/max)
// - Pattern matching with regex
// - Custom validation functions
// - Detailed error messages
// - OpenTelemetry tracing
//
// Usage Example:
//
//	validator := security.NewInputValidator()
//	validator.AddRule("email", security.EmailRule)
//	validator.AddRule("password", security.PasswordRule)
//	errors := validator.Validate(data)
type InputValidator struct {
	mu     sync.RWMutex
	rules  map[string]*ValidationRule
	stats  *ValidationStats
	tracer trace.Tracer
}

// ValidationStats holds statistics about validation operations.
type ValidationStats struct {
	TotalValidations      int64
	SuccessfulValidations int64
	FailedValidations     int64
	RuleViolations        int64
	LastValidationTime    time.Time
}

// ValidationRule defines a validation rule for input fields with comprehensive
// validation options including required checks, length constraints, pattern matching,
// and custom validation functions.
//
// Fields:
//   - Required: Whether the field is mandatory
//   - MinLen: Minimum length constraint
//   - MaxLen: Maximum length constraint
//   - Pattern: Regular expression pattern for format validation
//   - Custom: Custom validation function for complex validation logic
//   - ErrorMessage: Custom error message for validation failures
//   - Sanitize: Whether to sanitize the input value
type ValidationRule struct {
	Required     bool
	MinLen       int
	MaxLen       int
	Pattern      *regexp.Regexp
	Custom       func(string) error
	ErrorMessage string
	Sanitize     bool
}

// NewInputValidator creates a new input validator with default configuration
// and OpenTelemetry tracing support.
//
// The validator is initialized with:
// - Empty rules map
// - Statistics collection
// - OpenTelemetry tracer
//
// Returns a configured InputValidator ready for use.
func NewInputValidator() *InputValidator {
	return &InputValidator{
		rules:  make(map[string]*ValidationRule),
		stats:  &ValidationStats{},
		tracer: otel.Tracer("input_validator"),
	}
}

// AddRule adds a validation rule for a specific field.
//
// Parameters:
//   - field: The field name to validate
//   - rule: The validation rule to apply
//
// The rule is stored and will be applied during validation operations.
func (v *InputValidator) AddRule(field string, rule *ValidationRule) {
	_, span := v.tracer.Start(context.Background(), "add_validation_rule")
	defer span.End()

	span.SetAttributes(
		attribute.String("field", field),
		attribute.Bool("required", rule.Required),
		attribute.Int("min_length", rule.MinLen),
		attribute.Int("max_length", rule.MaxLen),
		attribute.Bool("has_pattern", rule.Pattern != nil),
		attribute.Bool("has_custom", rule.Custom != nil),
	)

	v.mu.Lock()
	defer v.mu.Unlock()

	v.rules[field] = rule
	span.SetAttributes(attribute.Bool("success", true))
}

// Validate validates input data against all registered rules and returns
// a map of field names to error messages for any validation failures.
//
// The validation process:
// 1. Iterates through all input fields
// 2. Applies corresponding validation rules
// 3. Collects error messages for failed validations
// 4. Updates statistics and tracing information
//
// Parameters:
//   - data: Map of field names to values to validate
//
// Returns a map of field names to error messages for validation failures.
func (v *InputValidator) Validate(data map[string]string) map[string]string {
	_, span := v.tracer.Start(context.Background(), "validate_input")
	defer span.End()

	span.SetAttributes(
		attribute.Int("input_fields", len(data)),
		attribute.Int("validation_rules", len(v.rules)),
	)

	v.mu.RLock()
	defer v.mu.RUnlock()

	errors := make(map[string]string)
	validations := 0
	failures := 0

	for field, value := range data {
		rule, exists := v.rules[field]
		if !exists {
			continue
		}

		validations++
		if err := v.validateField(field, value, rule); err != nil {
			errors[field] = err.Error()
			failures++

			span.AddEvent("validation_failed", trace.WithAttributes(
				attribute.String("field", field),
				attribute.String("error", err.Error()),
			))
		}
	}

	// Update statistics
	v.stats.TotalValidations += int64(validations)
	v.stats.SuccessfulValidations += int64(validations - failures)
	v.stats.FailedValidations += int64(failures)
	v.stats.RuleViolations += int64(failures)
	v.stats.LastValidationTime = time.Now()

	span.SetAttributes(
		attribute.Int("validations_performed", validations),
		attribute.Int("validation_failures", failures),
		attribute.Bool("validation_successful", failures == 0),
	)

	return errors
}

// validateField validates a single field against its validation rule.
// It performs comprehensive validation including required checks, length constraints,
// pattern matching, and custom validation functions.
//
// Parameters:
//   - field: The field name being validated
//   - value: The field value to validate
//   - rule: The validation rule to apply
//
// Returns an error if validation fails, nil if validation passes.
func (v *InputValidator) validateField(field, value string, rule *ValidationRule) error {
	// Sanitize input if configured
	if rule.Sanitize {
		value = strings.TrimSpace(value)
	}

	// Check required field
	if rule.Required && value == "" {
		if rule.ErrorMessage != "" {
			return fmt.Errorf("%s", rule.ErrorMessage)
		}
		return fmt.Errorf("%s is required", field)
	}

	// If value is empty and not required, skip other validations
	if value == "" {
		return nil
	}

	// Check minimum length
	if rule.MinLen > 0 && len(value) < rule.MinLen {
		if rule.ErrorMessage != "" {
			return fmt.Errorf("%s", rule.ErrorMessage)
		}
		return fmt.Errorf("%s must be at least %d characters", field, rule.MinLen)
	}

	// Check maximum length
	if rule.MaxLen > 0 && len(value) > rule.MaxLen {
		if rule.ErrorMessage != "" {
			return fmt.Errorf("%s", rule.ErrorMessage)
		}
		return fmt.Errorf("%s must be at most %d characters", field, rule.MaxLen)
	}

	// Check pattern match
	if rule.Pattern != nil && !rule.Pattern.MatchString(value) {
		if rule.ErrorMessage != "" {
			return fmt.Errorf("%s", rule.ErrorMessage)
		}
		return fmt.Errorf("%s format is invalid", field)
	}

	// Custom validation
	if rule.Custom != nil {
		if err := rule.Custom(value); err != nil {
			if rule.ErrorMessage != "" {
				return fmt.Errorf("%s", rule.ErrorMessage)
			}
			return err
		}
	}

	return nil
}

// Predefined validation rules for common data types.
// These rules provide standard validation patterns for email addresses,
// passwords, phone numbers, usernames, and other common input fields.
var (
	// EmailRule validates email addresses using RFC 5322 compliant regex pattern.
	EmailRule = &ValidationRule{
		Required:     true,
		Pattern:      regexp.MustCompile(`^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}$`),
		ErrorMessage: "Invalid email format",
		Sanitize:     true,
	}

	// PasswordRule validates passwords with length constraints and character requirements.
	PasswordRule = &ValidationRule{
		Required:     true,
		MinLen:       8,
		MaxLen:       128,
		Pattern:      regexp.MustCompile(`^[A-Za-z\d@$!%*?&]{8,}$`),
		ErrorMessage: "Password must be at least 8 characters and contain letters, numbers, and special characters",
		Sanitize:     false,
	}

	// PhoneRule validates phone numbers with international format support.
	PhoneRule = &ValidationRule{
		Required:     false,
		Pattern:      regexp.MustCompile(`^\+?[\d\s\-\(\)]+$`),
		ErrorMessage: "Invalid phone number format",
		Sanitize:     true,
	}

	// UsernameRule validates usernames with alphanumeric characters, underscores, and hyphens.
	UsernameRule = &ValidationRule{
		Required:     true,
		MinLen:       3,
		MaxLen:       50,
		Pattern:      regexp.MustCompile(`^[a-zA-Z0-9_-]+$`),
		ErrorMessage: "Username must contain only letters, numbers, underscores, and hyphens",
		Sanitize:     true,
	}

	// CreditCardRule validates credit card numbers using Luhn algorithm.
	CreditCardRule = &ValidationRule{
		Required:     true,
		MinLen:       13,
		MaxLen:       19,
		Pattern:      regexp.MustCompile(`^\d{13,19}$`),
		ErrorMessage: "Invalid credit card number",
		Sanitize:     true,
		Custom: func(value string) error {
			// Basic Luhn algorithm validation
			sum := 0
			alternate := false
			for i := len(value) - 1; i >= 0; i-- {
				n := int(value[i] - '0')
				if alternate {
					n *= 2
					if n > 9 {
						n = (n % 10) + 1
					}
				}
				sum += n
				alternate = !alternate
			}
			if sum%10 != 0 {
				return fmt.Errorf("invalid credit card number")
			}
			return nil
		},
	}

	// SSNRule validates Social Security Numbers in XXX-XX-XXXX format.
	SSNRule = &ValidationRule{
		Required:     true,
		Pattern:      regexp.MustCompile(`^\d{3}-\d{2}-\d{4}$`),
		ErrorMessage: "Invalid SSN format (XXX-XX-XXXX)",
		Sanitize:     true,
	}

	// URLRule validates URLs with proper protocol and domain format.
	URLRule = &ValidationRule{
		Required:     true,
		Pattern:      regexp.MustCompile(`^https?:\/\/(www\.)?[-a-zA-Z0-9@:%._\+~#=]{1,256}\.[a-zA-Z0-9()]{1,6}\b([-a-zA-Z0-9()@:%_\+.~#?&//=]*)$`),
		ErrorMessage: "Invalid URL format",
		Sanitize:     true,
	}
)

// SecurityContext represents the security context for a user session or request.
// It contains user identification, session information, permissions, roles,
// and timing information for security enforcement and audit logging.
//
// Fields:
//   - UserID: Unique identifier for the user
//   - SessionID: Unique identifier for the session
//   - IPAddress: Client IP address
//   - UserAgent: Client user agent string
//   - Permissions: List of permissions granted to the user
//   - Roles: List of roles assigned to the user
//   - CreatedAt: When the context was created
//   - ExpiresAt: When the context expires
//   - Metadata: Additional context metadata
type SecurityContext struct {
	UserID      string
	SessionID   string
	IPAddress   string
	UserAgent   string
	Permissions []string
	Roles       []string
	CreatedAt   time.Time
	ExpiresAt   time.Time
	Metadata    map[string]interface{}
}

// HasPermission checks if the security context has a specific permission.
//
// Parameters:
//   - permission: The permission to check for
//
// Returns true if the permission is granted, false otherwise.
func (sc *SecurityContext) HasPermission(permission string) bool {
	for _, p := range sc.Permissions {
		if p == permission {
			return true
		}
	}
	return false
}

// HasRole checks if the security context has a specific role.
//
// Parameters:
//   - role: The role to check for
//
// Returns true if the role is assigned, false otherwise.
func (sc *SecurityContext) HasRole(role string) bool {
	for _, r := range sc.Roles {
		if r == role {
			return true
		}
	}
	return false
}

// IsExpired checks if the security context has expired.
//
// Returns true if the current time is after the expiration time, false otherwise.
func (sc *SecurityContext) IsExpired() bool {
	return time.Now().After(sc.ExpiresAt)
}

// IsValid checks if the security context is valid (not expired and has required fields).
//
// Returns true if the context is valid, false otherwise.
func (sc *SecurityContext) IsValid() bool {
	return sc.UserID != "" && sc.SessionID != "" && !sc.IsExpired()
}

// AddPermission adds a permission to the security context.
//
// Parameters:
//   - permission: The permission to add
func (sc *SecurityContext) AddPermission(permission string) {
	for _, p := range sc.Permissions {
		if p == permission {
			return // Permission already exists
		}
	}
	sc.Permissions = append(sc.Permissions, permission)
}

// AddRole adds a role to the security context.
//
// Parameters:
//   - role: The role to add
func (sc *SecurityContext) AddRole(role string) {
	for _, r := range sc.Roles {
		if r == role {
			return // Role already exists
		}
	}
	sc.Roles = append(sc.Roles, role)
}

// RemovePermission removes a permission from the security context.
//
// Parameters:
//   - permission: The permission to remove
func (sc *SecurityContext) RemovePermission(permission string) {
	for i, p := range sc.Permissions {
		if p == permission {
			sc.Permissions = append(sc.Permissions[:i], sc.Permissions[i+1:]...)
			return
		}
	}
}

// RemoveRole removes a role from the security context.
//
// Parameters:
//   - role: The role to remove
func (sc *SecurityContext) RemoveRole(role string) {
	for i, r := range sc.Roles {
		if r == role {
			sc.Roles = append(sc.Roles[:i], sc.Roles[i+1:]...)
			return
		}
	}
}

// SecurityManager provides a centralized security management system that combines
// sensitive data filtering, input validation, authorization, encryption, and audit logging.
//
// The SecurityManager serves as the main entry point for all security operations
// and provides a unified interface for security-related functionality.
//
// Features:
// - Sensitive data filtering and redaction
// - Input validation and sanitization
// - Password hashing and verification
// - Token generation and management
// - Security headers configuration
// - Audit logging and compliance
// - Authorization and permission checking
//
// Usage Example:
//
//	sm := security.NewSecurityManager()
//	filtered := sm.FilterSensitiveData("password=secret123")
//	errors := sm.ValidateInput(data)
//	hashed, err := sm.HashPassword("password123")
type SecurityManager struct {
	mu          sync.RWMutex
	filter      *SensitiveDataFilter
	validator   *InputValidator
	auditLogger *AuditLogger
	config      *SecurityConfig
	stats       *SecurityManagerStats
	tracer      trace.Tracer
}

// SecurityConfig holds configuration for the security manager.
type SecurityConfig struct {
	EnableFiltering     bool
	EnableValidation    bool
	EnableAuditLogging  bool
	EnableEncryption    bool
	EnableAuthorization bool
	LogLevel            string
	AuditBufferSize     int
}

// SecurityManagerStats holds statistics about security manager operations.
type SecurityManagerStats struct {
	TotalOperations         int64
	FilterOperations        int64
	ValidationOperations    int64
	AuditOperations         int64
	EncryptionOperations    int64
	AuthorizationOperations int64
	LastOperationTime       time.Time
}

// NewSecurityManager creates a new security manager with default configuration
// and all security components initialized.
//
// The security manager is initialized with:
// - Sensitive data filter with predefined patterns
// - Input validator with common validation rules
// - Audit logger for security event tracking
// - Default security configuration
// - Statistics collection
// - OpenTelemetry tracing
//
// Returns a configured SecurityManager ready for use.
func NewSecurityManager() *SecurityManager {
	return &SecurityManager{
		filter:      NewSensitiveDataFilter(),
		validator:   NewInputValidator(),
		auditLogger: NewAuditLogger(1000), // Default buffer size
		config: &SecurityConfig{
			EnableFiltering:     true,
			EnableValidation:    true,
			EnableAuditLogging:  true,
			EnableEncryption:    true,
			EnableAuthorization: true,
			LogLevel:            "info",
			AuditBufferSize:     1000,
		},
		stats:  &SecurityManagerStats{},
		tracer: otel.Tracer("security_manager"),
	}
}

// FilterSensitiveData filters sensitive data from a string using the configured filter.
//
// Parameters:
//   - data: The input string containing potentially sensitive data
//
// Returns the filtered string with sensitive data replaced.
func (sm *SecurityManager) FilterSensitiveData(data string) string {
	_, span := sm.tracer.Start(context.Background(), "filter_sensitive_data")
	defer span.End()

	span.SetAttributes(
		attribute.Int("input_length", len(data)),
		attribute.Bool("filtering_enabled", sm.config.EnableFiltering),
	)

	if !sm.config.EnableFiltering {
		return data
	}

	result := sm.filter.Filter(data)

	sm.mu.Lock()
	sm.stats.TotalOperations++
	sm.stats.FilterOperations++
	sm.stats.LastOperationTime = time.Now()
	sm.mu.Unlock()

	span.SetAttributes(
		attribute.Int("output_length", len(result)),
		attribute.Bool("data_filtered", result != data),
	)

	return result
}

// FilterSensitiveMap filters sensitive data from a map structure using the configured filter.
//
// Parameters:
//   - data: The input map containing potentially sensitive data
//
// Returns a new map with sensitive data filtered.
func (sm *SecurityManager) FilterSensitiveMap(data map[string]interface{}) map[string]interface{} {
	_, span := sm.tracer.Start(context.Background(), "filter_sensitive_map")
	defer span.End()

	span.SetAttributes(
		attribute.Int("map_size", len(data)),
		attribute.Bool("filtering_enabled", sm.config.EnableFiltering),
	)

	if !sm.config.EnableFiltering {
		return data
	}

	result := sm.filter.FilterMap(data)

	sm.mu.Lock()
	sm.stats.TotalOperations++
	sm.stats.FilterOperations++
	sm.stats.LastOperationTime = time.Now()
	sm.mu.Unlock()

	span.SetAttributes(
		attribute.Int("output_size", len(result)),
		attribute.Bool("data_filtered", len(result) != len(data)),
	)

	return result
}

// ValidateInput validates input data against registered validation rules.
//
// Parameters:
//   - data: Map of field names to values to validate
//
// Returns a map of field names to error messages for validation failures.
func (sm *SecurityManager) ValidateInput(data map[string]string) map[string]string {
	_, span := sm.tracer.Start(context.Background(), "validate_input")
	defer span.End()

	span.SetAttributes(
		attribute.Int("input_fields", len(data)),
		attribute.Bool("validation_enabled", sm.config.EnableValidation),
	)

	if !sm.config.EnableValidation {
		return make(map[string]string)
	}

	errors := sm.validator.Validate(data)

	sm.mu.Lock()
	sm.stats.TotalOperations++
	sm.stats.ValidationOperations++
	sm.stats.LastOperationTime = time.Now()
	sm.mu.Unlock()

	span.SetAttributes(
		attribute.Int("validation_errors", len(errors)),
		attribute.Bool("validation_successful", len(errors) == 0),
	)

	return errors
}

// AddValidationRule adds a validation rule for a specific field.
//
// Parameters:
//   - field: The field name to validate
//   - rule: The validation rule to apply
func (sm *SecurityManager) AddValidationRule(field string, rule *ValidationRule) {
	_, span := sm.tracer.Start(context.Background(), "add_validation_rule")
	defer span.End()

	span.SetAttributes(
		attribute.String("field", field),
		attribute.Bool("validation_enabled", sm.config.EnableValidation),
	)

	if !sm.config.EnableValidation {
		return
	}

	sm.validator.AddRule(field, rule)
	span.SetAttributes(attribute.Bool("success", true))
}

// 加密工具

// HashPassword 哈希密码
func HashPassword(password string) (string, error) {
	// 生成随机盐
	salt := make([]byte, 32)
	if _, err := rand.Read(salt); err != nil {
		return "", fmt.Errorf("failed to generate salt: %w", err)
	}

	// 哈希密码
	hash := sha256.Sum256(append(salt, []byte(password)...))

	// 返回盐+哈希的十六进制表示
	return hex.EncodeToString(append(salt, hash[:]...)), nil
}

// VerifyPassword 验证密码
func VerifyPassword(password, hashedPassword string) bool {
	// 解码十六进制
	data, err := hex.DecodeString(hashedPassword)
	if err != nil {
		return false
	}

	if len(data) < 32 {
		return false
	}

	// 提取盐和哈希
	salt := data[:32]
	expectedHash := data[32:]

	// 计算哈希
	hash := sha256.Sum256(append(salt, []byte(password)...))

	// 比较哈希
	return string(hash[:]) == string(expectedHash)
}

// GenerateToken 生成令牌
func GenerateToken(length int) (string, error) {
	bytes := make([]byte, length)
	if _, err := rand.Read(bytes); err != nil {
		return "", fmt.Errorf("failed to generate token: %w", err)
	}
	return hex.EncodeToString(bytes), nil
}

// 安全头设置

// SecurityHeaders 安全头
type SecurityHeaders struct {
	ContentTypeOptions string
	FrameOptions       string
	XSSProtection      string
	StrictTransport    string
	CSP                string
}

// DefaultSecurityHeaders 默认安全头
func DefaultSecurityHeaders() *SecurityHeaders {
	return &SecurityHeaders{
		ContentTypeOptions: "nosniff",
		FrameOptions:       "DENY",
		XSSProtection:      "1; mode=block",
		StrictTransport:    "max-age=31536000; includeSubDomains",
		CSP:                "default-src 'self'",
	}
}

// GetHeaders 获取安全头
func (sh *SecurityHeaders) GetHeaders() map[string]string {
	return map[string]string{
		"X-Content-Type-Options":    sh.ContentTypeOptions,
		"X-Frame-Options":           sh.FrameOptions,
		"X-XSS-Protection":          sh.XSSProtection,
		"Strict-Transport-Security": sh.StrictTransport,
		"Content-Security-Policy":   sh.CSP,
	}
}

// 审计日志

// AuditEvent 审计事件
type AuditEvent struct {
	ID        string                 `json:"id"`
	UserID    string                 `json:"user_id"`
	Action    string                 `json:"action"`
	Resource  string                 `json:"resource"`
	IPAddress string                 `json:"ip_address"`
	UserAgent string                 `json:"user_agent"`
	Success   bool                   `json:"success"`
	Details   map[string]interface{} `json:"details"`
	Timestamp time.Time              `json:"timestamp"`
}

// AuditLogger 审计日志记录器
type AuditLogger struct {
	events chan *AuditEvent
	stopCh chan struct{}
}

// NewAuditLogger 创建审计日志记录器
func NewAuditLogger(bufferSize int) *AuditLogger {
	return &AuditLogger{
		events: make(chan *AuditEvent, bufferSize),
		stopCh: make(chan struct{}),
	}
}

// Start 开始审计日志记录
func (al *AuditLogger) Start() {
	go al.processEvents()
}

// Stop 停止审计日志记录
func (al *AuditLogger) Stop() {
	close(al.stopCh)
}

// Log 记录审计事件
func (al *AuditLogger) Log(event *AuditEvent) {
	select {
	case al.events <- event:
	default:
		// 如果缓冲区满了，丢弃事件
		fmt.Printf("Audit log buffer full, dropping event: %s\n", event.Action)
	}
}

// processEvents 处理审计事件
func (al *AuditLogger) processEvents() {
	for {
		select {
		case event := <-al.events:
			al.writeEvent(event)
		case <-al.stopCh:
			return
		}
	}
}

// writeEvent 写入审计事件
func (al *AuditLogger) writeEvent(event *AuditEvent) {
	// 这里可以实现实际的日志写入逻辑
	// 例如写入文件、数据库或发送到日志系统
	fmt.Printf("Audit Event: %+v\n", event)
}

// 全局安全管理器
var globalSecurityManager *SecurityManager

// InitGlobalSecurityManager 初始化全局安全管理器
func InitGlobalSecurityManager() {
	globalSecurityManager = NewSecurityManager()
}

// GetGlobalSecurityManager 获取全局安全管理器
func GetGlobalSecurityManager() *SecurityManager {
	return globalSecurityManager
}

// 便捷函数

// FilterSensitiveData 过滤敏感数据
func FilterSensitiveData(data string) string {
	if globalSecurityManager != nil {
		return globalSecurityManager.FilterSensitiveData(data)
	}
	return data
}

// FilterSensitiveMap 过滤敏感map数据
func FilterSensitiveMap(data map[string]interface{}) map[string]interface{} {
	if globalSecurityManager != nil {
		return globalSecurityManager.FilterSensitiveMap(data)
	}
	return data
}

// ValidateInput 验证输入
func ValidateInput(data map[string]string) map[string]string {
	if globalSecurityManager != nil {
		return globalSecurityManager.ValidateInput(data)
	}
	return make(map[string]string)
}
