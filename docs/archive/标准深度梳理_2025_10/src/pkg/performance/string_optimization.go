// Package performance provides advanced string operation optimization utilities.
// This file focuses on high-performance string operations, memory-efficient
// string handling, and advanced string processing patterns for OTLP Go applications.
package performance

import (
	"bytes"
	"context"
	"fmt"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// StringOptimizationManager provides advanced string optimization utilities.
type StringOptimizationManager struct {
	mu              sync.RWMutex
	stringPools     map[string]*StringPool
	builderPools    map[string]*StringBuilderPool
	formatterPools  map[string]*FormatterPool
	parserPools     map[string]*ParserPool
	optimizations   map[string]bool
	metrics         *StringOptimizationMetrics
	tracer          trace.Tracer
	enabledFeatures map[string]bool
}

// StringOptimizationMetrics holds string optimization metrics.
type StringOptimizationMetrics struct {
	StringAllocations   int64
	StringDeallocations int64
	BuilderReuses       int64
	FormatterReuses     int64
	ParserReuses        int64
	Concatenations      int64
	Conversions         int64
	Optimizations       int64
	PoolHits            int64
	PoolMisses          int64
	MemorySaved         int64
	LastUpdateTime      time.Time
}

// StringPool provides optimized string pooling for frequently used strings.
type StringPool struct {
	pool        sync.Pool
	name        string
	maxSize     int
	currentSize int64
	hits        int64
	misses      int64
	stats       *StringPoolStats
}

// StringPoolStats holds string pool statistics.
type StringPoolStats struct {
	TotalRequests int64
	CacheHits     int64
	CacheMisses   int64
	AverageSize   float64
	MaxSize       int64
	MinSize       int64
	MemoryUsage   int64
	Efficiency    float64
}

// StringBuilderPool provides optimized string builder pooling.
type StringBuilderPool struct {
	pool        sync.Pool
	name        string
	maxSize     int
	currentSize int64
	hits        int64
	misses      int64
	stats       *StringBuilderPoolStats
}

// StringBuilderPoolStats holds string builder pool statistics.
type StringBuilderPoolStats struct {
	TotalRequests   int64
	CacheHits       int64
	CacheMisses     int64
	AverageCapacity float64
	MaxCapacity     int64
	MinCapacity     int64
	MemoryUsage     int64
	Efficiency      float64
}

// FormatterPool provides optimized formatter pooling for string formatting.
type FormatterPool struct {
	pool        sync.Pool
	name        string
	maxSize     int
	currentSize int64
	hits        int64
	misses      int64
	stats       *FormatterPoolStats
}

// Get retrieves a formatter from the pool.
func (fp *FormatterPool) Get() interface{} {
	obj := fp.pool.Get()
	if obj != nil {
		atomic.AddInt64(&fp.hits, 1)
		atomic.AddInt64(&fp.currentSize, -1)
	} else {
		atomic.AddInt64(&fp.misses, 1)
	}
	return obj
}

// Put returns a formatter to the pool.
func (fp *FormatterPool) Put(obj interface{}) {
	if obj == nil {
		return
	}

	if atomic.LoadInt64(&fp.currentSize) >= int64(fp.maxSize) {
		return
	}

	fp.pool.Put(obj)
	atomic.AddInt64(&fp.currentSize, 1)
}

// FormatterPoolStats holds formatter pool statistics.
type FormatterPoolStats struct {
	TotalRequests     int64
	CacheHits         int64
	CacheMisses       int64
	AverageFormatTime time.Duration
	MaxFormatTime     time.Duration
	MinFormatTime     time.Duration
	Efficiency        float64
}

// ParserPool provides optimized parser pooling for string parsing.
type ParserPool struct {
	pool        sync.Pool
	name        string
	maxSize     int
	currentSize int64
	hits        int64
	misses      int64
	stats       *ParserPoolStats
}

// ParserPoolStats holds parser pool statistics.
type ParserPoolStats struct {
	TotalRequests    int64
	CacheHits        int64
	CacheMisses      int64
	AverageParseTime time.Duration
	MaxParseTime     time.Duration
	MinParseTime     time.Duration
	Efficiency       float64
}

// FastStringBuilder provides a high-performance string builder implementation.
type FastStringBuilder struct {
	buf      []byte
	length   int
	capacity int
	pooled   bool
	stats    *FastStringBuilderStats
}

// FastStringBuilderStats holds fast string builder statistics.
type FastStringBuilderStats struct {
	TotalOperations      int64
	AppendOperations     int64
	InsertOperations     int64
	DeleteOperations     int64
	ReplaceOperations    int64
	AverageOperationTime time.Duration
	MemoryAllocations    int64
	MemoryReallocations  int64
}

// StringOptimizer provides advanced string optimization utilities.
type StringOptimizer struct {
	manager       *StringOptimizationManager
	optimizations map[string]bool
	stats         *StringOptimizerStats
}

// StringOptimizerStats holds string optimizer statistics.
type StringOptimizerStats struct {
	OptimizationsApplied int64
	MemorySaved          int64
	TimeSaved            time.Duration
	CacheHits            int64
	CacheMisses          int64
	Efficiency           float64
}

// StringFormatter provides optimized string formatting utilities.
type StringFormatter struct {
	pool          *FormatterPool
	optimizations map[string]bool
	stats         *StringFormatterStats
}

// StringFormatterStats holds string formatter statistics.
type StringFormatterStats struct {
	FormatOperations   int64
	TemplateOperations int64
	InterpolationOps   int64
	AverageFormatTime  time.Duration
	MemoryAllocations  int64
	Efficiency         float64
}

// StringParser provides optimized string parsing utilities.
type StringParser struct {
	pool          *ParserPool
	optimizations map[string]bool
	stats         *StringParserStats
}

// StringParserStats holds string parser statistics.
type StringParserStats struct {
	ParseOperations    int64
	TokenizeOperations int64
	SplitOperations    int64
	AverageParseTime   time.Duration
	MemoryAllocations  int64
	Efficiency         float64
}

// NewStringOptimizationManager creates a new string optimization manager.
func NewStringOptimizationManager() *StringOptimizationManager {
	return &StringOptimizationManager{
		stringPools:     make(map[string]*StringPool),
		builderPools:    make(map[string]*StringBuilderPool),
		formatterPools:  make(map[string]*FormatterPool),
		parserPools:     make(map[string]*ParserPool),
		optimizations:   make(map[string]bool),
		metrics:         &StringOptimizationMetrics{},
		tracer:          otel.Tracer("string_optimization"),
		enabledFeatures: make(map[string]bool),
	}
}

// Initialize initializes the string optimization manager.
func (som *StringOptimizationManager) Initialize(ctx context.Context) error {
	_, span := som.tracer.Start(ctx, "string_optimization.initialize")
	defer span.End()

	// Enable default features
	som.enabledFeatures["string_pooling"] = true
	som.enabledFeatures["builder_pooling"] = true
	som.enabledFeatures["formatter_pooling"] = true
	som.enabledFeatures["parser_pooling"] = true
	som.enabledFeatures["fast_builder"] = true
	som.enabledFeatures["optimized_concat"] = true

	// Initialize string pools
	if err := som.initializeStringPools(); err != nil {
		return fmt.Errorf("failed to initialize string pools: %w", err)
	}

	// Initialize builder pools
	if err := som.initializeBuilderPools(); err != nil {
		return fmt.Errorf("failed to initialize builder pools: %w", err)
	}

	// Initialize formatter pools
	if err := som.initializeFormatterPools(); err != nil {
		return fmt.Errorf("failed to initialize formatter pools: %w", err)
	}

	// Initialize parser pools
	if err := som.initializeParserPools(); err != nil {
		return fmt.Errorf("failed to initialize parser pools: %w", err)
	}

	span.SetAttributes(
		attribute.Bool("initialized", true),
		attribute.Int("string_pools", len(som.stringPools)),
		attribute.Int("builder_pools", len(som.builderPools)),
		attribute.Int("formatter_pools", len(som.formatterPools)),
		attribute.Int("parser_pools", len(som.parserPools)),
	)

	return nil
}

// Shutdown gracefully shuts down the string optimization manager.
func (som *StringOptimizationManager) Shutdown(ctx context.Context) error {
	_, span := som.tracer.Start(ctx, "string_optimization.shutdown")
	defer span.End()

	som.mu.Lock()
	defer som.mu.Unlock()

	// Clear all pools
	som.stringPools = make(map[string]*StringPool)
	som.builderPools = make(map[string]*StringBuilderPool)
	som.formatterPools = make(map[string]*FormatterPool)
	som.parserPools = make(map[string]*ParserPool)

	span.SetAttributes(
		attribute.Bool("shutdown_complete", true),
	)

	return nil
}

// CreateStringPool creates a new string pool.
func (som *StringOptimizationManager) CreateStringPool(name string, maxSize int) *StringPool {
	som.mu.Lock()
	defer som.mu.Unlock()

	pool := &StringPool{
		pool: sync.Pool{
			New: func() interface{} {
				return ""
			},
		},
		name:        name,
		maxSize:     maxSize,
		currentSize: 0,
		hits:        0,
		misses:      0,
		stats:       &StringPoolStats{},
	}

	som.stringPools[name] = pool
	return pool
}

// GetStringPool retrieves a string pool by name.
func (som *StringOptimizationManager) GetStringPool(name string) (*StringPool, bool) {
	som.mu.RLock()
	defer som.mu.RUnlock()

	pool, exists := som.stringPools[name]
	return pool, exists
}

// Get retrieves a string from the pool.
func (sp *StringPool) Get() string {
	obj := sp.pool.Get()
	if obj != nil {
		atomic.AddInt64(&sp.hits, 1)
		atomic.AddInt64(&sp.currentSize, -1)
		atomic.AddInt64(&sp.stats.TotalRequests, 1)
		atomic.AddInt64(&sp.stats.CacheHits, 1)
		return obj.(string)
	}

	atomic.AddInt64(&sp.misses, 1)
	atomic.AddInt64(&sp.stats.TotalRequests, 1)
	atomic.AddInt64(&sp.stats.CacheMisses, 1)
	return ""
}

// Put returns a string to the pool.
func (sp *StringPool) Put(str string) {
	if str == "" || atomic.LoadInt64(&sp.currentSize) >= int64(sp.maxSize) {
		return
	}

	sp.pool.Put(&str)
	atomic.AddInt64(&sp.currentSize, 1)
}

// Stats returns pool statistics.
func (sp *StringPool) Stats() *StringPoolStats {
	total := atomic.LoadInt64(&sp.stats.TotalRequests)
	if total > 0 {
		sp.stats.Efficiency = float64(atomic.LoadInt64(&sp.stats.CacheHits)) / float64(total)
	}
	return sp.stats
}

// NewStringBuilderPool creates a new string builder pool.
func (som *StringOptimizationManager) CreateStringBuilderPool(name string, maxSize int) *StringBuilderPool {
	som.mu.Lock()
	defer som.mu.Unlock()

	pool := &StringBuilderPool{
		pool: sync.Pool{
			New: func() interface{} {
				return &strings.Builder{}
			},
		},
		name:        name,
		maxSize:     maxSize,
		currentSize: 0,
		hits:        0,
		misses:      0,
		stats:       &StringBuilderPoolStats{},
	}

	som.builderPools[name] = pool
	return pool
}

// GetStringBuilderPool retrieves a string builder pool by name.
func (som *StringOptimizationManager) GetStringBuilderPool(name string) (*StringBuilderPool, bool) {
	som.mu.RLock()
	defer som.mu.RUnlock()

	pool, exists := som.builderPools[name]
	return pool, exists
}

// Get retrieves a string builder from the pool.
func (sbp *StringBuilderPool) Get() *strings.Builder {
	obj := sbp.pool.Get()
	if obj != nil {
		atomic.AddInt64(&sbp.hits, 1)
		atomic.AddInt64(&sbp.currentSize, -1)
		atomic.AddInt64(&sbp.stats.TotalRequests, 1)
		atomic.AddInt64(&sbp.stats.CacheHits, 1)
		return obj.(*strings.Builder)
	}

	atomic.AddInt64(&sbp.misses, 1)
	atomic.AddInt64(&sbp.stats.TotalRequests, 1)
	atomic.AddInt64(&sbp.stats.CacheMisses, 1)
	return &strings.Builder{}
}

// Put returns a string builder to the pool.
func (sbp *StringBuilderPool) Put(builder *strings.Builder) {
	if builder == nil || atomic.LoadInt64(&sbp.currentSize) >= int64(sbp.maxSize) {
		return
	}

	builder.Reset()
	sbp.pool.Put(builder)
	atomic.AddInt64(&sbp.currentSize, 1)
}

// Stats returns pool statistics.
func (sbp *StringBuilderPool) Stats() *StringBuilderPoolStats {
	total := atomic.LoadInt64(&sbp.stats.TotalRequests)
	if total > 0 {
		sbp.stats.Efficiency = float64(atomic.LoadInt64(&sbp.stats.CacheHits)) / float64(total)
	}
	return sbp.stats
}

// NewFastStringBuilder creates a new fast string builder.
func NewFastStringBuilder(initialCapacity int) *FastStringBuilder {
	if initialCapacity <= 0 {
		initialCapacity = 64
	}

	return &FastStringBuilder{
		buf:      make([]byte, 0, initialCapacity),
		length:   0,
		capacity: initialCapacity,
		pooled:   false,
		stats:    &FastStringBuilderStats{},
	}
}

// Append appends a string to the builder.
func (fsb *FastStringBuilder) Append(str string) *FastStringBuilder {
	start := time.Now()

	// Convert string to bytes for efficient appending
	strBytes := []byte(str)
	fsb.buf = append(fsb.buf, strBytes...)
	fsb.length += len(strBytes)

	// Update capacity if needed
	if cap(fsb.buf) > fsb.capacity {
		fsb.capacity = cap(fsb.buf)
		atomic.AddInt64(&fsb.stats.MemoryReallocations, 1)
	}

	atomic.AddInt64(&fsb.stats.TotalOperations, 1)
	atomic.AddInt64(&fsb.stats.AppendOperations, 1)
	fsb.stats.AverageOperationTime = time.Since(start)

	return fsb
}

// AppendBytes appends bytes to the builder.
func (fsb *FastStringBuilder) AppendBytes(data []byte) *FastStringBuilder {
	start := time.Now()

	fsb.buf = append(fsb.buf, data...)
	fsb.length += len(data)

	// Update capacity if needed
	if cap(fsb.buf) > fsb.capacity {
		fsb.capacity = cap(fsb.buf)
		atomic.AddInt64(&fsb.stats.MemoryReallocations, 1)
	}

	atomic.AddInt64(&fsb.stats.TotalOperations, 1)
	atomic.AddInt64(&fsb.stats.AppendOperations, 1)
	fsb.stats.AverageOperationTime = time.Since(start)

	return fsb
}

// Insert inserts a string at the specified position.
func (fsb *FastStringBuilder) Insert(pos int, str string) *FastStringBuilder {
	if pos < 0 || pos > fsb.length {
		return fsb
	}

	start := time.Now()

	strBytes := []byte(str)
	// Create new buffer with inserted string
	newBuf := make([]byte, 0, fsb.length+len(strBytes))
	newBuf = append(newBuf, fsb.buf[:pos]...)
	newBuf = append(newBuf, strBytes...)
	newBuf = append(newBuf, fsb.buf[pos:]...)

	fsb.buf = newBuf
	fsb.length += len(strBytes)

	atomic.AddInt64(&fsb.stats.TotalOperations, 1)
	atomic.AddInt64(&fsb.stats.InsertOperations, 1)
	fsb.stats.AverageOperationTime = time.Since(start)

	return fsb
}

// Delete deletes characters from the specified range.
func (fsb *FastStringBuilder) Delete(start, end int) *FastStringBuilder {
	if start < 0 || start >= fsb.length || end <= start || end > fsb.length {
		return fsb
	}

	startTime := time.Now()

	// Create new buffer without deleted characters
	newBuf := make([]byte, 0, fsb.length-(end-start))
	newBuf = append(newBuf, fsb.buf[:start]...)
	newBuf = append(newBuf, fsb.buf[end:]...)

	fsb.buf = newBuf
	fsb.length -= (end - start)

	atomic.AddInt64(&fsb.stats.TotalOperations, 1)
	atomic.AddInt64(&fsb.stats.DeleteOperations, 1)
	fsb.stats.AverageOperationTime = time.Since(startTime)

	return fsb
}

// Replace replaces characters in the specified range.
func (fsb *FastStringBuilder) Replace(start, end int, str string) *FastStringBuilder {
	if start < 0 || start >= fsb.length || end <= start || end > fsb.length {
		return fsb
	}

	startTime := time.Now()

	strBytes := []byte(str)
	// Create new buffer with replaced string
	newBuf := make([]byte, 0, fsb.length-(end-start)+len(strBytes))
	newBuf = append(newBuf, fsb.buf[:start]...)
	newBuf = append(newBuf, strBytes...)
	newBuf = append(newBuf, fsb.buf[end:]...)

	fsb.buf = newBuf
	fsb.length = fsb.length - (end - start) + len(strBytes)

	atomic.AddInt64(&fsb.stats.TotalOperations, 1)
	atomic.AddInt64(&fsb.stats.ReplaceOperations, 1)
	fsb.stats.AverageOperationTime = time.Since(startTime)

	return fsb
}

// String returns the built string.
func (fsb *FastStringBuilder) String() string {
	return string(fsb.buf)
}

// Bytes returns the underlying bytes.
func (fsb *FastStringBuilder) Bytes() []byte {
	return fsb.buf
}

// Length returns the current length.
func (fsb *FastStringBuilder) Length() int {
	return fsb.length
}

// Capacity returns the current capacity.
func (fsb *FastStringBuilder) Capacity() int {
	return fsb.capacity
}

// Reset resets the builder.
func (fsb *FastStringBuilder) Reset() {
	fsb.buf = fsb.buf[:0]
	fsb.length = 0
}

// Stats returns builder statistics.
func (fsb *FastStringBuilder) Stats() *FastStringBuilderStats {
	return fsb.stats
}

// NewStringOptimizer creates a new string optimizer.
func NewStringOptimizer(manager *StringOptimizationManager) *StringOptimizer {
	return &StringOptimizer{
		manager:       manager,
		optimizations: make(map[string]bool),
		stats:         &StringOptimizerStats{},
	}
}

// OptimizeConcatenation optimizes string concatenation operations.
func (so *StringOptimizer) OptimizeConcatenation(strs ...string) string {
	if len(strs) == 0 {
		return ""
	}
	if len(strs) == 1 {
		return strs[0]
	}

	start := time.Now()

	// Use fast string builder for optimal performance
	builder := NewFastStringBuilder(estimateTotalLength(strs))
	for _, str := range strs {
		builder.Append(str)
	}

	result := builder.String()

	atomic.AddInt64(&so.stats.OptimizationsApplied, 1)
	so.stats.TimeSaved += time.Since(start)

	return result
}

// OptimizeFormat optimizes string formatting operations.
func (so *StringOptimizer) OptimizeFormat(format string, args ...interface{}) string {
	start := time.Now()

	// Use fast string builder for complex formatting
	builder := NewFastStringBuilder(len(format) + len(args)*10)

	// Simple format optimization - in production, use a proper formatter
	result := fmt.Sprintf(format, args...)
	builder.Append(result)

	atomic.AddInt64(&so.stats.OptimizationsApplied, 1)
	so.stats.TimeSaved += time.Since(start)

	return builder.String()
}

// NewStringFormatter creates a new string formatter.
func NewStringFormatter(pool *FormatterPool) *StringFormatter {
	return &StringFormatter{
		pool:          pool,
		optimizations: make(map[string]bool),
		stats:         &StringFormatterStats{},
	}
}

// Format formats a string using the formatter.
func (sf *StringFormatter) Format(format string, args ...interface{}) string {
	start := time.Now()

	// Use formatter from pool if available
	var formatter *strings.Builder
	if sf.pool != nil {
		formatter = sf.pool.Get().(*strings.Builder)
		defer sf.pool.Put(formatter)
	} else {
		formatter = &strings.Builder{}
	}

	// Format the string
	result := fmt.Sprintf(format, args...)
	formatter.WriteString(result)

	atomic.AddInt64(&sf.stats.FormatOperations, 1)
	sf.stats.AverageFormatTime = time.Since(start)

	return result
}

// NewStringParser creates a new string parser.
func NewStringParser(pool *ParserPool) *StringParser {
	return &StringParser{
		pool:          pool,
		optimizations: make(map[string]bool),
		stats:         &StringParserStats{},
	}
}

// ParseInt parses an integer from a string.
func (sp *StringParser) ParseInt(str string) (int, error) {
	start := time.Now()

	result, err := strconv.Atoi(str)

	atomic.AddInt64(&sp.stats.ParseOperations, 1)
	sp.stats.AverageParseTime = time.Since(start)

	return result, err
}

// ParseFloat parses a float from a string.
func (sp *StringParser) ParseFloat(str string) (float64, error) {
	start := time.Now()

	result, err := strconv.ParseFloat(str, 64)

	atomic.AddInt64(&sp.stats.ParseOperations, 1)
	sp.stats.AverageParseTime = time.Since(start)

	return result, err
}

// Tokenize tokenizes a string by delimiter.
func (sp *StringParser) Tokenize(str, delimiter string) []string {
	start := time.Now()

	tokens := strings.Split(str, delimiter)

	atomic.AddInt64(&sp.stats.TokenizeOperations, 1)
	sp.stats.AverageParseTime = time.Since(start)

	return tokens
}

// Split splits a string by delimiter.
func (sp *StringParser) Split(str, delimiter string) []string {
	start := time.Now()

	parts := strings.Split(str, delimiter)

	atomic.AddInt64(&sp.stats.SplitOperations, 1)
	sp.stats.AverageParseTime = time.Since(start)

	return parts
}

// Helper functions for string optimization

// estimateTotalLength estimates the total length of concatenated strings.
func estimateTotalLength(strs []string) int {
	total := 0
	for _, str := range strs {
		total += len(str)
	}
	return total
}

// Initialize helper functions
func (som *StringOptimizationManager) initializeStringPools() error {
	// Initialize common string pools
	som.CreateStringPool("default", 1000)
	som.CreateStringPool("small", 100)
	som.CreateStringPool("large", 10000)

	return nil
}

func (som *StringOptimizationManager) initializeBuilderPools() error {
	// Initialize common builder pools
	som.CreateStringBuilderPool("default", 100)
	som.CreateStringBuilderPool("small", 50)
	som.CreateStringBuilderPool("large", 500)

	return nil
}

func (som *StringOptimizationManager) initializeFormatterPools() error {
	// Initialize common formatter pools
	som.formatterPools["default"] = &FormatterPool{
		pool: sync.Pool{
			New: func() interface{} {
				return &strings.Builder{}
			},
		},
		name:        "default",
		maxSize:     100,
		currentSize: 0,
		hits:        0,
		misses:      0,
		stats:       &FormatterPoolStats{},
	}

	return nil
}

func (som *StringOptimizationManager) initializeParserPools() error {
	// Initialize common parser pools
	som.parserPools["default"] = &ParserPool{
		pool: sync.Pool{
			New: func() interface{} {
				return &strings.Builder{}
			},
		},
		name:        "default",
		maxSize:     100,
		currentSize: 0,
		hits:        0,
		misses:      0,
		stats:       &ParserPoolStats{},
	}

	return nil
}

// Advanced string optimization utilities

// OptimizeStringAllocation optimizes string allocation patterns.
func OptimizeStringAllocation(strs []string) []string {
	if len(strs) == 0 {
		return strs
	}

	// Pre-allocate slice with known capacity
	optimized := make([]string, 0, len(strs))

	for _, str := range strs {
		// Avoid unnecessary string copies
		if len(str) > 0 {
			optimized = append(optimized, str)
		}
	}

	return optimized
}

// OptimizeStringComparison optimizes string comparison operations.
func OptimizeStringComparison(str1, str2 string) int {
	// Use bytes.Compare for better performance
	return bytes.Compare([]byte(str1), []byte(str2))
}

// OptimizeStringSearch optimizes string search operations.
func OptimizeStringSearch(haystack, needle string) int {
	// Use strings.Index for optimal performance
	return strings.Index(haystack, needle)
}

// OptimizeStringReplace optimizes string replacement operations.
func OptimizeStringReplace(str, old, new string) string {
	// Use strings.ReplaceAll for optimal performance
	return strings.ReplaceAll(str, old, new)
}

// OptimizeStringTrim optimizes string trimming operations.
func OptimizeStringTrim(str string) string {
	// Use strings.TrimSpace for optimal performance
	return strings.TrimSpace(str)
}

// OptimizeStringToLower optimizes string case conversion.
func OptimizeStringToLower(str string) string {
	// Use strings.ToLower for optimal performance
	return strings.ToLower(str)
}

// OptimizeStringToUpper optimizes string case conversion.
func OptimizeStringToUpper(str string) string {
	// Use strings.ToUpper for optimal performance
	return strings.ToUpper(str)
}

// OptimizeStringHasPrefix optimizes string prefix checking.
func OptimizeStringHasPrefix(str, prefix string) bool {
	// Use strings.HasPrefix for optimal performance
	return strings.HasPrefix(str, prefix)
}

// OptimizeStringHasSuffix optimizes string suffix checking.
func OptimizeStringHasSuffix(str, suffix string) bool {
	// Use strings.HasSuffix for optimal performance
	return strings.HasSuffix(str, suffix)
}

// OptimizeStringContains optimizes string containment checking.
func OptimizeStringContains(str, substr string) bool {
	// Use strings.Contains for optimal performance
	return strings.Contains(str, substr)
}

// Performance optimization constants for strings
const (
	DefaultStringPoolSize              = 1000
	DefaultBuilderPoolSize             = 100
	DefaultFormatterPoolSize           = 100
	DefaultParserPoolSize              = 100
	DefaultFastBuilderCapacity         = 64
	DefaultStringOptimizationThreshold = 100
)

// String optimization error types
var (
	ErrStringPoolFull           = fmt.Errorf("string pool is full")
	ErrBuilderPoolFull          = fmt.Errorf("builder pool is full")
	ErrFormatterPoolFull        = fmt.Errorf("formatter pool is full")
	ErrParserPoolFull           = fmt.Errorf("parser pool is full")
	ErrStringOptimizationFailed = fmt.Errorf("string optimization failed")
)
