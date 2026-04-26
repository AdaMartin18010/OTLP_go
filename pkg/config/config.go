// Package config provides configuration management for the OTLP Go SDK.
//
// This package supports:
//   - Environment variable configuration
//   - File-based configuration (JSON, YAML)
//   - Dynamic configuration reloading
//   - Configuration validation
//
// Example usage:
//
//	cfg, err := config.Load("config.yaml")
//	if err != nil {
//	    log.Fatal(err)
//	}
//
//	endpoint := cfg.GetString("otel.endpoint")
//	timeout := cfg.GetDuration("otel.timeout")
//
// Stability: Stable
// Compliance: OpenTelemetry Specification v1.42.0
package config

import (
	"context"
	"fmt"
	"reflect"
	"strconv"
	"strings"
	"sync"
	"time"
)

// Config 是配置管理器的接口
type Config interface {
	// Get 获取原始值
	Get(key string) interface{}
	// GetString 获取字符串值
	GetString(key string) string
	// GetInt 获取整数值
	GetInt(key string) int
	// GetBool 获取布尔值
	GetBool(key string) bool
	// GetFloat64 获取浮点值
	GetFloat64(key string) float64
	// GetDuration 获取时间间隔值
	GetDuration(key string) time.Duration
	// GetTime 获取时间值
	GetTime(key string) time.Time
	// GetStringSlice 获取字符串切片
	GetStringSlice(key string) []string
	// GetStringMap 获取字符串映射
	GetStringMap(key string) map[string]interface{}
	// IsSet 检查键是否存在
	IsSet(key string) bool
	// Set 设置值
	Set(key string, value interface{})
	// Unmarshal 将配置反序列化到结构体
	Unmarshal(rawVal interface{}) error
	// UnmarshalKey 将特定键反序列化到结构体
	UnmarshalKey(key string, rawVal interface{}) error
	// Watch 监听配置变化
	Watch(ctx context.Context, onChange func(Event)) error
	// Reload 重新加载配置
	Reload(ctx context.Context) error
	// Validate 验证配置
	Validate() error
	// AllSettings 获取所有配置
	AllSettings() map[string]interface{}
}

// Event 表示配置变更事件
type Event struct {
	Key       string
	OldValue  interface{}
	NewValue  interface{}
	Timestamp time.Time
}

// Manager 是配置管理器的实现
type Manager struct {
	data      map[string]interface{}
	defaults  map[string]interface{}
	envPrefix string
	mu        sync.RWMutex
	watchers  []chan Event
	watchMu   sync.RWMutex
	onReload  []func() error
	validator Validator
	sources   []Source
}

// Source 表示配置来源
type Source interface {
	Load(ctx context.Context) (map[string]interface{}, error)
	Watch(ctx context.Context, onChange func()) error
}

// Validator 验证配置
type Validator interface {
	Validate(config map[string]interface{}) error
}

// ValidatorFunc 是验证器函数类型
type ValidatorFunc func(config map[string]interface{}) error

// Validate 实现 Validator 接口
func (f ValidatorFunc) Validate(config map[string]interface{}) error {
	return f(config)
}

// New 创建新的配置管理器
func New() *Manager {
	return &Manager{
		data:      make(map[string]interface{}),
		defaults:  make(map[string]interface{}),
		envPrefix: "OTEL_",
		watchers:  make([]chan Event, 0),
		sources:   make([]Source, 0),
	}
}

// WithEnvPrefix 设置环境变量前缀
func (m *Manager) WithEnvPrefix(prefix string) *Manager {
	m.envPrefix = prefix
	return m
}

// WithDefault 设置默认值
func (m *Manager) WithDefault(key string, value interface{}) *Manager {
	m.defaults[key] = value
	return m
}

// WithDefaults 批量设置默认值
func (m *Manager) WithDefaults(defaults map[string]interface{}) *Manager {
	for k, v := range defaults {
		m.defaults[k] = v
	}
	return m
}

// WithValidator 设置验证器
func (m *Manager) WithValidator(v Validator) *Manager {
	m.validator = v
	return m
}

// AddSource 添加配置源
func (m *Manager) AddSource(source Source) *Manager {
	m.sources = append(m.sources, source)
	return m
}

// OnReload 注册重载回调
func (m *Manager) OnReload(fn func() error) *Manager {
	m.onReload = append(m.onReload, fn)
	return m
}

// Load 从所有源加载配置
func (m *Manager) Load(ctx context.Context) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	// 首先加载默认值
	m.data = make(map[string]interface{})
	for k, v := range m.defaults {
		m.data[k] = v
	}

	// 从所有源加载配置
	for _, source := range m.sources {
		data, err := source.Load(ctx)
		if err != nil {
			return fmt.Errorf("failed to load from source: %w", err)
		}
		deepMerge(m.data, data)
	}

	// 应用环境变量覆盖
	if err := m.loadEnvVars(); err != nil {
		return fmt.Errorf("failed to load environment variables: %w", err)
	}

	// 验证配置
	if m.validator != nil {
		if err := m.validator.Validate(m.data); err != nil {
			return fmt.Errorf("configuration validation failed: %w", err)
		}
	}

	return nil
}

// loadEnvVars 从环境变量加载配置
func (m *Manager) loadEnvVars() error {
	return loadEnvIntoMap(m.data, m.envPrefix)
}

// Reload 重新加载配置
func (m *Manager) Reload(ctx context.Context) error {
	oldData := m.AllSettings()

	if err := m.Load(ctx); err != nil {
		return err
	}

	// 执行重载回调
	for _, fn := range m.onReload {
		if err := fn(); err != nil {
			return fmt.Errorf("reload callback failed: %w", err)
		}
	}

	// 通知监听器
	newData := m.AllSettings()
	m.notifyChanges(oldData, newData)

	return nil
}

// notifyChanges 通知配置变更
func (m *Manager) notifyChanges(oldData, newData map[string]interface{}) {
	changes := diffMaps("", oldData, newData)

	m.watchMu.RLock()
	watchers := make([]chan Event, len(m.watchers))
	copy(watchers, m.watchers)
	m.watchMu.RUnlock()

	for _, change := range changes {
		for _, ch := range watchers {
			select {
			case ch <- change:
			default:
			}
		}
	}
}

// Watch 监听配置变化
func (m *Manager) Watch(ctx context.Context, onChange func(Event)) error {
	ch := make(chan Event, 10)

	m.watchMu.Lock()
	m.watchers = append(m.watchers, ch)
	m.watchMu.Unlock()

	go func() {
		<-ctx.Done()
		m.watchMu.Lock()
		for i, watcher := range m.watchers {
			if watcher == ch {
				m.watchers = append(m.watchers[:i], m.watchers[i+1:]...)
				break
			}
		}
		m.watchMu.Unlock()
		close(ch)
	}()

	go func() {
		for event := range ch {
			onChange(event)
		}
	}()

	// 从所有源监听变化
	for _, source := range m.sources {
		if err := source.Watch(ctx, func() {
			_ = m.Reload(ctx)
		}); err != nil {
			return err
		}
	}

	return nil
}

// Get 获取原始值
func (m *Manager) Get(key string) interface{} {
	m.mu.RLock()
	defer m.mu.RUnlock()

	return getNestedValue(m.data, key)
}

// GetString 获取字符串值
func (m *Manager) GetString(key string) string {
	val := m.Get(key)
	if val == nil {
		return ""
	}

	switch v := val.(type) {
	case string:
		return v
	default:
		return fmt.Sprintf("%v", v)
	}
}

// GetInt 获取整数值
func (m *Manager) GetInt(key string) int {
	val := m.Get(key)
	if val == nil {
		return 0
	}

	switch v := val.(type) {
	case int:
		return v
	case int64:
		return int(v)
	case float64:
		return int(v)
	case string:
		i, _ := strconv.Atoi(v)
		return i
	default:
		return 0
	}
}

// GetBool 获取布尔值
func (m *Manager) GetBool(key string) bool {
	val := m.Get(key)
	if val == nil {
		return false
	}

	switch v := val.(type) {
	case bool:
		return v
	case string:
		b, _ := strconv.ParseBool(v)
		return b
	default:
		return false
	}
}

// GetFloat64 获取浮点值
func (m *Manager) GetFloat64(key string) float64 {
	val := m.Get(key)
	if val == nil {
		return 0
	}

	switch v := val.(type) {
	case float64:
		return v
	case float32:
		return float64(v)
	case int:
		return float64(v)
	case int64:
		return float64(v)
	case string:
		f, _ := strconv.ParseFloat(v, 64)
		return f
	default:
		return 0
	}
}

// GetDuration 获取时间间隔值
func (m *Manager) GetDuration(key string) time.Duration {
	val := m.Get(key)
	if val == nil {
		return 0
	}

	switch v := val.(type) {
	case time.Duration:
		return v
	case string:
		d, _ := time.ParseDuration(v)
		return d
	case int:
		return time.Duration(v)
	case int64:
		return time.Duration(v)
	case float64:
		return time.Duration(v)
	default:
		return 0
	}
}

// GetTime 获取时间值
func (m *Manager) GetTime(key string) time.Time {
	val := m.Get(key)
	if val == nil {
		return time.Time{}
	}

	switch v := val.(type) {
	case time.Time:
		return v
	case string:
		t, _ := time.Parse(time.RFC3339, v)
		return t
	default:
		return time.Time{}
	}
}

// GetStringSlice 获取字符串切片
func (m *Manager) GetStringSlice(key string) []string {
	val := m.Get(key)
	if val == nil {
		return nil
	}

	switch v := val.(type) {
	case []string:
		return v
	case []interface{}:
		result := make([]string, len(v))
		for i, item := range v {
			result[i] = fmt.Sprintf("%v", item)
		}
		return result
	case string:
		return strings.Split(v, ",")
	default:
		return []string{fmt.Sprintf("%v", v)}
	}
}

// GetStringMap 获取字符串映射
func (m *Manager) GetStringMap(key string) map[string]interface{} {
	val := m.Get(key)
	if val == nil {
		return nil
	}

	switch v := val.(type) {
	case map[string]interface{}:
		return v
	case map[interface{}]interface{}:
		result := make(map[string]interface{})
		for k, val := range v {
			result[fmt.Sprintf("%v", k)] = val
		}
		return result
	default:
		return nil
	}
}

// IsSet 检查键是否存在
func (m *Manager) IsSet(key string) bool {
	return m.Get(key) != nil
}

// Set 设置值
func (m *Manager) Set(key string, value interface{}) {
	m.mu.Lock()
	defer m.mu.Unlock()

	oldValue := getNestedValue(m.data, key)
	setNestedValue(m.data, key, value)

	// 通知监听器
	if !reflect.DeepEqual(oldValue, value) {
		m.watchMu.RLock()
		watchers := make([]chan Event, len(m.watchers))
		copy(watchers, m.watchers)
		m.watchMu.RUnlock()

		event := Event{
			Key:       key,
			OldValue:  oldValue,
			NewValue:  value,
			Timestamp: time.Now(),
		}

		for _, ch := range watchers {
			select {
			case ch <- event:
			default:
			}
		}
	}
}

// Unmarshal 将配置反序列化到结构体
func (m *Manager) Unmarshal(rawVal interface{}) error {
	m.mu.RLock()
	defer m.mu.RUnlock()

	return unmarshalMap(m.data, rawVal)
}

// UnmarshalKey 将特定键反序列化到结构体
func (m *Manager) UnmarshalKey(key string, rawVal interface{}) error {
	m.mu.RLock()
	defer m.mu.RUnlock()

	val := getNestedValue(m.data, key)
	if val == nil {
		return fmt.Errorf("key %s not found", key)
	}

	data, ok := val.(map[string]interface{})
	if !ok {
		return fmt.Errorf("key %s is not a map", key)
	}

	return unmarshalMap(data, rawVal)
}

// Validate 验证配置
func (m *Manager) Validate() error {
	if m.validator != nil {
		return m.validator.Validate(m.data)
	}
	return nil
}

// AllSettings 获取所有配置
func (m *Manager) AllSettings() map[string]interface{} {
	m.mu.RLock()
	defer m.mu.RUnlock()

	result := make(map[string]interface{})
	deepCopy(result, m.data)
	return result
}

// Helper functions

// getNestedValue 获取嵌套值
func getNestedValue(data map[string]interface{}, key string) interface{} {
	parts := strings.Split(key, ".")
	current := data

	for i, part := range parts {
		val, ok := current[part]
		if !ok {
			return nil
		}

		if i == len(parts)-1 {
			return val
		}

		next, ok := val.(map[string]interface{})
		if !ok {
			return nil
		}
		current = next
	}

	return nil
}

// setNestedValue 设置嵌套值
func setNestedValue(data map[string]interface{}, key string, value interface{}) {
	parts := strings.Split(key, ".")
	current := data

	for i, part := range parts {
		if i == len(parts)-1 {
			current[part] = value
			return
		}

		if _, ok := current[part]; !ok {
			current[part] = make(map[string]interface{})
		}

		next, ok := current[part].(map[string]interface{})
		if !ok {
			next = make(map[string]interface{})
			current[part] = next
		}
		current = next
	}
}

// deepMerge 深度合并两个 map
func deepMerge(dst, src map[string]interface{}) {
	for key, srcVal := range src {
		if dstVal, ok := dst[key]; ok {
			if srcMap, ok := srcVal.(map[string]interface{}); ok {
				if dstMap, ok := dstVal.(map[string]interface{}); ok {
					deepMerge(dstMap, srcMap)
					continue
				}
			}
		}
		dst[key] = srcVal
	}
}

// deepCopy 深度复制 map
func deepCopy(dst, src map[string]interface{}) {
	for k, v := range src {
		switch val := v.(type) {
		case map[string]interface{}:
			newMap := make(map[string]interface{})
			deepCopy(newMap, val)
			dst[k] = newMap
		default:
			dst[k] = v
		}
	}
}

// diffMaps 比较两个 map 的差异
func diffMaps(prefix string, oldData, newData map[string]interface{}) []Event {
	var changes []Event
	timestamp := time.Now()

	// 检查修改和删除的键
	for key, oldVal := range oldData {
		fullKey := key
		if prefix != "" {
			fullKey = prefix + "." + key
		}

		newVal, exists := newData[key]
		if !exists {
			changes = append(changes, Event{
				Key:       fullKey,
				OldValue:  oldVal,
				NewValue:  nil,
				Timestamp: timestamp,
			})
			continue
		}

		oldMap, oldIsMap := oldVal.(map[string]interface{})
		newMap, newIsMap := newVal.(map[string]interface{})

		if oldIsMap && newIsMap {
			changes = append(changes, diffMaps(fullKey, oldMap, newMap)...)
		} else if !reflect.DeepEqual(oldVal, newVal) {
			changes = append(changes, Event{
				Key:       fullKey,
				OldValue:  oldVal,
				NewValue:  newVal,
				Timestamp: timestamp,
			})
		}
	}

	// 检查新增的键
	for key, newVal := range newData {
		fullKey := key
		if prefix != "" {
			fullKey = prefix + "." + key
		}

		if _, exists := oldData[key]; !exists {
			changes = append(changes, Event{
				Key:       fullKey,
				OldValue:  nil,
				NewValue:  newVal,
				Timestamp: timestamp,
			})
		}
	}

	return changes
}

// unmarshalMap 将 map 反序列化到结构体
func unmarshalMap(data map[string]interface{}, rawVal interface{}) error {
	return decode(data, reflect.ValueOf(rawVal))
}

// decode 解码数据到反射值
func decode(data interface{}, val reflect.Value) error {
	if val.Kind() == reflect.Ptr {
		if val.IsNil() {
			val.Set(reflect.New(val.Type().Elem()))
		}
		return decode(data, reflect.Indirect(val))
	}

	if data == nil {
		return nil
	}

	switch val.Kind() {
	case reflect.Struct:
		return decodeStruct(data, val)
	case reflect.Map:
		return decodeMap(data, val)
	case reflect.Slice:
		return decodeSlice(data, val)
	case reflect.String:
		return decodeString(data, val)
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return decodeInt(data, val)
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return decodeUint(data, val)
	case reflect.Float32, reflect.Float64:
		return decodeFloat(data, val)
	case reflect.Bool:
		return decodeBool(data, val)
	default:
		return fmt.Errorf("unsupported kind: %v", val.Kind())
	}
}

// decodeStruct 解码结构体
func decodeStruct(data interface{}, val reflect.Value) error {
	dataMap, ok := data.(map[string]interface{})
	if !ok {
		return fmt.Errorf("expected map for struct, got %T", data)
	}

	typ := val.Type()
	for i := 0; i < val.NumField(); i++ {
		field := val.Field(i)
		fieldType := typ.Field(i)

		if !field.CanSet() {
			continue
		}

		// 获取字段名
		name := fieldType.Name
		tag := fieldType.Tag.Get("mapstructure")
		if tag != "" {
			parts := strings.Split(tag, ",")
			if parts[0] != "" {
				name = parts[0]
			}
			// 处理 omitempty
			for _, part := range parts[1:] {
				if part == "omitempty" && field.IsZero() {
					continue
				}
			}
		}

		if fieldData, ok := dataMap[name]; ok {
			if err := decode(fieldData, field); err != nil {
				return fmt.Errorf("field %s: %w", name, err)
			}
		}
	}

	return nil
}

// decodeMap 解码映射
func decodeMap(data interface{}, val reflect.Value) error {
	dataMap, ok := data.(map[string]interface{})
	if !ok {
		return fmt.Errorf("expected map, got %T", data)
	}

	if val.IsNil() {
		val.Set(reflect.MakeMap(val.Type()))
	}

	for k, v := range dataMap {
		key := reflect.ValueOf(k)
		elem := reflect.New(val.Type().Elem()).Elem()
		if err := decode(v, elem); err != nil {
			return err
		}
		val.SetMapIndex(key, elem)
	}

	return nil
}

// decodeSlice 解码切片
func decodeSlice(data interface{}, val reflect.Value) error {
	var dataSlice []interface{}

	switch v := data.(type) {
	case []interface{}:
		dataSlice = v
	default:
		return fmt.Errorf("expected slice, got %T", data)
	}

	slice := reflect.MakeSlice(val.Type(), len(dataSlice), len(dataSlice))
	for i, item := range dataSlice {
		if err := decode(item, slice.Index(i)); err != nil {
			return err
		}
	}

	val.Set(slice)
	return nil
}

// decodeString 解码字符串
func decodeString(data interface{}, val reflect.Value) error {
	switch v := data.(type) {
	case string:
		val.SetString(v)
	default:
		val.SetString(fmt.Sprintf("%v", v))
	}
	return nil
}

// decodeInt 解码整数
func decodeInt(data interface{}, val reflect.Value) error {
	switch v := data.(type) {
	case int:
		val.SetInt(int64(v))
	case int64:
		val.SetInt(v)
	case float64:
		val.SetInt(int64(v))
	case string:
		i, err := strconv.ParseInt(v, 10, 64)
		if err != nil {
			return err
		}
		val.SetInt(i)
	default:
		return fmt.Errorf("cannot decode %T to int", data)
	}
	return nil
}

// decodeUint 解码无符号整数
func decodeUint(data interface{}, val reflect.Value) error {
	switch v := data.(type) {
	case int:
		val.SetUint(uint64(v))
	case int64:
		val.SetUint(uint64(v))
	case float64:
		val.SetUint(uint64(v))
	case string:
		u, err := strconv.ParseUint(v, 10, 64)
		if err != nil {
			return err
		}
		val.SetUint(u)
	default:
		return fmt.Errorf("cannot decode %T to uint", data)
	}
	return nil
}

// decodeFloat 解码浮点数
func decodeFloat(data interface{}, val reflect.Value) error {
	switch v := data.(type) {
	case float64:
		val.SetFloat(v)
	case float32:
		val.SetFloat(float64(v))
	case int:
		val.SetFloat(float64(v))
	case int64:
		val.SetFloat(float64(v))
	case string:
		f, err := strconv.ParseFloat(v, 64)
		if err != nil {
			return err
		}
		val.SetFloat(f)
	default:
		return fmt.Errorf("cannot decode %T to float", data)
	}
	return nil
}

// decodeBool 解码布尔值
func decodeBool(data interface{}, val reflect.Value) error {
	switch v := data.(type) {
	case bool:
		val.SetBool(v)
	case string:
		b, err := strconv.ParseBool(v)
		if err != nil {
			return err
		}
		val.SetBool(b)
	default:
		return fmt.Errorf("cannot decode %T to bool", data)
	}
	return nil
}
