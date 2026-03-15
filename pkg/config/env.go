package config

import (
	"context"
	"fmt"
	"os"
	"reflect"
	"strconv"
	"strings"
)

// EnvLoader 环境变量加载器
type EnvLoader struct {
	Prefix     string
	KeyBuilder func(prefix, key string) string
}

// NewEnvLoader 创建新的环境变量加载器
func NewEnvLoader(prefix string) *EnvLoader {
	return &EnvLoader{
		Prefix:     prefix,
		KeyBuilder: DefaultKeyBuilder,
	}
}

// DefaultKeyBuilder 默认的键构建器
// 将配置键转换为大写的环境变量名
// 例如: "otel.endpoint" -> "OTEL_ENDPOINT"
func DefaultKeyBuilder(prefix, key string) string {
	// 移除前缀（如果存在）
	key = strings.TrimPrefix(key, prefix)
	key = strings.TrimPrefix(key, "_")
	
	// 将点分隔符替换为下划线
	key = strings.ReplaceAll(key, ".", "_")
	
	// 拼接前缀
	if prefix != "" {
		key = prefix + "_" + key
	}
	
	// 转换为大写
	return strings.ToUpper(key)
}

// Load 从环境变量加载配置到 map
func (e *EnvLoader) Load() (map[string]interface{}, error) {
	result := make(map[string]interface{})
	
	for _, env := range os.Environ() {
		parts := strings.SplitN(env, "=", 2)
		if len(parts) != 2 {
			continue
		}
		
		key := parts[0]
		value := parts[1]
		
		// 检查是否匹配前缀
		if e.Prefix != "" && !strings.HasPrefix(key, e.Prefix) {
			continue
		}
		
		// 转换键名
		configKey := envKeyToConfigKey(key, e.Prefix)
		
		// 解析值
		parsedValue := parseEnvValue(value)
		
		// 设置到结果 map
		setNestedValue(result, configKey, parsedValue)
	}
	
	return result, nil
}

// LoadInto 从环境变量加载配置到结构体
func (e *EnvLoader) LoadInto(target interface{}) error {
	v := reflect.ValueOf(target)
	if v.Kind() != reflect.Ptr || v.IsNil() {
		return fmt.Errorf("target must be a non-nil pointer")
	}
	
	return e.loadIntoValue(v.Elem(), "")
}

// loadIntoValue 递归加载到反射值
func (e *EnvLoader) loadIntoValue(val reflect.Value, prefix string) error {
	typ := val.Type()
	
	for i := 0; i < val.NumField(); i++ {
		field := val.Field(i)
		fieldType := typ.Field(i)
		
		if !field.CanSet() {
			continue
		}
		
		// 获取环境变量标签
		envTag := fieldType.Tag.Get("env")
		if envTag == "-" {
			continue
		}
		
		// 构建环境变量名
		var envKey string
		if envTag != "" {
			envKey = envTag
		} else {
			key := fieldType.Name
			if mapstructureTag := fieldType.Tag.Get("mapstructure"); mapstructureTag != "" {
				parts := strings.Split(mapstructureTag, ",")
				if parts[0] != "" {
					key = parts[0]
				}
			}
			
			if prefix != "" {
				key = prefix + "." + key
			}
			envKey = e.KeyBuilder(e.Prefix, key)
		}
		
		// 检查默认值标签
		defaultTag := fieldType.Tag.Get("default")
		
		// 递归处理嵌套结构体
		if field.Kind() == reflect.Struct {
			var nestedPrefix string
			if mapstructureTag := fieldType.Tag.Get("mapstructure"); mapstructureTag != "" {
				nestedPrefix = mapstructureTag
				if prefix != "" {
					nestedPrefix = prefix + "." + nestedPrefix
				}
			} else {
				nestedPrefix = prefix
			}
			
			if err := e.loadIntoValue(field, nestedPrefix); err != nil {
				return err
			}
			continue
		}
		
		// 获取环境变量值
		envValue := os.Getenv(envKey)
		if envValue == "" && defaultTag != "" {
			envValue = defaultTag
		}
		
		if envValue == "" {
			continue
		}
		
		// 设置字段值
		if err := setFieldFromEnv(field, envValue); err != nil {
			return fmt.Errorf("field %s (env: %s): %w", fieldType.Name, envKey, err)
		}
	}
	
	return nil
}

// envKeyToConfigKey 将环境变量键转换为配置键
func envKeyToConfigKey(envKey, prefix string) string {
	key := envKey
	
	// 移除前缀
	if prefix != "" {
		key = strings.TrimPrefix(key, prefix)
		key = strings.TrimPrefix(key, "_")
	}
	
	// 转换为小写并替换下划线为点
	key = strings.ToLower(key)
	key = strings.ReplaceAll(key, "_", ".")
	
	return key
}

// parseEnvValue 解析环境变量值
func parseEnvValue(value string) interface{} {
	// 尝试解析为布尔值
	if b, err := strconv.ParseBool(value); err == nil {
		return b
	}
	
	// 尝试解析为整数
	if i, err := strconv.ParseInt(value, 10, 64); err == nil {
		return int(i)
	}
	
	// 尝试解析为浮点数
	if f, err := strconv.ParseFloat(value, 64); err == nil {
		return f
	}
	
	// 尝试解析为逗号分隔的列表
	if strings.Contains(value, ",") {
		parts := strings.Split(value, ",")
		result := make([]interface{}, len(parts))
		for i, part := range parts {
			result[i] = strings.TrimSpace(part)
		}
		return result
	}
	
	// 返回字符串
	return value
}

// setFieldFromEnv 从环境变量设置字段值
func setFieldFromEnv(field reflect.Value, value string) error {
	switch field.Kind() {
	case reflect.String:
		field.SetString(value)
		
	case reflect.Bool:
		b, err := strconv.ParseBool(value)
		if err != nil {
			return fmt.Errorf("cannot parse bool: %w", err)
		}
		field.SetBool(b)
		
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		i, err := strconv.ParseInt(value, 10, 64)
		if err != nil {
			return fmt.Errorf("cannot parse int: %w", err)
		}
		field.SetInt(i)
		
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		u, err := strconv.ParseUint(value, 10, 64)
		if err != nil {
			return fmt.Errorf("cannot parse uint: %w", err)
		}
		field.SetUint(u)
		
	case reflect.Float32, reflect.Float64:
		f, err := strconv.ParseFloat(value, 64)
		if err != nil {
			return fmt.Errorf("cannot parse float: %w", err)
		}
		field.SetFloat(f)
		
	case reflect.Slice:
		if field.Type().Elem().Kind() == reflect.String {
			parts := strings.Split(value, ",")
			for i, part := range parts {
				parts[i] = strings.TrimSpace(part)
			}
			field.Set(reflect.ValueOf(parts))
		}
		
	case reflect.Map:
		if field.Type().Key().Kind() == reflect.String &&
		   field.Type().Elem().Kind() == reflect.String {
			m, err := parseKeyValuePairs(value)
			if err != nil {
				return err
			}
			field.Set(reflect.ValueOf(m))
		}
		
	default:
		return fmt.Errorf("unsupported field type: %v", field.Kind())
	}
	
	return nil
}

// parseKeyValuePairs 解析键值对字符串
// 格式: "key1=value1,key2=value2"
func parseKeyValuePairs(s string) (map[string]string, error) {
	result := make(map[string]string)
	
	pairs := strings.Split(s, ",")
	for _, pair := range pairs {
		pair = strings.TrimSpace(pair)
		if pair == "" {
			continue
		}
		
		parts := strings.SplitN(pair, "=", 2)
		if len(parts) != 2 {
			return nil, fmt.Errorf("invalid key-value pair: %s", pair)
		}
		
		key := strings.TrimSpace(parts[0])
		value := strings.TrimSpace(parts[1])
		result[key] = value
	}
	
	return result, nil
}

// loadEnvIntoMap 将环境变量加载到 map
func loadEnvIntoMap(data map[string]interface{}, prefix string) error {
	loader := NewEnvLoader(prefix)
	envData, err := loader.Load()
	if err != nil {
		return err
	}
	
	deepMerge(data, envData)
	return nil
}

// GetEnv 获取环境变量，如果不存在则返回默认值
func GetEnv(key, defaultValue string) string {
	value := os.Getenv(key)
	if value == "" {
		return defaultValue
	}
	return value
}

// GetEnvInt 获取整数环境变量
func GetEnvInt(key string, defaultValue int) int {
	value := os.Getenv(key)
	if value == "" {
		return defaultValue
	}
	
	i, err := strconv.Atoi(value)
	if err != nil {
		return defaultValue
	}
	return i
}

// GetEnvBool 获取布尔环境变量
func GetEnvBool(key string, defaultValue bool) bool {
	value := os.Getenv(key)
	if value == "" {
		return defaultValue
	}
	
	b, err := strconv.ParseBool(value)
	if err != nil {
		return defaultValue
	}
	return b
}

// GetEnvFloat 获取浮点数环境变量
func GetEnvFloat(key string, defaultValue float64) float64 {
	value := os.Getenv(key)
	if value == "" {
		return defaultValue
	}
	
	f, err := strconv.ParseFloat(value, 64)
	if err != nil {
		return defaultValue
	}
	return f
}

// GetEnvSlice 获取切片环境变量
func GetEnvSlice(key string, defaultValue []string) []string {
	value := os.Getenv(key)
	if value == "" {
		return defaultValue
	}
	
	parts := strings.Split(value, ",")
	for i, part := range parts {
		parts[i] = strings.TrimSpace(part)
	}
	return parts
}

// GetEnvMap 获取映射环境变量
func GetEnvMap(key string, defaultValue map[string]string) map[string]string {
	value := os.Getenv(key)
	if value == "" {
		return defaultValue
	}
	
	m, err := parseKeyValuePairs(value)
	if err != nil {
		return defaultValue
	}
	return m
}

// EnvSource 环境变量配置源
type EnvSource struct {
	Prefix string
	Loader *EnvLoader
}

// NewEnvSource 创建环境变量配置源
func NewEnvSource(prefix string) *EnvSource {
	return &EnvSource{
		Prefix: prefix,
		Loader: NewEnvLoader(prefix),
	}
}

// Load 实现 Source 接口
func (s *EnvSource) Load(ctx context.Context) (map[string]interface{}, error) {
	return s.Loader.Load()
}

// Watch 实现 Source 接口（环境变量不支持热重载）
func (s *EnvSource) Watch(ctx context.Context, onChange func()) error {
	// 环境变量不支持监听变化
	// 返回 nil 以允许配置加载，但不会触发热重载
	return nil
}
