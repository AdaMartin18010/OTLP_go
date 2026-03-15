package config

import (
	"context"
	"os"
	"reflect"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNew(t *testing.T) {
	m := New()
	assert.NotNil(t, m)
	assert.NotNil(t, m.data)
	assert.NotNil(t, m.defaults)
	assert.Equal(t, "OTEL_", m.envPrefix)
}

func TestManager_WithEnvPrefix(t *testing.T) {
	m := New().WithEnvPrefix("CUSTOM_")
	assert.Equal(t, "CUSTOM_", m.envPrefix)
}

func TestManager_WithDefault(t *testing.T) {
	m := New().
		WithDefault("key1", "value1").
		WithDefault("key2", 123)

	assert.Equal(t, "value1", m.defaults["key1"])
	assert.Equal(t, 123, m.defaults["key2"])
}

func TestManager_WithDefaults(t *testing.T) {
	defaults := map[string]interface{}{
		"a": 1,
		"b": "two",
	}
	m := New().WithDefaults(defaults)

	assert.Equal(t, 1, m.defaults["a"])
	assert.Equal(t, "two", m.defaults["b"])
}

func TestManager_SetAndGet(t *testing.T) {
	m := New()

	// 设置值
	m.Set("name", "test")
	m.Set("count", 42)
	m.Set("enabled", true)
	m.Set("rate", 3.14)

	// 获取值
	assert.Equal(t, "test", m.GetString("name"))
	assert.Equal(t, 42, m.GetInt("count"))
	assert.Equal(t, true, m.GetBool("enabled"))
	assert.InDelta(t, 3.14, m.GetFloat64("rate"), 0.001)
}

func TestManager_Get_NestedKeys(t *testing.T) {
	m := New()

	m.Set("otel.endpoint", "http://localhost:4317")
	m.Set("otel.timeout", "5s")
	m.Set("otel.batch.max_queue_size", 2048)

	assert.Equal(t, "http://localhost:4317", m.GetString("otel.endpoint"))
	assert.Equal(t, "5s", m.GetString("otel.timeout"))
	assert.Equal(t, 2048, m.GetInt("otel.batch.max_queue_size"))
}

func TestManager_IsSet(t *testing.T) {
	m := New()

	m.Set("existing", "value")

	assert.True(t, m.IsSet("existing"))
	assert.False(t, m.IsSet("non_existing"))
}

func TestManager_GetString(t *testing.T) {
	m := New()

	m.Set("string", "hello")
	m.Set("int", 123)
	m.Set("bool", true)

	assert.Equal(t, "hello", m.GetString("string"))
	assert.Equal(t, "123", m.GetString("int"))
	assert.Equal(t, "true", m.GetString("bool"))
	assert.Equal(t, "", m.GetString("non_existing"))
}

func TestManager_GetInt(t *testing.T) {
	m := New()

	m.Set("int", 42)
	m.Set("int64", int64(100))
	m.Set("float", 3.14)
	m.Set("string_int", "99")

	assert.Equal(t, 42, m.GetInt("int"))
	assert.Equal(t, 100, m.GetInt("int64"))
	assert.Equal(t, 3, m.GetInt("float"))
	assert.Equal(t, 99, m.GetInt("string_int"))
	assert.Equal(t, 0, m.GetInt("non_existing"))
}

func TestManager_GetBool(t *testing.T) {
	m := New()

	m.Set("bool_true", true)
	m.Set("bool_false", false)
	m.Set("string_true", "true")
	m.Set("string_false", "false")

	assert.True(t, m.GetBool("bool_true"))
	assert.False(t, m.GetBool("bool_false"))
	assert.True(t, m.GetBool("string_true"))
	assert.False(t, m.GetBool("string_false"))
	assert.False(t, m.GetBool("non_existing"))
}

func TestManager_GetFloat64(t *testing.T) {
	m := New()

	m.Set("float", 3.14)
	m.Set("int", 42)
	m.Set("string", "2.718")

	assert.InDelta(t, 3.14, m.GetFloat64("float"), 0.001)
	assert.InDelta(t, 42.0, m.GetFloat64("int"), 0.001)
	assert.InDelta(t, 2.718, m.GetFloat64("string"), 0.001)
}

func TestManager_GetDuration(t *testing.T) {
	m := New()

	m.Set("duration", 5*time.Second)
	m.Set("string", "10m")
	m.Set("int", 3000)

	assert.Equal(t, 5*time.Second, m.GetDuration("duration"))
	assert.Equal(t, 10*time.Minute, m.GetDuration("string"))
	assert.Equal(t, 3000, m.GetDuration("int"))
}

func TestManager_GetTime(t *testing.T) {
	m := New()

	now := time.Now().Truncate(time.Second)
	m.Set("time", now)
	m.Set("string", now.Format(time.RFC3339))

	assert.True(t, m.GetTime("time").Equal(now))
	assert.True(t, m.GetTime("string").Equal(now))
}

func TestManager_GetStringSlice(t *testing.T) {
	m := New()

	m.Set("slice", []string{"a", "b", "c"})
	m.Set("interface_slice", []interface{}{"x", "y", "z"})
	m.Set("string", "a,b,c")

	assert.Equal(t, []string{"a", "b", "c"}, m.GetStringSlice("slice"))
	assert.Equal(t, []string{"x", "y", "z"}, m.GetStringSlice("interface_slice"))
	assert.Equal(t, []string{"a", "b", "c"}, m.GetStringSlice("string"))
}

func TestManager_GetStringMap(t *testing.T) {
	m := New()

	m.Set("map", map[string]interface{}{"a": 1, "b": 2})
	m.Set("interface_map", map[interface{}]interface{}{"x": "value"})

	assert.Equal(t, map[string]interface{}{"a": 1, "b": 2}, m.GetStringMap("map"))
	assert.NotNil(t, m.GetStringMap("interface_map"))
}

func TestManager_AllSettings(t *testing.T) {
	m := New()

	m.Set("key1", "value1")
	m.Set("key2", 123)
	m.Set("nested.key", "nested_value")

	settings := m.AllSettings()

	assert.Equal(t, "value1", settings["key1"])
	assert.Equal(t, 123, settings["key2"])
	assert.NotNil(t, settings["nested"])
}

func TestManager_Load_WithDefaults(t *testing.T) {
	ctx := context.Background()
	m := New().
		WithDefault("key1", "default1").
		WithDefault("key2", 42)

	err := m.Load(ctx)
	require.NoError(t, err)

	assert.Equal(t, "default1", m.GetString("key1"))
	assert.Equal(t, 42, m.GetInt("key2"))
}

func TestManager_Validate(t *testing.T) {
	validator := ValidatorFunc(func(config map[string]interface{}) error {
		if config["required"] == nil {
			return assert.AnError
		}
		return nil
	})

	m := New().WithValidator(validator)
	m.Set("required", "value")

	err := m.Validate()
	assert.NoError(t, err)
}

func TestManager_Validate_Fail(t *testing.T) {
	validator := ValidatorFunc(func(config map[string]interface{}) error {
		return assert.AnError
	})

	m := New().WithValidator(validator)

	err := m.Load(context.Background())
	assert.Error(t, err)
}

func TestManager_Watch(t *testing.T) {
	m := New()
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	var receivedEvent Event
	done := make(chan bool)

	err := m.Watch(ctx, func(event Event) {
		receivedEvent = event
		done <- true
	})
	require.NoError(t, err)

	// 设置值以触发事件
	go func() {
		m.Set("test_key", "test_value")
	}()

	select {
	case <-done:
		assert.Equal(t, "test_key", receivedEvent.Key)
		assert.Equal(t, "test_value", receivedEvent.NewValue)
	case <-time.After(time.Second):
		t.Fatal("timeout waiting for event")
	}
}

func TestManager_Reload(t *testing.T) {
	ctx := context.Background()
	m := New()
	m.Set("key", "old_value")

	callbackCalled := false
	m.OnReload(func() error {
		callbackCalled = true
		return nil
	})

	err := m.Reload(ctx)
	require.NoError(t, err)

	assert.True(t, callbackCalled)
}

func TestManager_Unmarshal(t *testing.T) {
	m := New()
	m.Set("name", "test_service")
	m.Set("version", "1.0.0")
	m.Set("port", 8080)
	m.Set("debug", true)

	type Config struct {
		Name    string `mapstructure:"name"`
		Version string `mapstructure:"version"`
		Port    int    `mapstructure:"port"`
		Debug   bool   `mapstructure:"debug"`
	}

	var cfg Config
	err := m.Unmarshal(&cfg)
	require.NoError(t, err)

	assert.Equal(t, "test_service", cfg.Name)
	assert.Equal(t, "1.0.0", cfg.Version)
	assert.Equal(t, 8080, cfg.Port)
	assert.True(t, cfg.Debug)
}

func TestManager_Unmarshal_Nested(t *testing.T) {
	m := New()
	m.Set("server.host", "localhost")
	m.Set("server.port", 8080)

	type ServerConfig struct {
		Host string `mapstructure:"host"`
		Port int    `mapstructure:"port"`
	}

	type Config struct {
		Server ServerConfig `mapstructure:"server"`
	}

	var cfg Config
	err := m.Unmarshal(&cfg)
	require.NoError(t, err)

	assert.Equal(t, "localhost", cfg.Server.Host)
	assert.Equal(t, 8080, cfg.Server.Port)
}

func TestManager_UnmarshalKey(t *testing.T) {
	m := New()
	m.Set("server.host", "localhost")
	m.Set("server.port", 8080)

	type ServerConfig struct {
		Host string `mapstructure:"host"`
		Port int    `mapstructure:"port"`
	}

	var cfg ServerConfig
	err := m.UnmarshalKey("server", &cfg)
	require.NoError(t, err)

	assert.Equal(t, "localhost", cfg.Host)
	assert.Equal(t, 8080, cfg.Port)
}

func TestGetNestedValue(t *testing.T) {
	data := map[string]interface{}{
		"level1": map[string]interface{}{
			"level2": map[string]interface{}{
				"key": "value",
			},
		},
	}

	assert.Equal(t, "value", getNestedValue(data, "level1.level2.key"))
	assert.NotNil(t, getNestedValue(data, "level1.level2"))
	assert.Nil(t, getNestedValue(data, "nonexistent"))
	assert.Nil(t, getNestedValue(data, "level1.nonexistent"))
}

func TestSetNestedValue(t *testing.T) {
	data := make(map[string]interface{})

	setNestedValue(data, "a.b.c", "value")

	assert.NotNil(t, data["a"])
	a := data["a"].(map[string]interface{})
	assert.NotNil(t, a["b"])
	b := a["b"].(map[string]interface{})
	assert.Equal(t, "value", b["c"])
}

func TestDeepMerge(t *testing.T) {
	dst := map[string]interface{}{
		"a": 1,
		"b": map[string]interface{}{
			"x": 10,
		},
	}

	src := map[string]interface{}{
		"b": map[string]interface{}{
			"y": 20,
		},
		"c": 3,
	}

	deepMerge(dst, src)

	assert.Equal(t, 1, dst["a"])
	assert.Equal(t, 3, dst["c"])

	b := dst["b"].(map[string]interface{})
	assert.Equal(t, 10, b["x"])
	assert.Equal(t, 20, b["y"])
}

func TestDeepCopy(t *testing.T) {
	src := map[string]interface{}{
		"a": 1,
		"b": map[string]interface{}{
			"x": 10,
		},
	}

	dst := make(map[string]interface{})
	deepCopy(dst, src)

	// 修改源不应影响副本
	src["a"] = 100
	src["b"].(map[string]interface{})["x"] = 100

	assert.Equal(t, 1, dst["a"])
	b := dst["b"].(map[string]interface{})
	assert.Equal(t, 10, b["x"])
}

func TestDiffMaps(t *testing.T) {
	oldData := map[string]interface{}{
		"a": 1,
		"b": 2,
	}

	newData := map[string]interface{}{
		"a": 1,
		"b": 20,
		"c": 3,
	}

	changes := diffMaps("", oldData, newData)

	assert.Len(t, changes, 2)

	keys := make(map[string]bool)
	for _, change := range changes {
		keys[change.Key] = true
	}

	assert.True(t, keys["b"])
	assert.True(t, keys["c"])
}

func TestDecode(t *testing.T) {
	tests := []struct {
		name     string
		data     interface{}
		expected interface{}
	}{
		{"string", "hello", "hello"},
		{"int", 42, 42},
		{"bool", true, true},
		{"float", 3.14, 3.14},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			var result interface{}
			val := reflect.New(reflect.TypeOf(tt.expected))
			err := decode(tt.data, val.Elem())
			require.NoError(t, err)
			assert.Equal(t, tt.expected, val.Elem().Interface())
		})
	}
}

func TestIntegration_WithEnvironmentVariables(t *testing.T) {
	// 设置测试环境变量
	os.Setenv("OTEL_SERVICE_NAME", "test_service")
	os.Setenv("OTEL_EXPORTER_OTLP_ENDPOINT", "http://test:4317")
	defer os.Unsetenv("OTEL_SERVICE_NAME")
	defer os.Unsetenv("OTEL_EXPORTER_OTLP_ENDPOINT")

	ctx := context.Background()
	m := New().WithEnvPrefix("OTEL")
	m.Set("service_name", "default_name")

	err := m.Load(ctx)
	require.NoError(t, err)

	// 环境变量应该覆盖设置的值
	assert.Equal(t, "test_service", m.GetString("service_name"))
	assert.Equal(t, "http://test:4317", m.GetString("exporter_otlp_endpoint"))
}

func TestManager_ConcurrentAccess(t *testing.T) {
	m := New()

	// 并发写入
	done := make(chan bool, 100)
	for i := 0; i < 50; i++ {
		go func(n int) {
			m.Set("counter", n)
			done <- true
		}(i)
	}

	// 并发读取
	for i := 0; i < 50; i++ {
		go func() {
			_ = m.GetInt("counter")
			done <- true
		}()
	}

	// 等待所有 goroutine 完成
	for i := 0; i < 100; i++ {
		<-done
	}
}
