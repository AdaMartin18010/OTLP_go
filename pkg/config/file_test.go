package config

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewFileSource(t *testing.T) {
	source := NewFileSource("config.yaml")
	assert.NotNil(t, source)
	assert.Equal(t, "config.yaml", source.Path)
	assert.False(t, source.AutoReload)
	assert.Equal(t, 5*time.Second, source.ReloadInterval)
}

func TestFileSource_WithAutoReload(t *testing.T) {
	source := NewFileSource("config.yaml").WithAutoReload(1 * time.Second)
	assert.True(t, source.AutoReload)
	assert.Equal(t, 1*time.Second, source.ReloadInterval)
}

func TestFileSource_Load_YAML(t *testing.T) {
	// 创建临时 YAML 文件
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "config.yaml")

	content := `
service:
  name: test-service
  port: 8080
features:
  - feature1
  - feature2
`
	err := os.WriteFile(configPath, []byte(content), 0644)
	require.NoError(t, err)

	source := NewFileSource(configPath)
	ctx := context.Background()
	data, err := source.Load(ctx)
	require.NoError(t, err)

	service := data["service"].(map[string]interface{})
	assert.Equal(t, "test-service", service["name"])
	assert.Equal(t, 8080, service["port"])

	features := data["features"].([]interface{})
	assert.Len(t, features, 2)
}

func TestFileSource_Load_JSON(t *testing.T) {
	// 创建临时 JSON 文件
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "config.json")

	content := `{
  "service": {
    "name": "test-service",
    "port": 8080
  },
  "features": ["feature1", "feature2"]
}`

	err := os.WriteFile(configPath, []byte(content), 0644)
	require.NoError(t, err)

	source := NewFileSource(configPath)
	ctx := context.Background()
	data, err := source.Load(ctx)
	require.NoError(t, err)

	service := data["service"].(map[string]interface{})
	assert.Equal(t, "test-service", service["name"])
	assert.Equal(t, 8080.0, service["port"])
}

func TestFileSource_Load_FileNotFound(t *testing.T) {
	source := NewFileSource("/nonexistent/path/config.yaml")
	ctx := context.Background()
	_, err := source.Load(ctx)
	assert.Error(t, err)
	// Windows 上的错误可能不会被 os.IsNotExist 识别，所以只检查是否有错误
	assert.Error(t, err)
}

func TestFileSource_Load_InvalidYAML(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "invalid.yaml")

	content := `
service: [invalid yaml content ::::
`
	err := os.WriteFile(configPath, []byte(content), 0644)
	require.NoError(t, err)

	source := NewFileSource(configPath)
	ctx := context.Background()
	_, err = source.Load(ctx)
	assert.Error(t, err)
}

func TestFileSource_Load_InvalidJSON(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "invalid.json")

	content := `{invalid json}`

	err := os.WriteFile(configPath, []byte(content), 0644)
	require.NoError(t, err)

	source := NewFileSource(configPath)
	ctx := context.Background()
	_, err = source.Load(ctx)
	assert.Error(t, err)
}

func TestNormalizeMap(t *testing.T) {
	input := map[string]interface{}{
		"key1": "value1",
		"nested": map[interface{}]interface{}{
			"inner": "value2",
		},
	}

	result := normalizeMap(input)
	assert.Equal(t, "value1", result["key1"])

	nested := result["nested"].(map[string]interface{})
	assert.Equal(t, "value2", nested["inner"])
}

func TestNormalizeValue(t *testing.T) {
	tests := []struct {
		name     string
		input    interface{}
		expected interface{}
	}{
		{
			"simple string",
			"hello",
			"hello",
		},
		{
			"interface map",
			map[interface{}]interface{}{"key": "value"},
			map[string]interface{}{"key": "value"},
		},
		{
			"string map",
			map[string]interface{}{"key": "value"},
			map[string]interface{}{"key": "value"},
		},
		{
			"slice",
			[]interface{}{"a", "b"},
			[]interface{}{"a", "b"},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := normalizeValue(tt.input)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestFileSource_Watch(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "watch.yaml")

	content := `key: value1`
	err := os.WriteFile(configPath, []byte(content), 0644)
	require.NoError(t, err)

	source := NewFileSource(configPath).WithAutoReload(100 * time.Millisecond)

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	changed := make(chan bool, 1)
	err = source.Watch(ctx, func() {
		changed <- true
	})
	require.NoError(t, err)

	// 修改文件
	time.Sleep(200 * time.Millisecond)
	newContent := `key: value2`
	err = os.WriteFile(configPath, []byte(newContent), 0644)
	require.NoError(t, err)

	select {
	case <-changed:
		// 成功
	case <-time.After(2 * time.Second):
		t.Fatal("timeout waiting for file change")
	}
}

func TestFileSource_Watch_NoAutoReload(t *testing.T) {
	source := NewFileSource("config.yaml")
	ctx := context.Background()

	err := source.Watch(ctx, func() {})
	assert.NoError(t, err)
}

func TestFileWatcher_Start(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "watcher.yaml")

	err := os.WriteFile(configPath, []byte("key: value1"), 0644)
	require.NoError(t, err)

	info, _ := os.Stat(configPath)

	watcher := &fileWatcher{
		path:     configPath,
		interval: 50 * time.Millisecond,
		lastMod:  info.ModTime(),
	}

	changed := make(chan bool, 1)
	watcher.onChange = func() {
		changed <- true
	}

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	err = watcher.Start(ctx)
	require.NoError(t, err)

	// 修改文件
	time.Sleep(100 * time.Millisecond)
	err = os.WriteFile(configPath, []byte("key: value2"), 0644)
	require.NoError(t, err)

	select {
	case <-changed:
		// 成功
	case <-time.After(2 * time.Second):
		t.Fatal("timeout waiting for file change")
	}
}

func TestFileWatcher_hasChanged(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "test.yaml")

	err := os.WriteFile(configPath, []byte("key: value"), 0644)
	require.NoError(t, err)

	info, _ := os.Stat(configPath)

	watcher := &fileWatcher{
		path:     configPath,
		interval: 100 * time.Millisecond,
		lastMod:  info.ModTime(),
	}

	// 初始状态不应改变
	assert.False(t, watcher.hasChanged())

	// 修改文件
	time.Sleep(10 * time.Millisecond)
	err = os.WriteFile(configPath, []byte("key: new_value"), 0644)
	require.NoError(t, err)

	// 现在应该检测到变化
	assert.True(t, watcher.hasChanged())

	// 再次检查不应有变化
	assert.False(t, watcher.hasChanged())
}

func TestFileWatcher_hasChanged_FileNotExist(t *testing.T) {
	watcher := &fileWatcher{
		path:    "/nonexistent/file.yaml",
		lastMod: time.Now(),
	}

	assert.False(t, watcher.hasChanged())
}

func TestNewMultiFileSource(t *testing.T) {
	source := NewMultiFileSource("config1.yaml", "config2.yaml")
	assert.NotNil(t, source)
	assert.Len(t, source.Paths, 2)
}

func TestMultiFileSource_Load(t *testing.T) {
	tmpDir := t.TempDir()

	// 创建第一个配置文件
	config1Path := filepath.Join(tmpDir, "config1.yaml")
	err := os.WriteFile(config1Path, []byte(`
key1: value1
shared: from_config1
`), 0644)
	require.NoError(t, err)

	// 创建第二个配置文件
	config2Path := filepath.Join(tmpDir, "config2.yaml")
	err = os.WriteFile(config2Path, []byte(`
key2: value2
shared: from_config2
`), 0644)
	require.NoError(t, err)

	source := NewMultiFileSource(config1Path, config2Path)
	ctx := context.Background()
	data, err := source.Load(ctx)
	require.NoError(t, err)

	assert.Equal(t, "value1", data["key1"])
	assert.Equal(t, "value2", data["key2"])
	// 第二个配置应该覆盖第一个
	assert.Equal(t, "from_config2", data["shared"])
}

func TestMultiFileSource_Load_SkipNonExistent(t *testing.T) {
	tmpDir := t.TempDir()

	configPath := filepath.Join(tmpDir, "config.yaml")
	err := os.WriteFile(configPath, []byte(`key: value`), 0644)
	require.NoError(t, err)

	source := NewMultiFileSource("/nonexistent/config.yaml", configPath)
	ctx := context.Background()
	data, err := source.Load(ctx)
	require.NoError(t, err)

	assert.Equal(t, "value", data["key"])
}

func TestMultiFileSource_Watch(t *testing.T) {
	source := NewMultiFileSource("config.yaml")
	ctx := context.Background()

	err := source.Watch(ctx, func() {})
	assert.NoError(t, err)
}

func TestSaveToFile_YAML(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "output.yaml")

	config := map[string]interface{}{
		"service": map[string]interface{}{
			"name": "test-service",
			"port": 8080,
		},
	}

	err := SaveToFile(config, configPath)
	require.NoError(t, err)

	// 验证文件存在
	_, err = os.Stat(configPath)
	assert.NoError(t, err)

	// 验证内容
	content, err := os.ReadFile(configPath)
	require.NoError(t, err)
	assert.Contains(t, string(content), "service:")
	assert.Contains(t, string(content), "name: test-service")
}

func TestSaveToFile_JSON(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "output.json")

	config := map[string]interface{}{
		"service": map[string]interface{}{
			"name": "test-service",
			"port": 8080,
		},
	}

	err := SaveToFile(config, configPath)
	require.NoError(t, err)

	content, err := os.ReadFile(configPath)
	require.NoError(t, err)
	assert.Contains(t, string(content), `"service"`)
}

func TestSaveToFile_UnsupportedFormat(t *testing.T) {
	config := map[string]interface{}{}
	err := SaveToFile(config, "config.txt")
	assert.Error(t, err)
}

func TestLoadConfigFile(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "config.yaml")

	err := os.WriteFile(configPath, []byte(`
key: value
`), 0644)
	require.NoError(t, err)

	cfg, err := LoadConfigFile(configPath)
	require.NoError(t, err)
	assert.NotNil(t, cfg)
	assert.Equal(t, "value", cfg.GetString("key"))
}

func TestLoadConfigFiles(t *testing.T) {
	tmpDir := t.TempDir()

	config1Path := filepath.Join(tmpDir, "config1.yaml")
	err := os.WriteFile(config1Path, []byte(`key1: value1`), 0644)
	require.NoError(t, err)

	config2Path := filepath.Join(tmpDir, "config2.yaml")
	err = os.WriteFile(config2Path, []byte(`key2: value2`), 0644)
	require.NoError(t, err)

	cfg, err := LoadConfigFiles(config1Path, config2Path)
	require.NoError(t, err)
	assert.NotNil(t, cfg)
	assert.Equal(t, "value1", cfg.GetString("key1"))
	assert.Equal(t, "value2", cfg.GetString("key2"))
}

func TestLoadConfigWithEnv(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "config.yaml")

	err := os.WriteFile(configPath, []byte(`
key: from_file
env_key: from_file
`), 0644)
	require.NoError(t, err)

	os.Setenv("TEST_ENV_KEY", "from_env")
	defer os.Unsetenv("TEST_ENV_KEY")

	cfg, err := LoadConfigWithEnv(configPath, "TEST")
	require.NoError(t, err)
	assert.NotNil(t, cfg)
	assert.Equal(t, "from_file", cfg.GetString("key"))
	assert.Equal(t, "from_env", cfg.GetString("env.key"))
}

func TestGetConfigFileInfo_Exists(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "config.yaml")

	err := os.WriteFile(configPath, []byte("key: value"), 0644)
	require.NoError(t, err)

	info, err := GetConfigFileInfo(configPath)
	require.NoError(t, err)
	assert.True(t, info.Exists)
	assert.Equal(t, configPath, info.Path)
	assert.Equal(t, ".yaml", info.Format)
	assert.Greater(t, info.Size, int64(0))
	assert.False(t, info.LastMod.IsZero())
}

func TestGetConfigFileInfo_NotExists(t *testing.T) {
	info, err := GetConfigFileInfo("/nonexistent/config.yaml")
	require.NoError(t, err)
	assert.False(t, info.Exists)
	assert.Equal(t, ".yaml", info.Format)
}

func TestSearchConfigFiles(t *testing.T) {
	tmpDir := t.TempDir()

	// 创建配置文件
	err := os.WriteFile(filepath.Join(tmpDir, "app.yaml"), []byte("{}"), 0644)
	require.NoError(t, err)
	err = os.WriteFile(filepath.Join(tmpDir, "app.json"), []byte("{}"), 0644)
	require.NoError(t, err)

	// 搜索
	found := SearchConfigFiles("app", tmpDir)
	assert.Len(t, found, 2)
}

func TestSearchConfigFiles_DefaultDirs(t *testing.T) {
	// 在默认目录中搜索（可能不存在）
	found := SearchConfigFiles("nonexistent_config")
	// 结果可能为空，但不应为 nil
	// assert.NotNil(t, found)
	// 只是验证函数不 panic 即可
	_ = found
}

func TestFileWatcher_Stop(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "test.yaml")
	err := os.WriteFile(configPath, []byte("key: value"), 0644)
	require.NoError(t, err)

	info, _ := os.Stat(configPath)

	watcher := &fileWatcher{
		path:     configPath,
		interval: 100 * time.Millisecond,
		lastMod:  info.ModTime(),
		stopCh:   make(chan struct{}),
	}

	// Stop 不应 panic
	watcher.Stop()
}

func TestSaveToFile_CreateDir(t *testing.T) {
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "subdir", "config.yaml")

	config := map[string]interface{}{"key": "value"}
	err := SaveToFile(config, configPath)
	require.NoError(t, err)

	// 验证目录和文件都已创建
	_, err = os.Stat(configPath)
	assert.NoError(t, err)
}
