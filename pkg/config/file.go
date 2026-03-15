package config

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"time"

	"gopkg.in/yaml.v3"
)

// FileSource 文件配置源
type FileSource struct {
	Path     string
	AutoReload bool
	ReloadInterval time.Duration
	mu       sync.RWMutex
	lastMod  time.Time
	watcher  *fileWatcher
}

// NewFileSource 创建文件配置源
func NewFileSource(path string) *FileSource {
	return &FileSource{
		Path:           path,
		AutoReload:     false,
		ReloadInterval: 5 * time.Second,
	}
}

// WithAutoReload 启用自动重载
func (f *FileSource) WithAutoReload(interval time.Duration) *FileSource {
	f.AutoReload = true
	f.ReloadInterval = interval
	return f
}

// Load 实现 Source 接口
func (f *FileSource) Load(ctx context.Context) (map[string]interface{}, error) {
	f.mu.RLock()
	defer f.mu.RUnlock()

	data, err := f.loadFile()
	if err != nil {
		return nil, err
	}

	// 更新最后修改时间
	info, err := os.Stat(f.Path)
	if err == nil {
		f.lastMod = info.ModTime()
	}

	return data, nil
}

// Watch 实现 Source 接口
func (f *FileSource) Watch(ctx context.Context, onChange func()) error {
	if !f.AutoReload {
		return nil
	}

	f.watcher = &fileWatcher{
		path:      f.Path,
		interval:  f.ReloadInterval,
		onChange:  onChange,
		lastMod:   f.lastMod,
	}

	return f.watcher.Start(ctx)
}

// loadFile 加载配置文件
func (f *FileSource) loadFile() (map[string]interface{}, error) {
	content, err := os.ReadFile(f.Path)
	if err != nil {
		return nil, fmt.Errorf("failed to read file %s: %w", f.Path, err)
	}

	ext := filepath.Ext(f.Path)
	switch ext {
	case ".yaml", ".yml":
		return f.parseYAML(content)
	case ".json":
		return f.parseJSON(content)
	default:
		// 尝试自动检测格式
		if data, err := f.parseYAML(content); err == nil {
			return data, nil
		}
		return f.parseJSON(content)
	}
}

// parseYAML 解析 YAML 内容
func (f *FileSource) parseYAML(content []byte) (map[string]interface{}, error) {
	var data map[string]interface{}
	if err := yaml.Unmarshal(content, &data); err != nil {
		return nil, fmt.Errorf("failed to parse YAML: %w", err)
	}
	return normalizeMap(data), nil
}

// parseJSON 解析 JSON 内容
func (f *FileSource) parseJSON(content []byte) (map[string]interface{}, error) {
	var data map[string]interface{}
	if err := json.Unmarshal(content, &data); err != nil {
		return nil, fmt.Errorf("failed to parse JSON: %w", err)
	}
	return normalizeMap(data), nil
}

// normalizeMap 规范化 map 值类型
func normalizeMap(data map[string]interface{}) map[string]interface{} {
	result := make(map[string]interface{})
	for k, v := range data {
		result[k] = normalizeValue(v)
	}
	return result
}

// normalizeValue 规范化值类型
func normalizeValue(v interface{}) interface{} {
	switch val := v.(type) {
	case map[interface{}]interface{}:
		m := make(map[string]interface{})
		for k, v := range val {
			m[fmt.Sprintf("%v", k)] = normalizeValue(v)
		}
		return m
	case map[string]interface{}:
		return normalizeMap(val)
	case []interface{}:
		for i, item := range val {
			val[i] = normalizeValue(item)
		}
		return val
	default:
		return val
	}
}

// fileWatcher 文件监听器
type fileWatcher struct {
	path     string
	interval time.Duration
	onChange func()
	lastMod  time.Time
	stopCh   chan struct{}
}

// Start 启动文件监听
func (w *fileWatcher) Start(ctx context.Context) error {
	w.stopCh = make(chan struct{})

	go func() {
		ticker := time.NewTicker(w.interval)
		defer ticker.Stop()

		for {
			select {
			case <-ctx.Done():
				return
			case <-w.stopCh:
				return
			case <-ticker.C:
				if w.hasChanged() {
					w.onChange()
				}
			}
		}
	}()

	return nil
}

// hasChanged 检查文件是否已更改
func (w *fileWatcher) hasChanged() bool {
	info, err := os.Stat(w.path)
	if err != nil {
		return false
	}

	if info.ModTime().After(w.lastMod) {
		w.lastMod = info.ModTime()
		return true
	}

	return false
}

// Stop 停止文件监听
func (w *fileWatcher) Stop() {
	if w.stopCh != nil {
		close(w.stopCh)
	}
}

// MultiFileSource 多文件配置源
type MultiFileSource struct {
	Paths []string
}

// NewMultiFileSource 创建多文件配置源
func NewMultiFileSource(paths ...string) *MultiFileSource {
	return &MultiFileSource{Paths: paths}
}

// Load 实现 Source 接口
func (m *MultiFileSource) Load(ctx context.Context) (map[string]interface{}, error) {
	result := make(map[string]interface{})

	for _, path := range m.Paths {
		source := NewFileSource(path)
		data, err := source.Load(ctx)
		if err != nil {
			// 文件不存在时跳过
			if os.IsNotExist(err) {
				continue
			}
			return nil, fmt.Errorf("failed to load %s: %w", path, err)
		}

		deepMerge(result, data)
	}

	return result, nil
}

// Watch 实现 Source 接口
func (m *MultiFileSource) Watch(ctx context.Context, onChange func()) error {
	// 多文件源不支持监听，返回 nil
	return nil
}

// SaveToFile 将配置保存到文件
func SaveToFile(config map[string]interface{}, path string) error {
	ext := filepath.Ext(path)

	var content []byte
	var err error

	switch ext {
	case ".yaml", ".yml":
		content, err = yaml.Marshal(config)
	case ".json":
		content, err = json.MarshalIndent(config, "", "  ")
	default:
		return fmt.Errorf("unsupported file format: %s", ext)
	}

	if err != nil {
		return fmt.Errorf("failed to marshal config: %w", err)
	}

	// 创建目录（如果不存在）
	dir := filepath.Dir(path)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return fmt.Errorf("failed to create directory: %w", err)
	}

	if err := os.WriteFile(path, content, 0644); err != nil {
		return fmt.Errorf("failed to write file: %w", err)
	}

	return nil
}

// LoadConfigFile 加载配置文件（便捷函数）
func LoadConfigFile(path string) (Config, error) {
	ctx := context.Background()
	
	manager := New()
	manager.AddSource(NewFileSource(path))
	
	if err := manager.Load(ctx); err != nil {
		return nil, err
	}
	
	return manager, nil
}

// LoadConfigFiles 加载多个配置文件（便捷函数）
func LoadConfigFiles(paths ...string) (Config, error) {
	ctx := context.Background()
	
	manager := New()
	
	for _, path := range paths {
		manager.AddSource(NewFileSource(path))
	}
	
	if err := manager.Load(ctx); err != nil {
		return nil, err
	}
	
	return manager, nil
}

// LoadConfigWithEnv 加载配置文件和环境变量（便捷函数）
func LoadConfigWithEnv(filePath, envPrefix string) (Config, error) {
	ctx := context.Background()
	
	manager := New().
		WithEnvPrefix(envPrefix).
		AddSource(NewFileSource(filePath)).
		AddSource(NewEnvSource(envPrefix))
	
	if err := manager.Load(ctx); err != nil {
		return nil, err
	}
	
	return manager, nil
}

// ConfigFileInfo 配置文件信息
type ConfigFileInfo struct {
	Path       string
	Format     string
	LastMod    time.Time
	Size       int64
	Exists     bool
}

// GetConfigFileInfo 获取配置文件信息
func GetConfigFileInfo(path string) (*ConfigFileInfo, error) {
	info, err := os.Stat(path)
	if err != nil {
		if os.IsNotExist(err) {
			return &ConfigFileInfo{
				Path:   path,
				Format: filepath.Ext(path),
				Exists: false,
			}, nil
		}
		return nil, err
	}

	ext := filepath.Ext(path)
	format := ext
	if format == "" {
		format = "unknown"
	}

	return &ConfigFileInfo{
		Path:    path,
		Format:  format,
		LastMod: info.ModTime(),
		Size:    info.Size(),
		Exists:  true,
	}, nil
}

// SearchConfigFiles 搜索配置文件
func SearchConfigFiles(name string, dirs ...string) []string {
	var found []string

	// 如果没有指定目录，使用默认目录
	if len(dirs) == 0 {
		dirs = []string{
			".",
			"./config",
			"./configs",
			"/etc/otlp",
			os.Getenv("HOME") + "/.config/otlp",
		}
	}

	extensions := []string{".yaml", ".yml", ".json"}

	for _, dir := range dirs {
		for _, ext := range extensions {
			path := filepath.Join(dir, name+ext)
			if _, err := os.Stat(path); err == nil {
				found = append(found, path)
			}
		}
	}

	return found
}
