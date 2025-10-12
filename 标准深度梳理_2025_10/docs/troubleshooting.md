# 故障排除指南

## 📋 概述

本文档提供了OTLP Go项目的故障排除指南，包括常见问题、诊断方法、解决方案和预防措施。

## 🔍 故障分类

### 1. 系统故障

#### 服务启动失败

**症状**:

- 服务无法启动
- 启动后立即退出
- 端口绑定失败

**诊断方法**:

```bash
# 查看服务状态
systemctl status otlp-go-service

# 查看启动日志
journalctl -u otlp-go-service -f

# 检查端口占用
netstat -tlnp | grep 8080
lsof -i :8080

# 检查进程
ps aux | grep otlp-go
```

**常见原因**:

1. 端口被占用
2. 配置文件错误
3. 依赖服务未启动
4. 权限不足
5. 资源不足

**解决方案**:

```bash
# 1. 释放端口
sudo fuser -k 8080/tcp

# 2. 验证配置文件
otlp-go --config-check

# 3. 启动依赖服务
docker-compose up -d postgres redis

# 4. 检查权限
ls -la /var/log/otlp-go/
chown -R otlp-go:otlp-go /var/log/otlp-go/

# 5. 检查资源
free -h
df -h
```

#### 内存泄漏

**症状**:

- 内存使用持续增长
- 系统响应变慢
- OOM错误

**诊断方法**:

```bash
# 查看内存使用
free -h
cat /proc/meminfo

# 查看进程内存
ps aux --sort=-%mem | head -10

# 使用pprof分析
go tool pprof http://localhost:8080/debug/pprof/heap

# 查看GC统计
curl http://localhost:8080/debug/vars | grep gc
```

**解决方案**:

```go
// 1. 优化内存分配
func optimizeMemoryAllocation() {
    // 使用对象池
    pool := sync.Pool{
        New: func() interface{} {
            return make([]byte, 1024)
        },
    }
    
    // 重用对象
    buf := pool.Get().([]byte)
    defer pool.Put(buf)
}

// 2. 及时释放资源
func cleanupResources() {
    if db != nil {
        db.Close()
    }
    if redis != nil {
        redis.Close()
    }
}

// 3. 设置内存限制
func setMemoryLimit() {
    var m runtime.MemStats
    runtime.ReadMemStats(&m)
    
    if m.Alloc > 100*1024*1024 { // 100MB
        runtime.GC()
    }
}
```

#### CPU使用率过高

**症状**:

- CPU使用率持续100%
- 系统响应缓慢
- 请求超时

**诊断方法**:

```bash
# 查看CPU使用
top -p $(pgrep otlp-go)
htop

# 使用pprof分析
go tool pprof http://localhost:8080/debug/pprof/profile

# 查看系统调用
strace -p $(pgrep otlp-go)

# 查看热点函数
go tool pprof -list=main http://localhost:8080/debug/pprof/profile
```

**解决方案**:

```go
// 1. 优化算法复杂度
func optimizeAlgorithm() {
    // 使用更高效的算法
    sort.Slice(items, func(i, j int) bool {
        return items[i].Priority > items[j].Priority
    })
}

// 2. 使用并发处理
func concurrentProcessing() {
    var wg sync.WaitGroup
    semaphore := make(chan struct{}, 10) // 限制并发数
    
    for _, item := range items {
        wg.Add(1)
        go func(item Item) {
            defer wg.Done()
            semaphore <- struct{}{}
            defer func() { <-semaphore }()
            
            processItem(item)
        }(item)
    }
    
    wg.Wait()
}

// 3. 缓存计算结果
func cacheResults() {
    cache := make(map[string]interface{})
    
    func getCachedResult(key string) interface{} {
        if result, exists := cache[key]; exists {
            return result
        }
        
        result := expensiveCalculation(key)
        cache[key] = result
        return result
    }
}
```

### 2. 网络故障

#### 连接超时

**症状**:

- 请求超时
- 连接被拒绝
- 网络不可达

**诊断方法**:

```bash
# 测试网络连接
ping google.com
telnet target-host 8080
nc -zv target-host 8080

# 查看网络统计
netstat -i
ss -tuln

# 检查防火墙
iptables -L
ufw status

# 使用traceroute
traceroute target-host
```

**解决方案**:

```go
// 1. 设置连接超时
func setConnectionTimeout() {
    client := &http.Client{
        Timeout: 30 * time.Second,
        Transport: &http.Transport{
            DialTimeout:         10 * time.Second,
            TLSHandshakeTimeout: 10 * time.Second,
            IdleConnTimeout:     30 * time.Second,
        },
    }
}

// 2. 实现重试机制
func retryRequest() {
    maxRetries := 3
    backoff := time.Second
    
    for i := 0; i < maxRetries; i++ {
        resp, err := client.Do(req)
        if err == nil {
            return resp, nil
        }
        
        if i < maxRetries-1 {
            time.Sleep(backoff)
            backoff *= 2
        }
    }
    
    return nil, fmt.Errorf("max retries exceeded")
}

// 3. 使用连接池
func useConnectionPool() {
    transport := &http.Transport{
        MaxIdleConns:        100,
        MaxIdleConnsPerHost: 10,
        IdleConnTimeout:     90 * time.Second,
    }
    
    client := &http.Client{Transport: transport}
}
```

#### DNS解析失败

**症状**:

- 域名解析失败
- 服务发现失败
- 配置错误

**诊断方法**:

```bash
# 测试DNS解析
nslookup example.com
dig example.com
host example.com

# 检查DNS配置
cat /etc/resolv.conf
systemctl status systemd-resolved

# 使用Go测试DNS
go run -c 'package main; import "net"; func main() { _, err := net.LookupHost("example.com"); println(err) }'
```

**解决方案**:

```go
// 1. 使用自定义DNS解析器
func customDNSResolver() {
    resolver := &net.Resolver{
        PreferGo: true,
        Dial: func(ctx context.Context, network, address string) (net.Conn, error) {
            d := net.Dialer{
                Timeout: 5 * time.Second,
            }
            return d.DialContext(ctx, network, "8.8.8.8:53")
        },
    }
    
    ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
    defer cancel()
    
    addrs, err := resolver.LookupHost(ctx, "example.com")
    if err != nil {
        log.Printf("DNS lookup failed: %v", err)
        return
    }
    
    log.Printf("Resolved addresses: %v", addrs)
}

// 2. 实现DNS缓存
func dnsCache() {
    cache := make(map[string][]string)
    cacheExpiry := make(map[string]time.Time)
    
    func lookupWithCache(hostname string) ([]string, error) {
        if addrs, exists := cache[hostname]; exists {
            if time.Now().Before(cacheExpiry[hostname]) {
                return addrs, nil
            }
        }
        
        addrs, err := net.LookupHost(hostname)
        if err != nil {
            return nil, err
        }
        
        cache[hostname] = addrs
        cacheExpiry[hostname] = time.Now().Add(5 * time.Minute)
        
        return addrs, nil
    }
}
```

### 3. 数据库故障

#### 连接池耗尽

**症状**:

- 数据库连接失败
- 连接超时
- 性能下降

**诊断方法**:

```bash
# 查看数据库连接
psql -c "SELECT * FROM pg_stat_activity;"
mysql -e "SHOW PROCESSLIST;"

# 查看连接池配置
grep -r "max_connections" /etc/postgresql/
grep -r "max_connections" /etc/mysql/

# 监控连接数
watch -n 1 'psql -c "SELECT count(*) FROM pg_stat_activity;"'
```

**解决方案**:

```go
// 1. 优化连接池配置
func optimizeConnectionPool() {
    db, err := sql.Open("postgres", "postgres://user:pass@localhost/dbname?sslmode=disable")
    if err != nil {
        log.Fatal(err)
    }
    
    // 设置连接池参数
    db.SetMaxOpenConns(25)
    db.SetMaxIdleConns(5)
    db.SetConnMaxLifetime(5 * time.Minute)
    db.SetConnMaxIdleTime(1 * time.Minute)
}

// 2. 实现连接健康检查
func connectionHealthCheck() {
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()
    
    for range ticker.C {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        
        if err := db.PingContext(ctx); err != nil {
            log.Printf("Database health check failed: %v", err)
            // 实现重连逻辑
        }
    }
}

// 3. 使用连接复用
func connectionReuse() {
    var db *sql.DB
    var mu sync.RWMutex
    
    func getDB() *sql.DB {
        mu.RLock()
        if db != nil {
            mu.RUnlock()
            return db
        }
        mu.RUnlock()
        
        mu.Lock()
        defer mu.Unlock()
        
        if db == nil {
            var err error
            db, err = sql.Open("postgres", dsn)
            if err != nil {
                log.Fatal(err)
            }
        }
        
        return db
    }
}
```

#### 查询性能问题

**症状**:

- 查询响应慢
- 数据库CPU使用率高
- 锁等待时间长

**诊断方法**:

```sql
-- PostgreSQL查询分析
EXPLAIN ANALYZE SELECT * FROM orders WHERE user_id = '12345';

-- 查看慢查询
SELECT query, mean_time, calls 
FROM pg_stat_statements 
ORDER BY mean_time DESC 
LIMIT 10;

-- 查看锁等待
SELECT * FROM pg_locks WHERE NOT granted;

-- MySQL查询分析
EXPLAIN SELECT * FROM orders WHERE user_id = '12345';

-- 查看慢查询日志
SHOW VARIABLES LIKE 'slow_query_log';
SHOW VARIABLES LIKE 'long_query_time';
```

**解决方案**:

```go
// 1. 优化查询语句
func optimizeQuery() {
    // 使用索引
    query := `SELECT * FROM orders WHERE user_id = $1 AND created_at > $2`
    
    // 限制结果集
    query = `SELECT * FROM orders WHERE user_id = $1 ORDER BY created_at DESC LIMIT 100`
    
    // 使用分页
    query = `SELECT * FROM orders WHERE user_id = $1 ORDER BY created_at DESC LIMIT $2 OFFSET $3`
}

// 2. 实现查询缓存
func queryCache() {
    cache := make(map[string]interface{})
    cacheExpiry := make(map[string]time.Time)
    
    func cachedQuery(key string, queryFunc func() (interface{}, error)) (interface{}, error) {
        if result, exists := cache[key]; exists {
            if time.Now().Before(cacheExpiry[key]) {
                return result, nil
            }
        }
        
        result, err := queryFunc()
        if err != nil {
            return nil, err
        }
        
        cache[key] = result
        cacheExpiry[key] = time.Now().Add(5 * time.Minute)
        
        return result, nil
    }
}

// 3. 使用批量操作
func batchOperations() {
    func batchInsert(orders []Order) error {
        tx, err := db.Begin()
        if err != nil {
            return err
        }
        defer tx.Rollback()
        
        stmt, err := tx.Prepare(`INSERT INTO orders (id, user_id, total, status) VALUES ($1, $2, $3, $4)`)
        if err != nil {
            return err
        }
        defer stmt.Close()
        
        for _, order := range orders {
            _, err = stmt.Exec(order.ID, order.UserID, order.Total, order.Status)
            if err != nil {
                return err
            }
        }
        
        return tx.Commit()
    }
}
```

### 4. 缓存故障

#### Redis连接失败

**症状**:

- Redis连接超时
- 缓存操作失败
- 性能下降

**诊断方法**:

```bash
# 测试Redis连接
redis-cli ping
telnet redis-host 6379

# 查看Redis状态
redis-cli info
redis-cli monitor

# 检查Redis配置
redis-cli config get "*"
```

**解决方案**:

```go
// 1. 实现Redis重连机制
func redisReconnect() {
    var client *redis.Client
    var mu sync.RWMutex
    
    func getRedisClient() *redis.Client {
        mu.RLock()
        if client != nil {
            mu.RUnlock()
            return client
        }
        mu.RUnlock()
        
        mu.Lock()
        defer mu.Unlock()
        
        if client == nil {
            client = redis.NewClient(&redis.Options{
                Addr:         "localhost:6379",
                Password:     "",
                DB:           0,
                PoolSize:     10,
                MinIdleConns: 5,
                MaxRetries:   3,
                DialTimeout:  5 * time.Second,
                ReadTimeout:  3 * time.Second,
                WriteTimeout: 3 * time.Second,
            })
        }
        
        return client
    }
}

// 2. 实现缓存降级
func cacheFallback() {
    func getWithFallback(key string) (string, error) {
        // 尝试从缓存获取
        val, err := redisClient.Get(key).Result()
        if err == nil {
            return val, nil
        }
        
        // 缓存失败，从数据库获取
        val, err = getFromDatabase(key)
        if err != nil {
            return "", err
        }
        
        // 异步更新缓存
        go func() {
            redisClient.Set(key, val, 5*time.Minute)
        }()
        
        return val, nil
    }
}

// 3. 使用本地缓存作为备份
func localCacheBackup() {
    localCache := make(map[string]interface{})
    localCacheExpiry := make(map[string]time.Time)
    
    func getWithLocalBackup(key string) (interface{}, error) {
        // 尝试从Redis获取
        val, err := redisClient.Get(key).Result()
        if err == nil {
            return val, nil
        }
        
        // 尝试从本地缓存获取
        if val, exists := localCache[key]; exists {
            if time.Now().Before(localCacheExpiry[key]) {
                return val, nil
            }
        }
        
        // 从数据库获取
        val, err = getFromDatabase(key)
        if err != nil {
            return nil, err
        }
        
        // 更新本地缓存
        localCache[key] = val
        localCacheExpiry[key] = time.Now().Add(1 * time.Minute)
        
        return val, nil
    }
}
```

### 5. 监控故障

#### OpenTelemetry数据丢失

**症状**:

- 追踪数据不完整
- 指标数据缺失
- 日志收集失败

**诊断方法**:

```bash
# 检查OpenTelemetry Collector状态
docker logs otel-collector
kubectl logs deployment/otel-collector -n monitoring

# 检查数据导出
curl http://localhost:4317/v1/traces
curl http://localhost:4317/v1/metrics

# 查看Jaeger UI
open http://localhost:16686

# 检查Prometheus指标
curl http://localhost:9090/api/v1/query?query=up
```

**解决方案**:

```go
// 1. 实现数据重试机制
func retryExport() {
    exporter := otlptracegrpc.New(
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{
            Enabled:         true,
            InitialInterval: 1 * time.Second,
            MaxInterval:     30 * time.Second,
            MaxElapsedTime:  5 * time.Minute,
        }),
    )
}

// 2. 实现本地缓冲
func localBuffer() {
    buffer := make([]trace.Span, 0, 1000)
    var mu sync.Mutex
    
    func addToBuffer(span trace.Span) {
        mu.Lock()
        defer mu.Unlock()
        
        buffer = append(buffer, span)
        
        if len(buffer) >= 1000 {
            go flushBuffer()
        }
    }
    
    func flushBuffer() {
        mu.Lock()
        spans := make([]trace.Span, len(buffer))
        copy(spans, buffer)
        buffer = buffer[:0]
        mu.Unlock()
        
        // 发送到收集器
        for _, span := range spans {
            // 实现发送逻辑
        }
    }
}

// 3. 实现健康检查
func healthCheck() {
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()
    
    for range ticker.C {
        // 检查追踪器状态
        if tracer == nil {
            log.Printf("Tracer is nil, reinitializing...")
            initializeTracer()
        }
        
        // 检查指标器状态
        if meter == nil {
            log.Printf("Meter is nil, reinitializing...")
            initializeMeter()
        }
    }
}
```

## 🛠️ 诊断工具

### 1. 系统监控工具

```bash
# 系统资源监控
htop
iotop
nethogs

# 网络监控
iftop
nethogs
ss -tuln

# 进程监控
ps aux --sort=-%cpu
ps aux --sort=-%mem

# 文件系统监控
df -h
du -sh /var/log/*
```

### 2. 应用监控工具

```go
// 1. 性能分析
func performanceProfiling() {
    // CPU性能分析
    f, err := os.Create("cpu.prof")
    if err != nil {
        log.Fatal(err)
    }
    defer f.Close()
    
    pprof.StartCPUProfile(f)
    defer pprof.StopCPUProfile()
    
    // 内存性能分析
    f2, err := os.Create("mem.prof")
    if err != nil {
        log.Fatal(err)
    }
    defer f2.Close()
    
    runtime.GC()
    pprof.WriteHeapProfile(f2)
}

// 2. 指标收集
func metricsCollection() {
    // 自定义指标
    var (
        requestCount = prometheus.NewCounterVec(
            prometheus.CounterOpts{
                Name: "http_requests_total",
                Help: "Total number of HTTP requests",
            },
            []string{"method", "endpoint", "status"},
        )
        
        requestDuration = prometheus.NewHistogramVec(
            prometheus.HistogramOpts{
                Name: "http_request_duration_seconds",
                Help: "HTTP request duration in seconds",
            },
            []string{"method", "endpoint"},
        )
    )
    
    prometheus.MustRegister(requestCount, requestDuration)
}

// 3. 日志分析
func logAnalysis() {
    // 结构化日志
    logger := logrus.New()
    logger.SetFormatter(&logrus.JSONFormatter{})
    
    // 日志级别
    logger.SetLevel(logrus.InfoLevel)
    
    // 日志字段
    logger.WithFields(logrus.Fields{
        "user_id": "12345",
        "action":  "create_order",
        "status":  "success",
    }).Info("Order created successfully")
}
```

### 3. 调试工具

```go
// 1. 调试模式
func debugMode() {
    if os.Getenv("DEBUG") == "true" {
        // 启用详细日志
        log.SetLevel(log.DebugLevel)
        
        // 启用性能分析
        go func() {
            log.Println("Starting debug server on :6060")
            log.Println(http.ListenAndServe("localhost:6060", nil))
        }()
    }
}

// 2. 健康检查端点
func healthCheckEndpoint() {
    http.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) {
        status := map[string]interface{}{
            "status":    "healthy",
            "timestamp": time.Now(),
            "version":   "1.0.0",
        }
        
        // 检查依赖服务
        if err := checkDatabase(); err != nil {
            status["database"] = "unhealthy"
            status["status"] = "unhealthy"
        } else {
            status["database"] = "healthy"
        }
        
        if err := checkRedis(); err != nil {
            status["redis"] = "unhealthy"
            status["status"] = "unhealthy"
        } else {
            status["redis"] = "healthy"
        }
        
        w.Header().Set("Content-Type", "application/json")
        json.NewEncoder(w).Encode(status)
    })
}

// 3. 错误追踪
func errorTracking() {
    func trackError(err error, context map[string]interface{}) {
        // 记录错误
        log.WithFields(logrus.Fields{
            "error":   err.Error(),
            "context": context,
            "stack":   string(debug.Stack()),
        }).Error("Error occurred")
        
        // 发送到错误追踪服务
        if errorTracker != nil {
            errorTracker.CaptureException(err, context)
        }
    }
}
```

## 🔧 自动化故障排除

### 1. 自动诊断脚本

```bash
#!/bin/bash
# diagnose.sh - 自动诊断脚本

echo "=== OTLP Go 系统诊断 ==="

# 检查服务状态
echo "1. 检查服务状态..."
systemctl is-active otlp-go-service
systemctl is-enabled otlp-go-service

# 检查端口
echo "2. 检查端口..."
netstat -tlnp | grep 8080
lsof -i :8080

# 检查进程
echo "3. 检查进程..."
ps aux | grep otlp-go

# 检查资源使用
echo "4. 检查资源使用..."
free -h
df -h
top -bn1 | head -20

# 检查网络连接
echo "5. 检查网络连接..."
ping -c 3 google.com
telnet localhost 8080

# 检查日志
echo "6. 检查日志..."
journalctl -u otlp-go-service --since "1 hour ago" | tail -20

# 检查配置文件
echo "7. 检查配置文件..."
otlp-go --config-check

echo "=== 诊断完成 ==="
```

### 2. 自动修复脚本

```bash
#!/bin/bash
# auto-fix.sh - 自动修复脚本

echo "=== OTLP Go 自动修复 ==="

# 重启服务
echo "1. 重启服务..."
systemctl restart otlp-go-service
sleep 10

# 检查服务状态
if systemctl is-active --quiet otlp-go-service; then
    echo "服务重启成功"
else
    echo "服务重启失败，尝试手动启动..."
    systemctl start otlp-go-service
fi

# 清理临时文件
echo "2. 清理临时文件..."
rm -rf /tmp/otlp-go-*
rm -rf /var/log/otlp-go/*.log.old

# 清理缓存
echo "3. 清理缓存..."
redis-cli FLUSHALL

# 重启依赖服务
echo "4. 重启依赖服务..."
docker-compose restart postgres redis

# 验证修复结果
echo "5. 验证修复结果..."
curl -f http://localhost:8080/health
if [ $? -eq 0 ]; then
    echo "修复成功"
else
    echo "修复失败，需要手动干预"
fi

echo "=== 自动修复完成 ==="
```

### 3. 监控告警

```yaml
# alert-rules.yml
groups:
  - name: otlp-go-alerts
    rules:
      - alert: ServiceDown
        expr: up == 0
        for: 1m
        labels:
          severity: critical
        annotations:
          summary: "OTLP Go service is down"
          description: "Service has been down for more than 1 minute"
          runbook_url: "https://wiki.example.com/runbooks/service-down"
      
      - alert: HighErrorRate
        expr: rate(http_requests_total{status=~"5.."}[5m]) / rate(http_requests_total[5m]) > 0.05
        for: 3m
        labels:
          severity: warning
        annotations:
          summary: "High error rate detected"
          description: "Error rate is above 5% for more than 3 minutes"
          runbook_url: "https://wiki.example.com/runbooks/high-error-rate"
      
      - alert: HighLatency
        expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 1
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High latency detected"
          description: "95th percentile latency is above 1 second for more than 5 minutes"
          runbook_url: "https://wiki.example.com/runbooks/high-latency"
```

## 📚 最佳实践

### 1. 预防措施

```go
// 1. 实现优雅关闭
func gracefulShutdown() {
    c := make(chan os.Signal, 1)
    signal.Notify(c, os.Interrupt, syscall.SIGTERM)
    
    <-c
    log.Println("Shutting down gracefully...")
    
    // 停止接受新请求
    server.SetKeepAlivesEnabled(false)
    
    // 等待现有请求完成
    ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
    defer cancel()
    
    if err := server.Shutdown(ctx); err != nil {
        log.Printf("Server shutdown error: %v", err)
    }
    
    // 清理资源
    cleanup()
    log.Println("Shutdown complete")
}

// 2. 实现熔断器
func circuitBreaker() {
    breaker := gobreaker.NewCircuitBreaker(gobreaker.Settings{
        Name:        "database",
        MaxRequests: 3,
        Interval:    60 * time.Second,
        Timeout:     30 * time.Second,
        ReadyToTrip: func(counts gobreaker.Counts) bool {
            return counts.ConsecutiveFailures >= 5
        },
        OnStateChange: func(name string, from gobreaker.State, to gobreaker.State) {
            log.Printf("Circuit breaker %s changed from %s to %s", name, from, to)
        },
    })
    
    result, err := breaker.Execute(func() (interface{}, error) {
        return database.Query("SELECT * FROM users")
    })
}

// 3. 实现限流
func rateLimiting() {
    limiter := rate.NewLimiter(rate.Limit(100), 200) // 100 req/s, burst 200
    
    func handleRequest(w http.ResponseWriter, r *http.Request) {
        if !limiter.Allow() {
            http.Error(w, "Rate limit exceeded", http.StatusTooManyRequests)
            return
        }
        
        // 处理请求
        processRequest(w, r)
    }
}
```

### 2. 监控策略

```go
// 1. 健康检查
func healthCheck() {
    http.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) {
        status := "healthy"
        checks := make(map[string]string)
        
        // 检查数据库
        if err := db.Ping(); err != nil {
            status = "unhealthy"
            checks["database"] = "unhealthy"
        } else {
            checks["database"] = "healthy"
        }
        
        // 检查Redis
        if err := redis.Ping().Err(); err != nil {
            status = "unhealthy"
            checks["redis"] = "unhealthy"
        } else {
            checks["redis"] = "healthy"
        }
        
        response := map[string]interface{}{
            "status": status,
            "checks": checks,
            "timestamp": time.Now(),
        }
        
        w.Header().Set("Content-Type", "application/json")
        if status == "unhealthy" {
            w.WriteHeader(http.StatusServiceUnavailable)
        }
        json.NewEncoder(w).Encode(response)
    })
}

// 2. 指标收集
func metricsCollection() {
    // 请求计数器
    requestCounter := prometheus.NewCounterVec(
        prometheus.CounterOpts{
            Name: "http_requests_total",
            Help: "Total number of HTTP requests",
        },
        []string{"method", "endpoint", "status"},
    )
    
    // 请求延迟
    requestDuration := prometheus.NewHistogramVec(
        prometheus.HistogramOpts{
            Name: "http_request_duration_seconds",
            Help: "HTTP request duration in seconds",
            Buckets: prometheus.DefBuckets,
        },
        []string{"method", "endpoint"},
    )
    
    prometheus.MustRegister(requestCounter, requestDuration)
}

// 3. 日志记录
func logging() {
    logger := logrus.New()
    logger.SetFormatter(&logrus.JSONFormatter{})
    logger.SetLevel(logrus.InfoLevel)
    
    // 请求日志中间件
    func loggingMiddleware(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            start := time.Now()
            
            // 包装ResponseWriter以捕获状态码
            ww := &responseWriter{ResponseWriter: w, statusCode: 200}
            
            next.ServeHTTP(ww, r)
            
            duration := time.Since(start)
            
            logger.WithFields(logrus.Fields{
                "method":     r.Method,
                "url":        r.URL.String(),
                "status":     ww.statusCode,
                "duration":   duration,
                "user_agent": r.UserAgent(),
                "remote_ip":  r.RemoteAddr,
            }).Info("HTTP request")
        })
    }
}
```

## 📝 总结

本故障排除指南提供了OTLP Go项目的完整故障排除方案，包括：

1. **故障分类**: 系统、网络、数据库、缓存、监控故障
2. **诊断方法**: 详细的诊断步骤和命令
3. **解决方案**: 具体的解决方案和代码示例
4. **诊断工具**: 系统监控、应用监控、调试工具
5. **自动化**: 自动诊断脚本、自动修复脚本、监控告警
6. **最佳实践**: 预防措施、监控策略、日志记录

该指南为OTLP Go项目提供了全面的故障排除能力，确保系统的高可用性和稳定性。

---

**文档版本**: v1.0.0  
**最后更新**: 2025年10月13日  
**维护者**: OTLP Go Team
