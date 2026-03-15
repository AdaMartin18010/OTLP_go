# Go 1.26 最佳实践指南

## 1. 循环语法

### 推荐 (Go 1.22+)
```go
// range over integers
for i := range n {
    fmt.Println(i)
}

// range over slices
for i, v := range slice {
    fmt.Println(i, v)
}
```

### 避免 (旧方式)
```go
// 不要使用旧的三段式循环
for i := 0; i < n; i++ {
    fmt.Println(i)
}
```

## 2. 随机数生成

### 推荐 (Go 1.22+)
```go
import "math/rand/v2"

// 使用新的 API
n := rand.IntN(100)        // 0-99
m := rand.Int64N(1000)     // 0-999
```

### 避免
```go
import "math/rand"

// 旧 API
n := rand.Intn(100)
```

## 3. 结构化日志

### 推荐 (Go 1.21+)
```go
import "log/slog"

// 使用结构化日志
slog.Info("request completed",
    "method", req.Method,
    "path", req.URL.Path,
    "duration", time.Since(start),
)
```

### 避免
```go
import "log"

// 不要使用格式化日志
log.Printf("request completed: method=%s path=%s duration=%v", 
    req.Method, req.URL.Path, time.Since(start))
```

## 4. Context 处理

### 推荐
```go
// 使用 context.WithTimeout
ctx, cancel := context.WithTimeout(parentCtx, 5*time.Second)
defer cancel()

// 传递 context
result, err := processRequest(ctx, req)
```

### 避免
```go
// 不要使用 context.Background() 除非必要
ctx := context.Background()

// 不要忘记调用 cancel
ctx, cancel := context.WithTimeout(parentCtx, 5*time.Second)
// defer cancel()  // 不要忘记！
```

## 5. 错误处理

### 推荐
```go
// 包装错误提供上下文
if err != nil {
    return fmt.Errorf("failed to process item %d: %w", itemID, err)
}

// 使用 errors.Is 检查特定错误
if errors.Is(err, context.DeadlineExceeded) {
    // 处理超时
}
```

### 避免
```go
// 不要丢失原始错误
if err != nil {
    return errors.New("failed to process")  // 丢失了原始错误信息
}

// 不要直接比较错误字符串
if err.Error() == "timeout" {  // 不稳定！
    // ...
}
```

## 6. 资源管理

### 推荐
```go
// 使用 defer 确保资源释放
f, err := os.Open(file)
if err != nil {
    return err
}
defer f.Close()

// 使用 context 控制资源生命周期
ctx, cancel := context.WithCancel(context.Background())
defer cancel()
```

### 避免
```go
// 不要忘记关闭资源
f, _ := os.Open(file)
// 处理...
// f.Close()  // 容易忘记！

// 不要在循环中使用 defer
for _, file := range files {
    f, _ := os.Open(file)
    defer f.Close()  // 会累积延迟调用！
}
```

## 7. OpenTelemetry 最佳实践

### 推荐
```go
// 创建带有属性的 span
ctx, span := tracer.Start(ctx, "operation",
    trace.WithAttributes(
        attribute.String("key", "value"),
        attribute.Int("count", 42),
    ),
)
defer span.End()

// 记录事件
span.AddEvent("checkpoint", trace.WithAttributes(
    attribute.String("status", "ok"),
))

// 记录错误
if err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, err.Error())
}
```

### 避免
```go
// 不要忘记结束 span
ctx, span := tracer.Start(ctx, "operation")
// span.End()  // 不要忘记！

// 不要设置过多属性
span.SetAttributes(
    attribute.String("key1", "value1"),
    // ... 数十个属性
)  // 会导致性能问题
```

## 8. 性能优化

### 推荐
```go
// 使用 sync.Pool 复用对象
pool := sync.Pool{
    New: func() interface{} {
        return make([]byte, 1024)
    },
}

buf := pool.Get().([]byte)
defer pool.Put(buf)

// 预分配切片容量
result := make([]int, 0, len(input))
```

### 避免
```go
// 不要频繁分配小对象
for i := 0; i < 1000000; i++ {
    buf := make([]byte, 1024)  // 每次循环都分配
    // 使用 buf...
}

// 不要重复追加而不预分配
var result []int
for i := range n {
    result = append(result, i)  // 多次重新分配
}
```