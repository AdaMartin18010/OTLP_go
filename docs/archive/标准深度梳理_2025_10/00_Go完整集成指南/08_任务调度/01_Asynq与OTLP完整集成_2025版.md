# Asynq 与 OTLP 完整集成（2025版）

> **Asynq 版本**: v0.24.1+  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [1. Asynq 概述](#1-asynq-概述)
- [2. 快速开始](#2-快速开始)
- [3. 完整集成示例](#3-完整集成示例)
- [4. 高级特性](#4-高级特性)
- [5. 生产部署](#5-生产部署)
- [6. 最佳实践](#6-最佳实践)

---

## 1. Asynq 概述

**Asynq** 是一个基于 Redis 的 Go 异步任务队列库，提供可靠的任务调度和执行。

```text
🚀 核心特性:
  ✅ 可靠性 - Redis 持久化，任务不丢失
  ✅ 延迟任务 - 支持定时执行
  ✅ 周期任务 - Cron 表达式调度
  ✅ 重试机制 - 指数退避重试
  ✅ 优先级队列 - 多优先级支持
  ✅ 任务去重 - 避免重复执行
  ✅ Web UI - 任务监控界面
  ✅ 分布式 - 多worker并行处理

📊 适用场景:
  - 异步邮件发送
  - 图片/视频处理
  - 报表生成
  - 数据导入导出
  - 定时任务调度
  - 事件驱动处理
```

### 1.1 Asynq vs Machinery vs River

```text
┌──────────────┬─────────┬───────────┬─────────┐
│   特性       │  Asynq  │ Machinery │  River  │
├──────────────┼─────────┼───────────┼─────────┤
│ 后端         │  Redis  │ Multi     │ Postgres│
│ 性能         │  ⭐⭐⭐⭐  │  ⭐⭐⭐     │  ⭐⭐⭐⭐  │
│ 易用性       │  ⭐⭐⭐⭐⭐│  ⭐⭐⭐     │  ⭐⭐⭐⭐  │
│ Web UI       │   ✅    │   ❌      │   ❌    │
│ 定时任务     │   ✅    │   ✅      │   ✅    │
│ 优先级       │   ✅    │   ✅      │   ✅    │
│ 任务去重     │   ✅    │   ❌      │   ✅    │
│ 社区活跃度   │  高     │   中      │   新    │
└──────────────┴─────────┴───────────┴─────────┘

✅ 选择 Asynq:
  - 需要 Redis 作为任务队列
  - 需要 Web 监控界面
  - 简单易用的 API
  - 活跃的社区支持

✅ 选择 Machinery:
  - 需要多种后端（Redis/AMQP/Memcache）
  - 复杂的任务工作流
  - 任务链和分组

✅ 选择 River:
  - 使用 PostgreSQL
  - 需要事务性保证
  - 利用 Postgres 生态
```

---

## 2. 快速开始

### 2.1 依赖安装

```bash
# 安装 Asynq
go get -u github.com/hibiken/asynq@v0.24.1

# 安装 Redis (如果未安装)
docker run -d --name redis -p 6379:6379 redis:latest

# 安装 Asynqmon (Web UI)
go install github.com/hibiken/asynqmon@latest

# 启动 Asynqmon
asynqmon --redis-addr=localhost:6379

# 访问 http://localhost:8080
```

### 2.2 基础集成

```go
package main

import (
    "context"
    "encoding/json"
    "fmt"
    "log"
    "time"

    "github.com/hibiken/asynq"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
    "go.opentelemetry.io/otel/trace"
)

// 任务类型常量
const (
    TypeEmailDelivery = "email:deliver"
    TypeImageResize   = "image:resize"
)

// EmailTask 邮件任务
type EmailTask struct {
    To      string `json:"to"`
    Subject string `json:"subject"`
    Body    string `json:"body"`
}

// 初始化 Tracer
func initTracer() (*sdktrace.TracerProvider, error) {
    ctx := context.Background()

    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("asynq-demo"),
            semconv.ServiceVersion("1.0.0"),
        ),
    )
    if err != nil {
        return nil, err
    }

    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )

    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))

    return tp, nil
}

// NewEmailTask 创建邮件任务
func NewEmailTask(to, subject, body string) (*asynq.Task, error) {
    payload, err := json.Marshal(EmailTask{
        To:      to,
        Subject: subject,
        Body:    body,
    })
    if err != nil {
        return nil, err
    }

    return asynq.NewTask(TypeEmailDelivery, payload), nil
}

// HandleEmailTask 处理邮件任务
func HandleEmailTask(ctx context.Context, t *asynq.Task) error {
    tracer := otel.Tracer("email-handler")
    ctx, span := tracer.Start(ctx, "HandleEmailTask",
        trace.WithSpanKind(trace.SpanKindConsumer),
        trace.WithAttributes(
            attribute.String("task.type", t.Type()),
        ),
    )
    defer span.End()

    // 解析 payload
    var p EmailTask
    if err := json.Unmarshal(t.Payload(), &p); err != nil {
        span.RecordError(err)
        return fmt.Errorf("json.Unmarshal failed: %v", err)
    }

    span.SetAttributes(
        attribute.String("email.to", p.To),
        attribute.String("email.subject", p.Subject),
    )

    // 模拟发送邮件
    log.Printf("Sending Email to %s: %s", p.To, p.Subject)
    time.Sleep(2 * time.Second)

    return nil
}

func main() {
    // 初始化追踪
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())

    // Redis 配置
    redisOpt := asynq.RedisClientOpt{
        Addr: "localhost:6379",
    }

    // 启动 Client (生产者)
    go func() {
        client := asynq.NewClient(redisOpt)
        defer client.Close()

        // 创建任务
        task, err := NewEmailTask(
            "user@example.com",
            "Welcome",
            "Welcome to our service!",
        )
        if err != nil {
            log.Fatal(err)
        }

        // 入队任务
        info, err := client.Enqueue(task)
        if err != nil {
            log.Fatal(err)
        }

        log.Printf("Task enqueued: id=%s queue=%s", info.ID, info.Queue)
    }()

    // 启动 Server (消费者)
    srv := asynq.NewServer(
        redisOpt,
        asynq.Config{
            Concurrency: 10,
            Queues: map[string]int{
                "critical": 6,
                "default":  3,
                "low":      1,
            },
        },
    )

    // 注册处理器
    mux := asynq.NewServeMux()
    mux.HandleFunc(TypeEmailDelivery, HandleEmailTask)

    // 启动服务器
    if err := srv.Run(mux); err != nil {
        log.Fatalf("could not run server: %v", err)
    }
}
```

---

## 3. 完整集成示例

### 3.1 带追踪的任务处理器

```go
package handlers

import (
    "context"
    "encoding/json"
    "fmt"
    "time"

    "github.com/hibiken/asynq"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// TaskPayload 任务载荷基础结构
type TaskPayload struct {
    TraceParent string                 `json:"traceparent,omitempty"`
    Data        map[string]interface{} `json:"data"`
}

// TracedTaskHandler 带追踪的任务处理器
type TracedTaskHandler struct {
    handler func(context.Context, map[string]interface{}) error
    tracer  trace.Tracer
}

func NewTracedTaskHandler(name string, handler func(context.Context, map[string]interface{}) error) *TracedTaskHandler {
    return &TracedTaskHandler{
        handler: handler,
        tracer:  otel.Tracer(name),
    }
}

// ProcessTask 处理任务
func (h *TracedTaskHandler) ProcessTask(ctx context.Context, t *asynq.Task) error {
    // 解析 payload
    var payload TaskPayload
    if err := json.Unmarshal(t.Payload(), &payload); err != nil {
        return fmt.Errorf("failed to unmarshal payload: %w", err)
    }

    // 提取追踪上下文
    if payload.TraceParent != "" {
        carrier := propagation.MapCarrier{
            "traceparent": payload.TraceParent,
        }
        ctx = otel.GetTextMapPropagator().Extract(ctx, carrier)
    }

    // 创建 span
    ctx, span := h.tracer.Start(ctx, "ProcessTask",
        trace.WithSpanKind(trace.SpanKindConsumer),
        trace.WithAttributes(
            attribute.String("task.type", t.Type()),
            attribute.String("task.id", t.ResultWriter().TaskID()),
            attribute.Int("task.retry", t.ResultWriter().TaskInfo().Retried),
        ),
    )
    defer span.End()

    // 执行处理逻辑
    if err := h.handler(ctx, payload.Data); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetStatus(codes.Ok, "Task completed successfully")
    return nil
}

// TaskEnqueuer 任务入队器
type TaskEnqueuer struct {
    client *asynq.Client
    tracer trace.Tracer
}

func NewTaskEnqueuer(client *asynq.Client) *TaskEnqueuer {
    return &TaskEnqueuer{
        client: client,
        tracer: otel.Tracer("task-enqueuer"),
    }
}

// EnqueueTask 入队任务（带追踪）
func (e *TaskEnqueuer) EnqueueTask(ctx context.Context, taskType string, data map[string]interface{}, opts ...asynq.Option) (*asynq.TaskInfo, error) {
    ctx, span := e.tracer.Start(ctx, "EnqueueTask",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("task.type", taskType),
        ),
    )
    defer span.End()

    // 注入追踪上下文
    carrier := propagation.MapCarrier{}
    otel.GetTextMapPropagator().Inject(ctx, carrier)

    payload := TaskPayload{
        TraceParent: carrier["traceparent"],
        Data:        data,
    }

    payloadBytes, err := json.Marshal(payload)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    task := asynq.NewTask(taskType, payloadBytes)
    info, err := e.client.Enqueue(task, opts...)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    span.SetAttributes(
        attribute.String("task.id", info.ID),
        attribute.String("task.queue", info.Queue),
    )
    span.SetStatus(codes.Ok, "Task enqueued successfully")

    return info, nil
}
```

### 3.2 实战：图片处理任务系统

```go
package imageprocessing

import (
    "context"
    "fmt"
    "image"
    "log"
    "os"
    "time"

    "github.com/disintegration/imaging"
    "github.com/hibiken/asynq"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 任务类型
const (
    TypeImageResize    = "image:resize"
    TypeImageWatermark = "image:watermark"
    TypeImageCompress  = "image:compress"
)

// ImageProcessingService 图片处理服务
type ImageProcessingService struct {
    client   *TaskEnqueuer
    storage  ImageStorage
    tracer   trace.Tracer
}

// ImageStorage 图片存储接口
type ImageStorage interface {
    Get(ctx context.Context, path string) (image.Image, error)
    Put(ctx context.Context, path string, img image.Image) error
}

func NewImageProcessingService(client *TaskEnqueuer, storage ImageStorage) *ImageProcessingService {
    return &ImageProcessingService{
        client:  client,
        storage: storage,
        tracer:  otel.Tracer("image-processing"),
    }
}

// ResizeImage 调整图片大小
func (s *ImageProcessingService) ResizeImage(ctx context.Context, sourcePath, destPath string, width, height int) error {
    ctx, span := s.tracer.Start(ctx, "ResizeImage",
        trace.WithAttributes(
            attribute.String("source.path", sourcePath),
            attribute.String("dest.path", destPath),
            attribute.Int("width", width),
            attribute.Int("height", height),
        ),
    )
    defer span.End()

    // 入队任务
    _, err := s.client.EnqueueTask(ctx, TypeImageResize, map[string]interface{}{
        "source_path": sourcePath,
        "dest_path":   destPath,
        "width":       width,
        "height":      height,
    })

    if err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}

// HandleImageResize 处理图片调整任务
func (s *ImageProcessingService) HandleImageResize(ctx context.Context, data map[string]interface{}) error {
    ctx, span := s.tracer.Start(ctx, "HandleImageResize")
    defer span.End()

    // 提取参数
    sourcePath := data["source_path"].(string)
    destPath := data["dest_path"].(string)
    width := int(data["width"].(float64))
    height := int(data["height"].(float64))

    span.SetAttributes(
        attribute.String("source.path", sourcePath),
        attribute.String("dest.path", destPath),
    )

    // 加载图片
    img, err := s.storage.Get(ctx, sourcePath)
    if err != nil {
        span.RecordError(err)
        return fmt.Errorf("failed to load image: %w", err)
    }

    // 调整大小
    resized := imaging.Resize(img, width, height, imaging.Lanczos)

    // 保存图片
    if err := s.storage.Put(ctx, destPath, resized); err != nil {
        span.RecordError(err)
        return fmt.Errorf("failed to save image: %w", err)
    }

    log.Printf("Resized image: %s -> %s (%dx%d)", sourcePath, destPath, width, height)
    return nil
}

// BatchProcessImages 批量处理图片
func (s *ImageProcessingService) BatchProcessImages(ctx context.Context, images []string, operations []string) error {
    ctx, span := s.tracer.Start(ctx, "BatchProcessImages",
        trace.WithAttributes(
            attribute.Int("image.count", len(images)),
            attribute.StringSlice("operations", operations),
        ),
    )
    defer span.End()

    // 创建任务链
    for _, imgPath := range images {
        for _, op := range operations {
            switch op {
            case "resize":
                s.ResizeImage(ctx, imgPath, imgPath+".resized.jpg", 800, 600)
            case "watermark":
                // ... 水印处理
            case "compress":
                // ... 压缩处理
            }
        }
    }

    return nil
}

// LocalStorage 本地文件存储实现
type LocalStorage struct {
    basePath string
}

func NewLocalStorage(basePath string) *LocalStorage {
    return &LocalStorage{basePath: basePath}
}

func (s *LocalStorage) Get(ctx context.Context, path string) (image.Image, error) {
    file, err := os.Open(s.basePath + "/" + path)
    if err != nil {
        return nil, err
    }
    defer file.Close()

    img, _, err := image.Decode(file)
    return img, err
}

func (s *LocalStorage) Put(ctx context.Context, path string, img image.Image) error {
    file, err := os.Create(s.basePath + "/" + path)
    if err != nil {
        return err
    }
    defer file.Close()

    return imaging.Encode(file, img, imaging.JPEG)
}
```

### 3.3 周期任务调度

```go
package scheduler

import (
    "context"
    "log"

    "github.com/hibiken/asynq"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// ScheduledTaskManager 定时任务管理器
type ScheduledTaskManager struct {
    scheduler *asynq.Scheduler
    tracer    trace.Tracer
}

func NewScheduledTaskManager(redisOpt asynq.RedisClientOpt) *ScheduledTaskManager {
    scheduler := asynq.NewScheduler(redisOpt, &asynq.SchedulerOpts{
        Location: time.UTC,
    })

    return &ScheduledTaskManager{
        scheduler: scheduler,
        tracer:    otel.Tracer("task-scheduler"),
    }
}

// RegisterCronTask 注册 Cron 任务
func (m *ScheduledTaskManager) RegisterCronTask(cronspec, taskType string, payload map[string]interface{}) error {
    ctx, span := m.tracer.Start(context.Background(), "RegisterCronTask",
        trace.WithAttributes(
            attribute.String("cron.spec", cronspec),
            attribute.String("task.type", taskType),
        ),
    )
    defer span.End()

    payloadBytes, err := json.Marshal(payload)
    if err != nil {
        span.RecordError(err)
        return err
    }

    task := asynq.NewTask(taskType, payloadBytes)
    
    entryID, err := m.scheduler.Register(cronspec, task)
    if err != nil {
        span.RecordError(err)
        return err
    }

    span.SetAttributes(attribute.String("entry.id", entryID))
    log.Printf("Registered cron task: %s, entry_id: %s", taskType, entryID)

    return nil
}

// Start 启动调度器
func (m *ScheduledTaskManager) Start() error {
    return m.scheduler.Run()
}

// Stop 停止调度器
func (m *ScheduledTaskManager) Stop() {
    m.scheduler.Shutdown()
}

// 使用示例
func ExampleScheduler() {
    redisOpt := asynq.RedisClientOpt{
        Addr: "localhost:6379",
    }

    scheduler := NewScheduledTaskManager(redisOpt)

    // 每天凌晨2点执行数据备份
    scheduler.RegisterCronTask("0 2 * * *", "backup:database", map[string]interface{}{
        "database": "main",
    })

    // 每小时执行数据清理
    scheduler.RegisterCronTask("0 * * * *", "cleanup:old_data", map[string]interface{}{
        "retention_days": 30,
    })

    // 每5分钟执行健康检查
    scheduler.RegisterCronTask("*/5 * * * *", "health:check", nil)

    // 启动调度器
    if err := scheduler.Start(); err != nil {
        log.Fatal(err)
    }
}
```

---

## 4. 高级特性

### 4.1 任务去重

```go
package dedup

import (
    "fmt"
    "time"

    "github.com/hibiken/asynq"
)

// EnqueueWithDeduplication 入队任务（带去重）
func EnqueueWithDeduplication(
    client *asynq.Client,
    task *asynq.Task,
    uniqueKey string,
    ttl time.Duration,
) (*asynq.TaskInfo, error) {
    // 设置唯一性选项
    opts := []asynq.Option{
        asynq.Unique(ttl),
        asynq.TaskID(uniqueKey),
    }

    info, err := client.Enqueue(task, opts...)
    if err != nil {
        return nil, err
    }

    return info, nil
}

// 使用示例
func ExampleDeduplication(client *asynq.Client) {
    // 创建任务
    task, _ := NewEmailTask("user@example.com", "Hello", "Content")

    // 使用用户ID作为唯一键
    uniqueKey := fmt.Sprintf("email:user:123")

    // 24小时内相同的任务只会执行一次
    info, err := EnqueueWithDeduplication(
        client,
        task,
        uniqueKey,
        24*time.Hour,
    )

    if err != nil {
        log.Printf("Task already exists or error: %v", err)
    } else {
        log.Printf("Task enqueued: %s", info.ID)
    }
}
```

### 4.2 任务分组与依赖

```go
package taskgroup

import (
    "context"
    "encoding/json"
    "time"

    "github.com/hibiken/asynq"
)

// TaskGroup 任务组
type TaskGroup struct {
    client *asynq.Client
    tasks  []*asynq.Task
}

func NewTaskGroup(client *asynq.Client) *TaskGroup {
    return &TaskGroup{
        client: client,
        tasks:  make([]*asynq.Task, 0),
    }
}

// AddTask 添加任务到组
func (g *TaskGroup) AddTask(task *asynq.Task) {
    g.tasks = append(g.tasks, task)
}

// EnqueueAll 入队所有任务
func (g *TaskGroup) EnqueueAll(ctx context.Context, opts ...asynq.Option) error {
    for _, task := range g.tasks {
        if _, err := g.client.Enqueue(task, opts...); err != nil {
            return err
        }
    }
    return nil
}

// TaskChain 任务链（顺序执行）
type TaskChain struct {
    client *asynq.Client
    tasks  []*asynq.Task
}

func NewTaskChain(client *asynq.Client) *TaskChain {
    return &TaskChain{
        client: client,
        tasks:  make([]*asynq.Task, 0),
    }
}

// AddTask 添加任务到链
func (c *TaskChain) AddTask(task *asynq.Task) {
    c.tasks = append(c.tasks, task)
}

// EnqueueChain 入队任务链
func (c *TaskChain) EnqueueChain(ctx context.Context) error {
    delay := time.Duration(0)
    
    for i, task := range c.tasks {
        opts := []asynq.Option{
            asynq.ProcessIn(delay),
        }
        
        if _, err := c.client.Enqueue(task, opts...); err != nil {
            return err
        }
        
        // 每个任务延迟5秒执行（确保顺序）
        delay += 5 * time.Second
    }
    
    return nil
}
```

### 4.3 任务监控与指标

```go
package monitoring

import (
    "context"
    "time"

    "github.com/hibiken/asynq"
    "go.opentelemetry.io/otel/metric"
)

// TaskMetrics 任务指标
type TaskMetrics struct {
    tasksEnqueued    metric.Int64Counter
    tasksProcessed   metric.Int64Counter
    tasksFailed      metric.Int64Counter
    tasksRetried     metric.Int64Counter
    processingTime   metric.Float64Histogram
}

func NewTaskMetrics(meter metric.Meter) (*TaskMetrics, error) {
    tasksEnqueued, err := meter.Int64Counter(
        "asynq.tasks.enqueued",
        metric.WithDescription("Number of tasks enqueued"),
    )
    if err != nil {
        return nil, err
    }

    tasksProcessed, err := meter.Int64Counter(
        "asynq.tasks.processed",
        metric.WithDescription("Number of tasks processed"),
    )
    if err != nil {
        return nil, err
    }

    tasksFailed, err := meter.Int64Counter(
        "asynq.tasks.failed",
        metric.WithDescription("Number of tasks failed"),
    )
    if err != nil {
        return nil, err
    }

    tasksRetried, err := meter.Int64Counter(
        "asynq.tasks.retried",
        metric.WithDescription("Number of tasks retried"),
    )
    if err != nil {
        return nil, err
    }

    processingTime, err := meter.Float64Histogram(
        "asynq.task.processing_time",
        metric.WithDescription("Task processing time in seconds"),
        metric.WithUnit("s"),
    )
    if err != nil {
        return nil, err
    }

    return &TaskMetrics{
        tasksEnqueued:  tasksEnqueued,
        tasksProcessed: tasksProcessed,
        tasksFailed:    tasksFailed,
        tasksRetried:   tasksRetried,
        processingTime: processingTime,
    }, nil
}

// RecordEnqueued 记录入队
func (m *TaskMetrics) RecordEnqueued(ctx context.Context, taskType string) {
    m.tasksEnqueued.Add(ctx, 1,
        metric.WithAttributes(
            attribute.String("task.type", taskType),
        ),
    )
}

// RecordProcessed 记录处理成功
func (m *TaskMetrics) RecordProcessed(ctx context.Context, taskType string, duration time.Duration) {
    m.tasksProcessed.Add(ctx, 1,
        metric.WithAttributes(
            attribute.String("task.type", taskType),
        ),
    )
    
    m.processingTime.Record(ctx, duration.Seconds(),
        metric.WithAttributes(
            attribute.String("task.type", taskType),
        ),
    )
}

// RecordFailed 记录失败
func (m *TaskMetrics) RecordFailed(ctx context.Context, taskType string, err error) {
    m.tasksFailed.Add(ctx, 1,
        metric.WithAttributes(
            attribute.String("task.type", taskType),
            attribute.String("error", err.Error()),
        ),
    )
}
```

---

## 5. 生产部署

### 5.1 Docker Compose 部署

```yaml
version: '3.8'

services:
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis-data:/data
    command: redis-server --appendonly yes
    restart: unless-stopped

  asynq-worker:
    build: .
    command: ./worker
    depends_on:
      - redis
    environment:
      - REDIS_ADDR=redis:6379
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
    restart: unless-stopped
    deploy:
      replicas: 3

  asynqmon:
    image: hibiken/asynqmon:latest
    ports:
      - "8080:8080"
    command:
      - --redis-addr=redis:6379
    depends_on:
      - redis
    restart: unless-stopped

volumes:
  redis-data:
```

### 5.2 Kubernetes 部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: asynq-worker
spec:
  replicas: 3
  selector:
    matchLabels:
      app: asynq-worker
  template:
    metadata:
      labels:
        app: asynq-worker
    spec:
      containers:
      - name: worker
        image: asynq-worker:latest
        env:
        - name: REDIS_ADDR
          value: "redis:6379"
        - name: CONCURRENCY
          value: "10"
        resources:
          requests:
            cpu: "100m"
            memory: "128Mi"
          limits:
            cpu: "500m"
            memory: "512Mi"
```

---

## 6. 最佳实践

### 6.1 性能优化

```text
✅ Worker 配置:
  - Concurrency: 10-50 (根据任务类型)
  - ShutdownTimeout: 30s
  - HealthCheckInterval: 15s

✅ Redis 配置:
  - 使用 Redis Cluster (生产环境)
  - 启用 AOF 持久化
  - 设置合理的 maxmemory

✅ 任务设计:
  - 保持任务幂等性
  - 任务粒度不要太大
  - 使用任务去重
  - 合理设置重试次数
```

### 6.2 监控告警

```text
✅ 关键指标:
  - 任务入队速率
  - 任务处理速率
  - 任务失败率
  - 队列积压数量
  - Worker 数量

✅ 告警规则:
  - 队列积压 > 10000
  - 任务失败率 > 5%
  - Worker 全部故障
  - Redis 连接失败
```

---

**参考资源**：

- [Asynq 官方文档](https://github.com/hibiken/asynq)
- [Asynqmon Web UI](https://github.com/hibiken/asynqmon)
- [Redis 文档](https://redis.io/documentation)
- [OpenTelemetry Go](https://opentelemetry.io/docs/instrumentation/go/)

