package patterns

import (
	"context"
	"fmt"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
)

// AdvancedPipeline 高级 Pipeline 模式实现
// CSP 模型: Stage1 -> Stage2 -> Stage3 -> ... -> StageN
// 每个 Stage 都是独立的 CSP Process

// PipelineStage 定义 Pipeline 阶段
type PipelineStage[In any, Out any] func(context.Context, In) (Out, error)

// AdvancedPipeline 多阶段处理流水线
type AdvancedPipeline struct {
	name          string
	tracer        trace.Tracer
	meter         metric.Meter
	latencyHist   metric.Float64Histogram
	throughputCtr metric.Int64Counter
	errorCtr      metric.Int64Counter
}

// NewAdvancedPipeline 创建新的高级 Pipeline
func NewAdvancedPipeline(name string) *AdvancedPipeline {
	tracer := otel.Tracer(fmt.Sprintf("pipeline/%s", name))
	meter := otel.Meter(fmt.Sprintf("pipeline/%s", name))

	latencyHist, _ := meter.Float64Histogram(
		"pipeline.stage.latency",
		metric.WithDescription("Stage processing latency in seconds"),
		metric.WithUnit("s"),
	)

	throughputCtr, _ := meter.Int64Counter(
		"pipeline.throughput",
		metric.WithDescription("Number of items processed"),
		metric.WithUnit("1"),
	)

	errorCtr, _ := meter.Int64Counter(
		"pipeline.errors",
		metric.WithDescription("Number of errors"),
		metric.WithUnit("1"),
	)

	return &AdvancedPipeline{
		name:          name,
		tracer:        tracer,
		meter:         meter,
		latencyHist:   latencyHist,
		throughputCtr: throughputCtr,
		errorCtr:      errorCtr,
	}
}

// ProcessItem 处理单个项目通过所有阶段
func (p *AdvancedPipeline) ProcessItem(ctx context.Context, stageName string, process func(context.Context) error) error {
	start := time.Now()

	ctx, span := p.tracer.Start(ctx, fmt.Sprintf("stage.%s", stageName),
		trace.WithAttributes(
			attribute.String("pipeline.name", p.name),
			attribute.String("stage.name", stageName),
		),
	)
	defer span.End()

	// 执行处理逻辑
	err := process(ctx)
	duration := time.Since(start).Seconds()

	// 记录指标
	attrs := metric.WithAttributes(
		attribute.String("pipeline", p.name),
		attribute.String("stage", stageName),
	)

	p.latencyHist.Record(ctx, duration, attrs)

	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		p.errorCtr.Add(ctx, 1, attrs)
		return err
	}

	p.throughputCtr.Add(ctx, 1, attrs)
	span.SetStatus(codes.Ok, "completed")

	return nil
}

// DataPipeline 通用数据处理 Pipeline
type DataPipeline[T any] struct {
	*AdvancedPipeline
	stages []DataStage[T]
}

// DataStage 数据处理阶段
type DataStage[T any] struct {
	Name    string
	Process func(context.Context, T) (T, error)
}

// NewDataPipeline 创建数据处理 Pipeline
func NewDataPipeline[T any](name string, stages []DataStage[T]) *DataPipeline[T] {
	return &DataPipeline[T]{
		AdvancedPipeline: NewAdvancedPipeline(name),
		stages:           stages,
	}
}

// Execute 执行完整的 Pipeline
func (dp *DataPipeline[T]) Execute(ctx context.Context, input T) (T, error) {
	ctx, span := dp.tracer.Start(ctx, "pipeline.execute",
		trace.WithAttributes(
			attribute.String("pipeline.name", dp.name),
			attribute.Int("stages.count", len(dp.stages)),
		),
	)
	defer span.End()

	current := input

	for i, stage := range dp.stages {
		stageCtx, stageSpan := dp.tracer.Start(ctx, stage.Name,
			trace.WithAttributes(
				attribute.Int("stage.index", i),
				attribute.String("stage.name", stage.Name),
			),
		)

		start := time.Now()

		// 执行阶段处理
		result, err := stage.Process(stageCtx, current)
		duration := time.Since(start).Seconds()

		// 记录指标
		attrs := metric.WithAttributes(
			attribute.String("pipeline", dp.name),
			attribute.String("stage", stage.Name),
		)
		dp.latencyHist.Record(stageCtx, duration, attrs)

		if err != nil {
			stageSpan.RecordError(err)
			stageSpan.SetStatus(codes.Error, err.Error())
			dp.errorCtr.Add(stageCtx, 1, attrs)
			stageSpan.End()

			span.RecordError(err)
			span.SetStatus(codes.Error, fmt.Sprintf("failed at stage %s", stage.Name))
			return current, fmt.Errorf("stage %s failed: %w", stage.Name, err)
		}

		stageSpan.SetStatus(codes.Ok, "completed")
		stageSpan.End()

		current = result
		dp.throughputCtr.Add(stageCtx, 1, attrs)
	}

	span.SetStatus(codes.Ok, "all stages completed")
	return current, nil
}

// Example: 图像处理 Pipeline
type ImageData struct {
	ID       string
	Data     []byte
	Width    int
	Height   int
	Metadata map[string]string
}

func ExampleImageProcessingPipeline() {
	ctx := context.Background()

	// 定义处理阶段
	stages := []DataStage[*ImageData]{
		{
			Name: "validate",
			Process: func(ctx context.Context, img *ImageData) (*ImageData, error) {
				if len(img.Data) == 0 {
					return nil, fmt.Errorf("empty image data")
				}
				return img, nil
			},
		},
		{
			Name: "resize",
			Process: func(ctx context.Context, img *ImageData) (*ImageData, error) {
				// 模拟缩放
				time.Sleep(10 * time.Millisecond)
				img.Width = 800
				img.Height = 600
				return img, nil
			},
		},
		{
			Name: "compress",
			Process: func(ctx context.Context, img *ImageData) (*ImageData, error) {
				// 模拟压缩
				time.Sleep(20 * time.Millisecond)
				img.Data = img.Data[:len(img.Data)/2] // 模拟压缩
				return img, nil
			},
		},
		{
			Name: "watermark",
			Process: func(ctx context.Context, img *ImageData) (*ImageData, error) {
				// 模拟添加水印
				time.Sleep(5 * time.Millisecond)
				img.Metadata["watermark"] = "applied"
				return img, nil
			},
		},
	}

	// 创建 Pipeline
	pipeline := NewDataPipeline("image-processing", stages)

	// 处理图像
	input := &ImageData{
		ID:       "img-001",
		Data:     make([]byte, 1024*1024), // 1MB
		Width:    1920,
		Height:   1080,
		Metadata: make(map[string]string),
	}

	result, err := pipeline.Execute(ctx, input)
	if err != nil {
		fmt.Printf("Pipeline failed: %v\n", err)
		return
	}

	fmt.Printf("Processed image %s: %dx%d, size=%d bytes\n",
		result.ID, result.Width, result.Height, len(result.Data))
}

// StreamPipeline 流式处理 Pipeline（无限流）
type StreamPipeline[T any] struct {
	*AdvancedPipeline
	input      <-chan T
	output     chan T
	stages     []func(context.Context, T) (T, error)
	bufferSize int
}

// NewStreamPipeline 创建流式 Pipeline
func NewStreamPipeline[T any](name string, bufferSize int) *StreamPipeline[T] {
	return &StreamPipeline[T]{
		AdvancedPipeline: NewAdvancedPipeline(name),
		bufferSize:       bufferSize,
		stages:           make([]func(context.Context, T) (T, error), 0),
	}
}

// AddStage 添加处理阶段
func (sp *StreamPipeline[T]) AddStage(name string, process func(context.Context, T) (T, error)) *StreamPipeline[T] {
	sp.stages = append(sp.stages, process)
	return sp
}

// Start 启动流式处理
func (sp *StreamPipeline[T]) Start(ctx context.Context, input <-chan T) <-chan T {
	sp.input = input
	sp.output = make(chan T, sp.bufferSize)

	go sp.process(ctx)

	return sp.output
}

// process 处理流式数据
func (sp *StreamPipeline[T]) process(ctx context.Context) {
	defer close(sp.output)

	for item := range sp.input {
		ctx, span := sp.tracer.Start(ctx, "stream.item",
			trace.WithAttributes(
				attribute.String("pipeline.name", sp.name),
			),
		)

		current := item
		failed := false

		// 通过所有阶段
		for i, stage := range sp.stages {
			result, err := stage(ctx, current)
			if err != nil {
				span.RecordError(err)
				span.SetStatus(codes.Error, fmt.Sprintf("stage %d failed", i))
				failed = true
				break
			}
			current = result
		}

		if !failed {
			span.SetStatus(codes.Ok, "completed")
			select {
			case sp.output <- current:
			case <-ctx.Done():
				span.End()
				return
			}
		}

		span.End()
	}
}

// Example: 日志处理流 Pipeline
type LogEntry struct {
	Timestamp time.Time
	Level     string
	Message   string
	Fields    map[string]interface{}
}

func ExampleLogStreamPipeline() {
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	// 创建流式 Pipeline
	pipeline := NewStreamPipeline[*LogEntry]("log-processing", 100)

	// 添加处理阶段
	pipeline.
		AddStage("parse", func(ctx context.Context, log *LogEntry) (*LogEntry, error) {
			// 解析日志
			return log, nil
		}).
		AddStage("enrich", func(ctx context.Context, log *LogEntry) (*LogEntry, error) {
			// 丰富日志（添加元数据）
			log.Fields["enriched"] = true
			return log, nil
		}).
		AddStage("filter", func(ctx context.Context, log *LogEntry) (*LogEntry, error) {
			// 过滤（只保留 ERROR 及以上）
			if log.Level == "DEBUG" || log.Level == "INFO" {
				return nil, fmt.Errorf("filtered out")
			}
			return log, nil
		})

	// 创建输入通道
	input := make(chan *LogEntry, 100)

	// 启动处理
	output := pipeline.Start(ctx, input)

	// 发送日志
	go func() {
		defer close(input)
		levels := []string{"DEBUG", "INFO", "WARN", "ERROR"}
		for i := 0; i < 1000; i++ {
			input <- &LogEntry{
				Timestamp: time.Now(),
				Level:     levels[i%len(levels)],
				Message:   fmt.Sprintf("log message %d", i),
				Fields:    make(map[string]interface{}),
			}
		}
	}()

	// 消费输出
	count := 0
	for log := range output {
		count++
		fmt.Printf("Processed log: %s - %s\n", log.Level, log.Message)
	}

	fmt.Printf("Total processed: %d logs\n", count)
}
