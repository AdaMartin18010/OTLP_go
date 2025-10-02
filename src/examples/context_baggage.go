package examples

import (
	"context"
	"fmt"
	"net/http"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/baggage"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/trace"
)

// BaggageExample Baggage 使用示例
// Baggage 用于在分布式系统中传递业务上下文

// SetBaggage 设置 Baggage
func SetBaggage(ctx context.Context, key, value string) (context.Context, error) {
	member, err := baggage.NewMember(key, value)
	if err != nil {
		return ctx, fmt.Errorf("failed to create baggage member: %w", err)
	}

	bag, err := baggage.New(member)
	if err != nil {
		return ctx, fmt.Errorf("failed to create baggage: %w", err)
	}

	return baggage.ContextWithBaggage(ctx, bag), nil
}

// GetBaggage 获取 Baggage
func GetBaggage(ctx context.Context, key string) string {
	bag := baggage.FromContext(ctx)
	member := bag.Member(key)
	return member.Value()
}

// AddBaggage 添加 Baggage 到现有 bag
func AddBaggage(ctx context.Context, key, value string) (context.Context, error) {
	// 获取现有的 baggage
	existingBag := baggage.FromContext(ctx)

	// 创建新成员
	member, err := baggage.NewMember(key, value)
	if err != nil {
		return ctx, err
	}

	// 合并
	newBag, err := existingBag.SetMember(member)
	if err != nil {
		return ctx, err
	}

	return baggage.ContextWithBaggage(ctx, newBag), nil
}

// BaggageHTTPExample HTTP 中使用 Baggage 示例
func BaggageHTTPExample() {
	tracer := otel.Tracer("baggage-example")
	propagator := otel.GetTextMapPropagator()

	// 服务 A：设置 Baggage
	http.HandleFunc("/service-a", func(w http.ResponseWriter, r *http.Request) {
		ctx := r.Context()
		ctx, span := tracer.Start(ctx, "service-a")
		defer span.End()

		// 设置 Baggage
		ctx, _ = SetBaggage(ctx, "user.id", "user-123")
		ctx, _ = AddBaggage(ctx, "request.id", "req-456")
		ctx, _ = AddBaggage(ctx, "tenant.id", "tenant-789")

		span.AddEvent("baggage.set", trace.WithAttributes(
			attribute.String("user.id", "user-123"),
			attribute.String("request.id", "req-456"),
		))

		// 调用服务 B
		req, _ := http.NewRequestWithContext(ctx, "GET", "http://service-b:8080/process", nil)

		// 注入 Trace Context 和 Baggage
		propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))

		client := &http.Client{}
		resp, err := client.Do(req)
		if err != nil {
			http.Error(w, "Failed to call service B", http.StatusInternalServerError)
			return
		}
		defer resp.Body.Close()

		w.Write([]byte("Service A completed"))
	})

	// 服务 B：读取 Baggage
	http.HandleFunc("/service-b", func(w http.ResponseWriter, r *http.Request) {
		// 提取 Trace Context 和 Baggage
		ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))
		ctx, span := tracer.Start(ctx, "service-b")
		defer span.End()

		// 读取 Baggage
		userID := GetBaggage(ctx, "user.id")
		requestID := GetBaggage(ctx, "request.id")
		tenantID := GetBaggage(ctx, "tenant.id")

		span.SetAttributes(
			attribute.String("baggage.user_id", userID),
			attribute.String("baggage.request_id", requestID),
			attribute.String("baggage.tenant_id", tenantID),
		)

		span.AddEvent("baggage.read", trace.WithAttributes(
			attribute.String("user.id", userID),
			attribute.String("request.id", requestID),
			attribute.String("tenant.id", tenantID),
		))

		// 使用 Baggage 进行业务逻辑
		processRequest(ctx, userID, tenantID)

		w.Write([]byte("Service B completed"))
	})
}

// processRequest 处理请求（使用 Baggage 中的信息）
func processRequest(ctx context.Context, userID, tenantID string) {
	tracer := otel.Tracer("baggage-example")
	_, span := tracer.Start(ctx, "process_request")
	defer span.End()

	// 使用 userID 和 tenantID 进行多租户隔离
	span.SetAttributes(
		attribute.String("user.id", userID),
		attribute.String("tenant.id", tenantID),
	)

	// 实际业务逻辑
	fmt.Printf("Processing request for user %s in tenant %s\n", userID, tenantID)
}

// ContextPropagationExample Context 传播示例
func ContextPropagationExample() {
	tracer := otel.Tracer("context-propagation")

	// 1. 创建根 Span
	ctx := context.Background()
	ctx, rootSpan := tracer.Start(ctx, "root-operation")
	defer rootSpan.End()

	rootSpan.SetAttributes(
		attribute.String("operation.type", "batch-processing"),
		attribute.Int("batch.size", 100),
	)

	// 2. 传递 Context 到子操作
	processItems(ctx, 100)
}

// processItems 处理多个项目
func processItems(ctx context.Context, count int) {
	tracer := otel.Tracer("context-propagation")
	ctx, span := tracer.Start(ctx, "process-items")
	defer span.End()

	span.SetAttributes(attribute.Int("items.count", count))

	for i := 0; i < count; i++ {
		// 为每个项目创建子 Span
		processItem(ctx, i)
	}
}

// processItem 处理单个项目
func processItem(ctx context.Context, itemID int) {
	tracer := otel.Tracer("context-propagation")
	_, span := tracer.Start(ctx, "process-item")
	defer span.End()

	span.SetAttributes(
		attribute.Int("item.id", itemID),
	)

	// 模拟处理
	// time.Sleep(10 * time.Millisecond)
}

// AdvancedBaggageExample 高级 Baggage 使用示例
func AdvancedBaggageExample() {
	tracer := otel.Tracer("advanced-baggage")
	ctx := context.Background()

	// 1. 创建带多个属性的 Baggage
	members := []baggage.Member{}

	// 用户信息
	userID, _ := baggage.NewMember("user.id", "user-123")
	userName, _ := baggage.NewMember("user.name", "Alice")
	userRole, _ := baggage.NewMember("user.role", "admin")

	members = append(members, userID, userName, userRole)

	// 请求信息
	requestID, _ := baggage.NewMember("request.id", "req-456")
	correlationID, _ := baggage.NewMember("correlation.id", "corr-789")

	members = append(members, requestID, correlationID)

	// 创建 Baggage
	bag, _ := baggage.New(members...)
	ctx = baggage.ContextWithBaggage(ctx, bag)

	// 2. 在整个调用链中使用
	ctx, span := tracer.Start(ctx, "advanced-operation")
	defer span.End()

	// 从 Baggage 中提取所有信息
	extractedBag := baggage.FromContext(ctx)
	for _, member := range extractedBag.Members() {
		span.SetAttributes(
			attribute.String("baggage."+member.Key(), member.Value()),
		)
	}

	// 3. 条件性地添加 Baggage
	if extractedBag.Member("user.role").Value() == "admin" {
		ctx, _ = AddBaggage(ctx, "admin.permissions", "full")
	}

	// 4. 传递到下游服务
	callDownstreamService(ctx)
}

// callDownstreamService 调用下游服务
func callDownstreamService(ctx context.Context) {
	tracer := otel.Tracer("advanced-baggage")
	ctx, span := tracer.Start(ctx, "downstream-service")
	defer span.End()

	// 读取并使用 Baggage
	bag := baggage.FromContext(ctx)

	// 记录所有 Baggage
	for _, member := range bag.Members() {
		fmt.Printf("Baggage: %s = %s\n", member.Key(), member.Value())
	}

	// 根据 Baggage 执行不同逻辑
	if bag.Member("admin.permissions").Value() == "full" {
		span.AddEvent("admin.access.granted")
	}
}

// BaggageBestPractices Baggage 最佳实践示例
func BaggageBestPractices() {
	// 1. 只在 Baggage 中存储小量数据
	// ✅ 好的做法
	ctx, _ := SetBaggage(context.Background(), "user.id", "123")
	ctx, _ = AddBaggage(ctx, "tenant.id", "tenant-456")

	// ❌ 不好的做法：存储大量数据
	// ctx, _ = SetBaggage(ctx, "user.profile", "{...大量JSON数据...}")

	// 2. 使用有意义的键名
	// ✅ 好的做法
	ctx, _ = SetBaggage(ctx, "request.priority", "high")

	// ❌ 不好的做法
	// ctx, _ = SetBaggage(ctx, "p", "high")

	// 3. 在 Span 中记录 Baggage
	tracer := otel.Tracer("baggage-best-practices")
	_, span := tracer.Start(ctx, "operation")
	defer span.End()

	bag := baggage.FromContext(ctx)
	for _, member := range bag.Members() {
		span.SetAttributes(
			attribute.String("baggage."+member.Key(), member.Value()),
		)
	}

	// 4. 清理不需要的 Baggage
	bag = baggage.FromContext(ctx)
	newBag := bag.DeleteMember("temporary.data")
	ctx = baggage.ContextWithBaggage(ctx, newBag)
	_ = ctx // 避免未使用警告
}
