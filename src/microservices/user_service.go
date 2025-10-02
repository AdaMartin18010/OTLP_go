package microservices

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/trace"
)

// UserService 用户服务实现
type UserService struct {
	tracer     trace.Tracer
	propagator propagation.TextMapPropagator
	users      sync.Map
}

// NewUserService 创建用户服务
func NewUserService() *UserService {
	us := &UserService{
		tracer:     otel.Tracer("user-service"),
		propagator: otel.GetTextMapPropagator(),
	}

	// 初始化一些测试用户
	us.seedUsers()

	return us
}

// User 用户数据结构
type User struct {
	ID        string    `json:"id"`
	Name      string    `json:"name"`
	Email     string    `json:"email"`
	Phone     string    `json:"phone"`
	Level     string    `json:"level"` // normal, vip, premium
	CreatedAt time.Time `json:"created_at"`
}

// seedUsers 初始化测试用户
func (us *UserService) seedUsers() {
	testUsers := []User{
		{
			ID:        "user-001",
			Name:      "Alice",
			Email:     "alice@example.com",
			Phone:     "+1234567890",
			Level:     "vip",
			CreatedAt: time.Now().Add(-365 * 24 * time.Hour),
		},
		{
			ID:        "user-002",
			Name:      "Bob",
			Email:     "bob@example.com",
			Phone:     "+1234567891",
			Level:     "normal",
			CreatedAt: time.Now().Add(-180 * 24 * time.Hour),
		},
		{
			ID:        "user-003",
			Name:      "Charlie",
			Email:     "charlie@example.com",
			Phone:     "+1234567892",
			Level:     "premium",
			CreatedAt: time.Now().Add(-730 * 24 * time.Hour),
		},
	}

	for _, user := range testUsers {
		us.users.Store(user.ID, user)
	}
}

// GetUserHandler 查询用户信息
func (us *UserService) GetUserHandler(w http.ResponseWriter, r *http.Request) {
	ctx := us.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := us.tracer.Start(ctx, "UserService.GetUser",
		trace.WithSpanKind(trace.SpanKindServer),
		trace.WithAttributes(
			attribute.String("service.name", "user-service"),
		),
	)
	defer span.End()

	userID := r.URL.Query().Get("id")
	if userID == "" {
		span.SetStatus(codes.Error, "missing user_id")
		http.Error(w, "Missing user_id", http.StatusBadRequest)
		return
	}

	span.SetAttributes(attribute.String("user.id", userID))

	user, err := us.getUser(ctx, userID)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "user not found")
		http.Error(w, "User not found", http.StatusNotFound)
		return
	}

	span.SetAttributes(
		attribute.String("user.name", user.Name),
		attribute.String("user.level", user.Level),
	)
	span.SetStatus(codes.Ok, "user found")

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(user)
}

// getUser 查询用户
func (us *UserService) getUser(ctx context.Context, userID string) (*User, error) {
	_, span := us.tracer.Start(ctx, "UserService.getUser")
	defer span.End()

	// 模拟数据库查询
	time.Sleep(15 * time.Millisecond)

	value, ok := us.users.Load(userID)
	if !ok {
		err := fmt.Errorf("user not found: %s", userID)
		span.RecordError(err)
		return nil, err
	}

	user := value.(User)
	span.AddEvent("user.loaded", trace.WithAttributes(
		attribute.String("user.id", user.ID),
		attribute.String("user.level", user.Level),
	))

	return &user, nil
}

// CreateUserHandler 创建用户
func (us *UserService) CreateUserHandler(w http.ResponseWriter, r *http.Request) {
	ctx := us.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := us.tracer.Start(ctx, "UserService.CreateUser",
		trace.WithSpanKind(trace.SpanKindServer),
	)
	defer span.End()

	var req struct {
		Name  string `json:"name"`
		Email string `json:"email"`
		Phone string `json:"phone"`
	}

	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		span.RecordError(err)
		http.Error(w, "Invalid request", http.StatusBadRequest)
		return
	}

	user, err := us.createUser(ctx, req.Name, req.Email, req.Phone)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	span.SetAttributes(
		attribute.String("user.id", user.ID),
		attribute.String("user.name", user.Name),
	)
	span.SetStatus(codes.Ok, "user created")

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(user)
}

// createUser 创建用户业务逻辑
func (us *UserService) createUser(ctx context.Context, name, email, phone string) (*User, error) {
	ctx, span := us.tracer.Start(ctx, "UserService.createUser")
	defer span.End()

	// 1. 验证输入
	ctx, validateSpan := us.tracer.Start(ctx, "validate_user_input")
	if name == "" || email == "" {
		err := fmt.Errorf("name and email are required")
		validateSpan.RecordError(err)
		validateSpan.SetStatus(codes.Error, "validation failed")
		validateSpan.End()
		return nil, err
	}
	validateSpan.SetStatus(codes.Ok, "validated")
	validateSpan.End()

	// 2. 检查邮箱是否已存在
	ctx, checkSpan := us.tracer.Start(ctx, "check_email_exists")
	if us.emailExists(ctx, email) {
		err := fmt.Errorf("email already exists: %s", email)
		checkSpan.RecordError(err)
		checkSpan.SetStatus(codes.Error, "email exists")
		checkSpan.End()
		return nil, err
	}
	checkSpan.SetStatus(codes.Ok, "email available")
	checkSpan.End()

	// 3. 创建用户记录
	user := User{
		ID:        fmt.Sprintf("user-%d", time.Now().UnixNano()),
		Name:      name,
		Email:     email,
		Phone:     phone,
		Level:     "normal",
		CreatedAt: time.Now(),
	}

	// 4. 保存到存储
	us.users.Store(user.ID, user)

	span.AddEvent("user.created", trace.WithAttributes(
		attribute.String("user.id", user.ID),
	))

	return &user, nil
}

// UpdateUserLevelHandler 更新用户等级
func (us *UserService) UpdateUserLevelHandler(w http.ResponseWriter, r *http.Request) {
	ctx := us.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := us.tracer.Start(ctx, "UserService.UpdateUserLevel",
		trace.WithSpanKind(trace.SpanKindServer),
	)
	defer span.End()

	var req struct {
		UserID string `json:"user_id"`
		Level  string `json:"level"`
	}

	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		span.RecordError(err)
		http.Error(w, "Invalid request", http.StatusBadRequest)
		return
	}

	if err := us.updateUserLevel(ctx, req.UserID, req.Level); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	span.SetAttributes(
		attribute.String("user.id", req.UserID),
		attribute.String("user.new_level", req.Level),
	)
	span.SetStatus(codes.Ok, "level updated")

	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, "User level updated")
}

// updateUserLevel 更新用户等级
func (us *UserService) updateUserLevel(ctx context.Context, userID, level string) error {
	_, span := us.tracer.Start(ctx, "UserService.updateUserLevel")
	defer span.End()

	value, ok := us.users.Load(userID)
	if !ok {
		err := fmt.Errorf("user not found: %s", userID)
		span.RecordError(err)
		return err
	}

	user := value.(User)
	oldLevel := user.Level
	user.Level = level

	us.users.Store(userID, user)

	span.AddEvent("user.level.updated", trace.WithAttributes(
		attribute.String("user.id", userID),
		attribute.String("old_level", oldLevel),
		attribute.String("new_level", level),
	))

	return nil
}

// GetUserStatsHandler 获取用户统计信息
func (us *UserService) GetUserStatsHandler(w http.ResponseWriter, r *http.Request) {
	ctx := us.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := us.tracer.Start(ctx, "UserService.GetUserStats",
		trace.WithSpanKind(trace.SpanKindServer),
	)
	defer span.End()

	userID := r.URL.Query().Get("id")
	if userID == "" {
		span.SetStatus(codes.Error, "missing user_id")
		http.Error(w, "Missing user_id", http.StatusBadRequest)
		return
	}

	stats, err := us.getUserStats(ctx, userID)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		http.Error(w, err.Error(), http.StatusNotFound)
		return
	}

	span.SetStatus(codes.Ok, "stats retrieved")

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(stats)
}

// getUserStats 获取用户统计信息
func (us *UserService) getUserStats(ctx context.Context, userID string) (map[string]interface{}, error) {
	ctx, span := us.tracer.Start(ctx, "UserService.getUserStats")
	defer span.End()

	// 1. 查询用户基本信息
	user, err := us.getUser(ctx, userID)
	if err != nil {
		return nil, err
	}

	// 2. 计算统计信息（模拟）
	_, calcSpan := us.tracer.Start(ctx, "calculate_stats")
	time.Sleep(30 * time.Millisecond)

	stats := map[string]interface{}{
		"user_id":        user.ID,
		"level":          user.Level,
		"member_days":    int(time.Since(user.CreatedAt).Hours() / 24),
		"total_orders":   42, // 模拟数据
		"total_spent":    1234.56,
		"loyalty_points": 567,
	}

	calcSpan.SetAttributes(
		attribute.Int("total_orders", 42),
		attribute.Float64("total_spent", 1234.56),
	)
	calcSpan.SetStatus(codes.Ok, "stats calculated")
	calcSpan.End()

	return stats, nil
}

// Helper methods
func (us *UserService) emailExists(ctx context.Context, email string) bool {
	exists := false
	us.users.Range(func(key, value interface{}) bool {
		user := value.(User)
		if user.Email == email {
			exists = true
			return false // stop iteration
		}
		return true
	})
	return exists
}

// StartServer 启动用户服务
func (us *UserService) StartServer(addr string) error {
	mux := http.NewServeMux()

	mux.HandleFunc("/users/get", us.GetUserHandler)
	mux.HandleFunc("/users/create", us.CreateUserHandler)
	mux.HandleFunc("/users/update-level", us.UpdateUserLevelHandler)
	mux.HandleFunc("/users/stats", us.GetUserStatsHandler)

	server := &http.Server{
		Addr:         addr,
		Handler:      mux,
		ReadTimeout:  10 * time.Second,
		WriteTimeout: 10 * time.Second,
	}

	fmt.Printf("User Service listening on %s\n", addr)
	return server.ListenAndServe()
}
