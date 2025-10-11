# 53. GraphQL 完整集成 - gqlgen 最佳实践

## 📚 目录

- [53. GraphQL 完整集成 - gqlgen 最佳实践](#53-graphql-完整集成---gqlgen-最佳实践)
  - [📚 目录](#-目录)
  - [1. GraphQL 概述](#1-graphql-概述)
    - [1.1 什么是 GraphQL](#11-什么是-graphql)
    - [1.2 gqlgen 特点](#12-gqlgen-特点)
    - [1.3 依赖版本](#13-依赖版本)
  - [2. gqlgen 快速开始](#2-gqlgen-快速开始)
    - [2.1 项目初始化](#21-项目初始化)
    - [2.2 配置文件](#22-配置文件)
  - [3. Schema 设计](#3-schema-设计)
    - [3.1 基础 Schema](#31-基础-schema)
  - [4. Resolver 实现](#4-resolver-实现)
    - [4.1 基础 Resolver](#41-基础-resolver)
    - [4.2 Query Resolver](#42-query-resolver)
    - [4.3 Mutation Resolver](#43-mutation-resolver)
    - [4.4 Field Resolver](#44-field-resolver)
  - [5. DataLoader（N+1 问题）](#5-dataloadern1-问题)
    - [5.1 UserLoader 实现](#51-userloader-实现)
    - [5.2 DataLoader 中间件](#52-dataloader-中间件)
  - [6. OTLP 完整集成](#6-otlp-完整集成)
    - [6.1 追踪中间件](#61-追踪中间件)
    - [6.2 Metrics 集成](#62-metrics-集成)
  - [7. 认证与授权](#7-认证与授权)
    - [7.1 JWT 认证中间件](#71-jwt-认证中间件)
    - [7.2 指令级授权](#72-指令级授权)
  - [8. 生产级实践](#8-生产级实践)
    - [8.1 完整服务器](#81-完整服务器)
    - [8.2 性能优化](#82-性能优化)
  - [9. 总结](#9-总结)
    - [核心优势](#核心优势)
    - [最佳实践](#最佳实践)
    - [相关文档](#相关文档)

---

## 1. GraphQL 概述

### 1.1 什么是 GraphQL

GraphQL 是一种用于 API 的查询语言和运行时，允许客户端精确指定所需数据。

**核心优势**:

- ✅ **按需获取** - 避免过度获取和不足获取
- ✅ **强类型** - Schema 定义清晰
- ✅ **单一端点** - 统一的 API 入口
- ✅ **实时更新** - Subscription 支持
- ✅ **开发效率** - 减少 API 版本管理

### 1.2 gqlgen 特点

**gqlgen** 是 Go 语言中最流行的 GraphQL 服务器库。

**核心特点**:

- ✅ Schema-first 设计
- ✅ 代码生成
- ✅ 类型安全
- ✅ 高性能
- ✅ 易于集成

### 1.3 依赖版本

```go
// go.mod
module github.com/yourorg/graphql-service

go 1.25.1

require (
    // GraphQL
    github.com/99designs/gqlgen v0.17.59
    github.com/vektah/gqlparser/v2 v2.5.20
    
    // DataLoader
    github.com/graph-gophers/dataloader/v7 v7.1.0
    
    // OTLP
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/trace v1.32.0
    go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp v0.57.0
    
    // 工具
    github.com/go-chi/chi/v5 v5.1.0
)
```

---

## 2. gqlgen 快速开始

### 2.1 项目初始化

```bash
# 安装 gqlgen
go get github.com/99designs/gqlgen

# 初始化项目
go run github.com/99designs/gqlgen init

# 目录结构
# .
# ├── graph/
# │   ├── schema.graphqls      # GraphQL Schema
# │   ├── generated.go         # 自动生成
# │   ├── model/
# │   │   └── models_gen.go    # 自动生成的模型
# │   └── resolver.go          # Resolver 实现
# ├── server.go                # 服务器入口
# └── gqlgen.yml               # 配置文件
```

### 2.2 配置文件

```yaml
# gqlgen.yml
schema:
  - graph/*.graphqls

exec:
  filename: graph/generated.go
  package: graph

model:
  filename: graph/model/models_gen.go
  package: model

resolver:
  layout: follow-schema
  dir: graph
  package: graph
  filename_template: "{name}.resolvers.go"

# 自定义标量
models:
  ID:
    model:
      - github.com/99designs/gqlgen/graphql.ID
  Time:
    model:
      - github.com/99designs/gqlgen/graphql.Time
```

---

## 3. Schema 设计

### 3.1 基础 Schema

```graphql
# graph/schema.graphqls

# 标量类型
scalar Time
scalar Upload

# 用户类型
type User {
  id: ID!
  email: String!
  username: String!
  posts: [Post!]!
  createdAt: Time!
  updatedAt: Time!
}

# 文章类型
type Post {
  id: ID!
  title: String!
  content: String!
  author: User!
  comments: [Comment!]!
  createdAt: Time!
  updatedAt: Time!
}

# 评论类型
type Comment {
  id: ID!
  content: String!
  author: User!
  post: Post!
  createdAt: Time!
}

# 分页信息
type PageInfo {
  hasNextPage: Boolean!
  hasPreviousPage: Boolean!
  startCursor: String
  endCursor: String
}

# 用户连接（分页）
type UserConnection {
  edges: [UserEdge!]!
  pageInfo: PageInfo!
  totalCount: Int!
}

type UserEdge {
  node: User!
  cursor: String!
}

# 输入类型
input CreateUserInput {
  email: String!
  username: String!
  password: String!
}

input UpdateUserInput {
  email: String
  username: String
}

input CreatePostInput {
  title: String!
  content: String!
}

# 查询
type Query {
  # 用户查询
  user(id: ID!): User
  users(first: Int, after: String): UserConnection!
  me: User!
  
  # 文章查询
  post(id: ID!): Post
  posts(first: Int = 10, after: String): [Post!]!
  
  # 搜索
  search(query: String!): [SearchResult!]!
}

# 联合类型
union SearchResult = User | Post | Comment

# 变更
type Mutation {
  # 用户操作
  createUser(input: CreateUserInput!): User!
  updateUser(id: ID!, input: UpdateUserInput!): User!
  deleteUser(id: ID!): Boolean!
  
  # 文章操作
  createPost(input: CreatePostInput!): Post!
  updatePost(id: ID!, title: String, content: String): Post!
  deletePost(id: ID!): Boolean!
  
  # 评论操作
  createComment(postID: ID!, content: String!): Comment!
  
  # 文件上传
  uploadFile(file: Upload!): String!
}

# 订阅
type Subscription {
  postCreated: Post!
  commentAdded(postID: ID!): Comment!
}
```

---

## 4. Resolver 实现

### 4.1 基础 Resolver

```go
// graph/resolver.go
package graph

import (
    "context"
    
    "github.com/yourorg/graphql-service/graph/model"
    "go.opentelemetry.io/otel/trace"
)

// Resolver 根 Resolver
type Resolver struct {
    userService    *UserService
    postService    *PostService
    commentService *CommentService
    tracer         trace.Tracer
}

// NewResolver 创建 Resolver
func NewResolver(
    userService *UserService,
    postService *PostService,
    commentService *CommentService,
    tracer trace.Tracer,
) *Resolver {
    return &Resolver{
        userService:    userService,
        postService:    postService,
        commentService: commentService,
        tracer:         tracer,
    }
}
```

### 4.2 Query Resolver

```go
// graph/query.resolvers.go
package graph

import (
    "context"
    
    "github.com/yourorg/graphql-service/graph/model"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// User 查询单个用户
func (r *queryResolver) User(ctx context.Context, id string) (*model.User, error) {
    ctx, span := r.tracer.Start(ctx, "Query.user",
        trace.WithAttributes(
            attribute.String("user.id", id),
        ),
    )
    defer span.End()
    
    user, err := r.userService.GetByID(ctx, id)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "failed to get user")
        return nil, err
    }
    
    span.SetStatus(codes.Ok, "")
    return user, nil
}

// Users 查询用户列表（分页）
func (r *queryResolver) Users(ctx context.Context, first *int, after *string) (*model.UserConnection, error) {
    ctx, span := r.tracer.Start(ctx, "Query.users")
    defer span.End()
    
    limit := 10
    if first != nil {
        limit = *first
    }
    
    var cursor string
    if after != nil {
        cursor = *after
    }
    
    users, pageInfo, err := r.userService.List(ctx, limit, cursor)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "failed to list users")
        return nil, err
    }
    
    edges := make([]*model.UserEdge, len(users))
    for i, user := range users {
        edges[i] = &model.UserEdge{
            Node:   user,
            Cursor: user.ID,
        }
    }
    
    connection := &model.UserConnection{
        Edges:      edges,
        PageInfo:   pageInfo,
        TotalCount: len(users),
    }
    
    span.SetStatus(codes.Ok, "")
    return connection, nil
}

// Me 获取当前用户
func (r *queryResolver) Me(ctx context.Context) (*model.User, error) {
    ctx, span := r.tracer.Start(ctx, "Query.me")
    defer span.End()
    
    // 从 Context 获取用户 ID
    userID, ok := ctx.Value("user_id").(string)
    if !ok {
        span.SetStatus(codes.Error, "unauthorized")
        return nil, fmt.Errorf("unauthorized")
    }
    
    user, err := r.userService.GetByID(ctx, userID)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "failed to get user")
        return nil, err
    }
    
    span.SetStatus(codes.Ok, "")
    return user, nil
}

// Post 查询单个文章
func (r *queryResolver) Post(ctx context.Context, id string) (*model.Post, error) {
    ctx, span := r.tracer.Start(ctx, "Query.post")
    defer span.End()
    
    post, err := r.postService.GetByID(ctx, id)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    return post, nil
}

// Search 搜索
func (r *queryResolver) Search(ctx context.Context, query string) ([]model.SearchResult, error) {
    ctx, span := r.tracer.Start(ctx, "Query.search",
        trace.WithAttributes(
            attribute.String("search.query", query),
        ),
    )
    defer span.End()
    
    // 搜索用户和文章
    users, _ := r.userService.Search(ctx, query)
    posts, _ := r.postService.Search(ctx, query)
    
    results := make([]model.SearchResult, 0)
    for _, user := range users {
        results = append(results, user)
    }
    for _, post := range posts {
        results = append(results, post)
    }
    
    span.SetStatus(codes.Ok, "")
    return results, nil
}
```

### 4.3 Mutation Resolver

```go
// graph/mutation.resolvers.go
package graph

import (
    "context"
    
    "github.com/yourorg/graphql-service/graph/model"
)

// CreateUser 创建用户
func (r *mutationResolver) CreateUser(ctx context.Context, input model.CreateUserInput) (*model.User, error) {
    ctx, span := r.tracer.Start(ctx, "Mutation.createUser")
    defer span.End()
    
    user, err := r.userService.Create(ctx, input.Email, input.Username, input.Password)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    return user, nil
}

// UpdateUser 更新用户
func (r *mutationResolver) UpdateUser(ctx context.Context, id string, input model.UpdateUserInput) (*model.User, error) {
    ctx, span := r.tracer.Start(ctx, "Mutation.updateUser")
    defer span.End()
    
    user, err := r.userService.Update(ctx, id, input)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    return user, nil
}

// CreatePost 创建文章
func (r *mutationResolver) CreatePost(ctx context.Context, input model.CreatePostInput) (*model.Post, error) {
    ctx, span := r.tracer.Start(ctx, "Mutation.createPost")
    defer span.End()
    
    // 获取当前用户
    userID := ctx.Value("user_id").(string)
    
    post, err := r.postService.Create(ctx, userID, input.Title, input.Content)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    // 发布订阅事件
    r.postCreated <- post
    
    return post, nil
}
```

### 4.4 Field Resolver

```go
// graph/user.resolvers.go
package graph

import (
    "context"
    
    "github.com/yourorg/graphql-service/graph/model"
)

// Posts 用户的文章列表
func (r *userResolver) Posts(ctx context.Context, obj *model.User) ([]*model.Post, error) {
    ctx, span := r.tracer.Start(ctx, "User.posts")
    defer span.End()
    
    // 使用 DataLoader 避免 N+1 问题
    loader := GetPostLoader(ctx)
    return loader.Load(obj.ID)
}

// graph/post.resolvers.go
// Author 文章作者
func (r *postResolver) Author(ctx context.Context, obj *model.Post) (*model.User, error) {
    ctx, span := r.tracer.Start(ctx, "Post.author")
    defer span.End()
    
    // 使用 DataLoader
    loader := GetUserLoader(ctx)
    return loader.Load(obj.AuthorID)
}

// Comments 文章评论
func (r *postResolver) Comments(ctx context.Context, obj *model.Post) ([]*model.Comment, error) {
    ctx, span := r.tracer.Start(ctx, "Post.comments")
    defer span.End()
    
    return r.commentService.GetByPostID(ctx, obj.ID)
}
```

---

## 5. DataLoader（N+1 问题）

### 5.1 UserLoader 实现

```go
// graph/dataloader.go
package graph

import (
    "context"
    "time"
    
    "github.com/graph-gophers/dataloader/v7"
    "github.com/yourorg/graphql-service/graph/model"
)

type contextKey string

const (
    userLoaderKey contextKey = "user_loader"
    postLoaderKey contextKey = "post_loader"
)

// UserLoader 用户加载器
type UserLoader struct {
    *dataloader.Loader[string, *model.User]
}

// NewUserLoader 创建用户加载器
func NewUserLoader(userService *UserService) *UserLoader {
    batchFn := func(ctx context.Context, keys []string) []*dataloader.Result[*model.User] {
        // 批量加载用户
        users, err := userService.GetByIDs(ctx, keys)
        if err != nil {
            results := make([]*dataloader.Result[*model.User], len(keys))
            for i := range keys {
                results[i] = &dataloader.Result[*model.User]{Error: err}
            }
            return results
        }
        
        // 构建结果映射
        userMap := make(map[string]*model.User)
        for _, user := range users {
            userMap[user.ID] = user
        }
        
        // 按原始顺序返回结果
        results := make([]*dataloader.Result[*model.User], len(keys))
        for i, key := range keys {
            if user, ok := userMap[key]; ok {
                results[i] = &dataloader.Result[*model.User]{Data: user}
            } else {
                results[i] = &dataloader.Result[*model.User]{Error: fmt.Errorf("user not found: %s", key)}
            }
        }
        
        return results
    }
    
    loader := dataloader.NewBatchedLoader(
        batchFn,
        dataloader.WithWait[string, *model.User](10*time.Millisecond),
        dataloader.WithBatchCapacity[string, *model.User](100),
    )
    
    return &UserLoader{Loader: loader}
}

// Load 加载单个用户
func (l *UserLoader) Load(ctx context.Context, id string) (*model.User, error) {
    return l.Loader.Load(ctx, id)()
}

// LoadMany 加载多个用户
func (l *UserLoader) LoadMany(ctx context.Context, ids []string) ([]*model.User, error) {
    results := l.Loader.LoadMany(ctx, ids)()
    users := make([]*model.User, len(results))
    for i, result := range results {
        if result.Error != nil {
            return nil, result.Error
        }
        users[i] = result.Data
    }
    return users, nil
}

// GetUserLoader 从 Context 获取用户加载器
func GetUserLoader(ctx context.Context) *UserLoader {
    return ctx.Value(userLoaderKey).(*UserLoader)
}
```

### 5.2 DataLoader 中间件

```go
// graph/middleware.go
package graph

import (
    "context"
    "net/http"
)

// DataLoaderMiddleware DataLoader 中间件
func DataLoaderMiddleware(userService *UserService, postService *PostService) func(http.Handler) http.Handler {
    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            ctx := r.Context()
            
            // 创建 DataLoader
            userLoader := NewUserLoader(userService)
            postLoader := NewPostLoader(postService)
            
            // 存入 Context
            ctx = context.WithValue(ctx, userLoaderKey, userLoader)
            ctx = context.WithValue(ctx, postLoaderKey, postLoader)
            
            next.ServeHTTP(w, r.WithContext(ctx))
        })
    }
}
```

---

## 6. OTLP 完整集成

### 6.1 追踪中间件

```go
// graph/tracing.go
package graph

import (
    "context"
    
    "github.com/99designs/gqlgen/graphql"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// TracingMiddleware GraphQL 追踪中间件
type TracingMiddleware struct {
    tracer trace.Tracer
}

// NewTracingMiddleware 创建追踪中间件
func NewTracingMiddleware() *TracingMiddleware {
    return &TracingMiddleware{
        tracer: otel.Tracer("graphql"),
    }
}

// OperationMiddleware 操作级别追踪
func (m *TracingMiddleware) OperationMiddleware() graphql.OperationMiddleware {
    return func(ctx context.Context, next graphql.OperationHandler) graphql.ResponseHandler {
        oc := graphql.GetOperationContext(ctx)
        
        ctx, span := m.tracer.Start(ctx, "GraphQL Operation",
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                attribute.String("graphql.operation.name", oc.OperationName),
                attribute.String("graphql.operation.type", string(oc.Operation.Operation)),
                attribute.String("graphql.query", oc.RawQuery),
            ),
        )
        defer span.End()
        
        responseHandler := next(ctx)
        
        return func(ctx context.Context) *graphql.Response {
            resp := responseHandler(ctx)
            
            if len(resp.Errors) > 0 {
                span.RecordError(resp.Errors[0])
                span.SetStatus(codes.Error, "GraphQL errors")
            } else {
                span.SetStatus(codes.Ok, "")
            }
            
            return resp
        }
    }
}

// FieldMiddleware 字段级别追踪
func (m *TracingMiddleware) FieldMiddleware() graphql.FieldMiddleware {
    return func(ctx context.Context, next graphql.Resolver) (interface{}, error) {
        fc := graphql.GetFieldContext(ctx)
        
        ctx, span := m.tracer.Start(ctx, fc.Field.Name,
            trace.WithAttributes(
                attribute.String("graphql.field.name", fc.Field.Name),
                attribute.String("graphql.field.alias", fc.Field.Alias),
                attribute.String("graphql.field.path", fc.Path().String()),
            ),
        )
        defer span.End()
        
        res, err := next(ctx)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "field resolver failed")
        } else {
            span.SetStatus(codes.Ok, "")
        }
        
        return res, err
    }
}
```

### 6.2 Metrics 集成

```go
// graph/metrics.go
package graph

import (
    "context"
    
    "github.com/99designs/gqlgen/graphql"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

// MetricsMiddleware GraphQL 指标中间件
type MetricsMiddleware struct {
    requestCounter  metric.Int64Counter
    requestDuration metric.Float64Histogram
    errorCounter    metric.Int64Counter
}

// NewMetricsMiddleware 创建指标中间件
func NewMetricsMiddleware() (*MetricsMiddleware, error) {
    meter := otel.Meter("graphql")
    
    requestCounter, err := meter.Int64Counter(
        "graphql.requests",
        metric.WithDescription("GraphQL requests count"),
    )
    if err != nil {
        return nil, err
    }
    
    requestDuration, err := meter.Float64Histogram(
        "graphql.request.duration",
        metric.WithDescription("GraphQL request duration"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }
    
    errorCounter, err := meter.Int64Counter(
        "graphql.errors",
        metric.WithDescription("GraphQL errors count"),
    )
    if err != nil {
        return nil, err
    }
    
    return &MetricsMiddleware{
        requestCounter:  requestCounter,
        requestDuration: requestDuration,
        errorCounter:    errorCounter,
    }, nil
}

// OperationMiddleware 操作指标
func (m *MetricsMiddleware) OperationMiddleware() graphql.OperationMiddleware {
    return func(ctx context.Context, next graphql.OperationHandler) graphql.ResponseHandler {
        oc := graphql.GetOperationContext(ctx)
        start := time.Now()
        
        responseHandler := next(ctx)
        
        return func(ctx context.Context) *graphql.Response {
            resp := responseHandler(ctx)
            duration := time.Since(start)
            
            attrs := metric.WithAttributes(
                attribute.String("operation.name", oc.OperationName),
                attribute.String("operation.type", string(oc.Operation.Operation)),
            )
            
            m.requestCounter.Add(ctx, 1, attrs)
            m.requestDuration.Record(ctx, float64(duration.Milliseconds()), attrs)
            
            if len(resp.Errors) > 0 {
                m.errorCounter.Add(ctx, int64(len(resp.Errors)), attrs)
            }
            
            return resp
        }
    }
}
```

---

## 7. 认证与授权

### 7.1 JWT 认证中间件

```go
// graph/auth.go
package graph

import (
    "context"
    "net/http"
    "strings"
    
    "github.com/golang-jwt/jwt/v5"
)

// AuthMiddleware JWT 认证中间件
func AuthMiddleware(secretKey string) func(http.Handler) http.Handler {
    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            // 获取 Authorization header
            authHeader := r.Header.Get("Authorization")
            if authHeader == "" {
                next.ServeHTTP(w, r)
                return
            }
            
            // 解析 Bearer token
            tokenString := strings.TrimPrefix(authHeader, "Bearer ")
            
            // 验证 JWT
            token, err := jwt.Parse(tokenString, func(token *jwt.Token) (interface{}, error) {
                return []byte(secretKey), nil
            })
            
            if err != nil || !token.Valid {
                http.Error(w, "Unauthorized", http.StatusUnauthorized)
                return
            }
            
            // 提取用户信息
            claims := token.Claims.(jwt.MapClaims)
            userID := claims["user_id"].(string)
            
            // 存入 Context
            ctx := context.WithValue(r.Context(), "user_id", userID)
            next.ServeHTTP(w, r.WithContext(ctx))
        })
    }
}
```

### 7.2 指令级授权

```graphql
# 定义指令
directive @auth on FIELD_DEFINITION
directive @hasRole(role: String!) on FIELD_DEFINITION

type Query {
  me: User! @auth
  adminPanel: AdminPanel! @hasRole(role: "admin")
}
```

```go
// 实现指令
func AuthDirective(ctx context.Context, obj interface{}, next graphql.Resolver) (interface{}, error) {
    userID, ok := ctx.Value("user_id").(string)
    if !ok || userID == "" {
        return nil, fmt.Errorf("unauthorized")
    }
    
    return next(ctx)
}

func HasRoleDirective(ctx context.Context, obj interface{}, next graphql.Resolver, role string) (interface{}, error) {
    userRole, ok := ctx.Value("user_role").(string)
    if !ok || userRole != role {
        return nil, fmt.Errorf("forbidden")
    }
    
    return next(ctx)
}
```

---

## 8. 生产级实践

### 8.1 完整服务器

```go
// server.go
package main

import (
    "log"
    "net/http"
    "os"
    
    "github.com/99designs/gqlgen/graphql/handler"
    "github.com/99designs/gqlgen/graphql/playground"
    "github.com/go-chi/chi/v5"
    "github.com/go-chi/chi/v5/middleware"
    
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    
    "github.com/yourorg/graphql-service/graph"
)

func main() {
    // 初始化服务
    userService := NewUserService()
    postService := NewPostService()
    commentService := NewCommentService()
    
    // 创建 Resolver
    resolver := graph.NewResolver(userService, postService, commentService, tracer)
    
    // 创建 GraphQL 服务器
    srv := handler.NewDefaultServer(graph.NewExecutableSchema(graph.Config{
        Resolvers: resolver,
    }))
    
    // 添加中间件
    tracingMiddleware := graph.NewTracingMiddleware()
    srv.Use(tracingMiddleware.OperationMiddleware())
    srv.Use(tracingMiddleware.FieldMiddleware())
    
    metricsMiddleware, _ := graph.NewMetricsMiddleware()
    srv.Use(metricsMiddleware.OperationMiddleware())
    
    // 创建路由
    r := chi.NewRouter()
    
    // 基础中间件
    r.Use(middleware.RequestID)
    r.Use(middleware.RealIP)
    r.Use(middleware.Logger)
    r.Use(middleware.Recoverer)
    
    // DataLoader 中间件
    r.Use(graph.DataLoaderMiddleware(userService, postService))
    
    // 认证中间件
    r.Use(graph.AuthMiddleware(os.Getenv("JWT_SECRET")))
    
    // GraphQL 端点
    r.Handle("/query", otelhttp.NewHandler(srv, "graphql"))
    
    // Playground
    r.Handle("/", playground.Handler("GraphQL Playground", "/query"))
    
    log.Println("Server starting on :8080")
    log.Fatal(http.ListenAndServe(":8080", r))
}
```

### 8.2 性能优化

```go
// 查询复杂度限制
srv.Use(extension.FixedComplexityLimit(1000))

// 查询深度限制
srv.Use(extension.FixedComplexityLimit(10))

// APQ (Automatic Persisted Queries)
srv.Use(extension.AutomaticPersistedQuery{
    Cache: cache,
})
```

---

## 9. 总结

### 核心优势

✅ **灵活查询** - 客户端按需获取  
✅ **强类型** - Schema 定义清晰  
✅ **单一端点** - 简化 API 管理  
✅ **实时更新** - Subscription 支持  
✅ **完整追踪** - OTLP 集成

### 最佳实践

1. ✅ Schema-first 设计
2. ✅ 使用 DataLoader 解决 N+1 问题
3. ✅ 实现完整的 OTLP 追踪
4. ✅ 查询复杂度和深度限制
5. ✅ 实现认证和授权
6. ✅ 错误处理
7. ✅ 性能监控
8. ✅ APQ 优化

### 相关文档

- [49_Chi框架深度集成](./49_Chi框架深度集成与最佳实践.md)
- [51_gRPC完整集成指南](./51_gRPC完整集成指南与最佳实践.md)

---

**版本**: v1.0.0  
**最后更新**: 2025-10-11  
**gqlgen 版本**: v0.17.59
