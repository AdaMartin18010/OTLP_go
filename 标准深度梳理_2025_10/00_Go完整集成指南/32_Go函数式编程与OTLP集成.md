# Go 函数式编程与 OTLP 集成

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [Go 函数式编程与 OTLP 集成](#go-函数式编程与-otlp-集成)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [函数式编程基础](#函数式编程基础)
    - [1. 一等函数与追踪](#1-一等函数与追踪)
    - [2. 函数式集合操作](#2-函数式集合操作)
  - [高阶函数与追踪](#高阶函数与追踪)
    - [完整的高阶函数实现](#完整的高阶函数实现)
  - [函数组合模式](#函数组合模式)
    - [完整的函数组合实现](#完整的函数组合实现)
  - [柯里化与偏函数](#柯里化与偏函数)
  - [Monad 模式](#monad-模式)
    - [Result Monad](#result-monad)
    - [Option Monad](#option-monad)
  - [函数式错误处理](#函数式错误处理)
  - [实战案例](#实战案例)
    - [HTTP 请求处理的函数式实现](#http-请求处理的函数式实现)
  - [总结](#总结)

---

## 概述

虽然 Go 不是纯函数式语言，但通过泛型和高阶函数，我们可以实现函数式编程模式，并与 OpenTelemetry 深度集成。

**函数式编程核心概念**:

```text
✅ 一等函数 (First-class functions)
✅ 高阶函数 (Higher-order functions)
✅ 不可变性 (Immutability)
✅ 纯函数 (Pure functions)
✅ 函数组合 (Function composition)
✅ 柯里化 (Currying)
✅ Monad 模式
✅ 惰性求值 (Lazy evaluation)
```

---

## 函数式编程基础

### 1. 一等函数与追踪

```go
package functional

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// Func 泛型函数类型
type Func[T, R any] func(context.Context, T) (R, error)

// TracedFunc 带追踪的函数包装器
func TracedFunc[T, R any](
    name string,
    fn Func[T, R],
) Func[T, R] {
    tracer := otel.Tracer("functional")
    
    return func(ctx context.Context, input T) (R, error) {
        ctx, span := tracer.Start(ctx, name,
            trace.WithAttributes(
                attribute.String("function.name", name),
            ),
        )
        defer span.End()
        
        start := time.Now()
        result, err := fn(ctx, input)
        duration := time.Since(start)
        
        span.SetAttributes(
            attribute.Float64("duration_ms", float64(duration.Milliseconds())),
        )
        
        if err != nil {
            span.RecordError(err)
        }
        
        return result, err
    }
}

// Pure 纯函数标记（无副作用）
type Pure[T, R any] func(T) R

// TracedPure 带追踪的纯函数
func TracedPure[T, R any](
    name string,
    fn Pure[T, R],
) Func[T, R] {
    tracer := otel.Tracer("functional")
    
    return func(ctx context.Context, input T) (R, error) {
        ctx, span := tracer.Start(ctx, name,
            trace.WithAttributes(
                attribute.String("function.type", "pure"),
            ),
        )
        defer span.End()
        
        result := fn(input)
        
        span.AddEvent("pure function executed")
        return result, nil
    }
}
```

### 2. 函数式集合操作

```go
package functional

import (
    "context"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// Map 映射操作
func Map[T, R any](
    ctx context.Context,
    items []T,
    fn Func[T, R],
) ([]R, error) {
    tracer := otel.Tracer("functional")
    
    ctx, span := tracer.Start(ctx, "functional.map",
        trace.WithAttributes(
            attribute.Int("items.count", len(items)),
        ),
    )
    defer span.End()
    
    results := make([]R, 0, len(items))
    
    for i, item := range items {
        span.AddEvent("processing item", trace.WithAttributes(
            attribute.Int("item.index", i),
        ))
        
        result, err := fn(ctx, item)
        if err != nil {
            span.RecordError(err)
            return nil, err
        }
        
        results = append(results, result)
    }
    
    return results, nil
}

// Filter 过滤操作
func Filter[T any](
    ctx context.Context,
    items []T,
    predicate func(context.Context, T) (bool, error),
) ([]T, error) {
    tracer := otel.Tracer("functional")
    
    ctx, span := tracer.Start(ctx, "functional.filter",
        trace.WithAttributes(
            attribute.Int("items.count", len(items)),
        ),
    )
    defer span.End()
    
    results := make([]T, 0)
    
    for _, item := range items {
        keep, err := predicate(ctx, item)
        if err != nil {
            span.RecordError(err)
            return nil, err
        }
        
        if keep {
            results = append(results, item)
        }
    }
    
    span.SetAttributes(
        attribute.Int("filtered.count", len(results)),
    )
    
    return results, nil
}

// Reduce 归约操作
func Reduce[T, R any](
    ctx context.Context,
    items []T,
    initial R,
    reducer func(context.Context, R, T) (R, error),
) (R, error) {
    tracer := otel.Tracer("functional")
    
    ctx, span := tracer.Start(ctx, "functional.reduce",
        trace.WithAttributes(
            attribute.Int("items.count", len(items)),
        ),
    )
    defer span.End()
    
    accumulator := initial
    
    for i, item := range items {
        span.AddEvent("reducing item", trace.WithAttributes(
            attribute.Int("item.index", i),
        ))
        
        result, err := reducer(ctx, accumulator, item)
        if err != nil {
            span.RecordError(err)
            return accumulator, err
        }
        
        accumulator = result
    }
    
    return accumulator, nil
}

// FlatMap 扁平化映射
func FlatMap[T, R any](
    ctx context.Context,
    items []T,
    fn func(context.Context, T) ([]R, error),
) ([]R, error) {
    tracer := otel.Tracer("functional")
    
    ctx, span := tracer.Start(ctx, "functional.flatmap",
        trace.WithAttributes(
            attribute.Int("items.count", len(items)),
        ),
    )
    defer span.End()
    
    results := make([]R, 0)
    
    for _, item := range items {
        mapped, err := fn(ctx, item)
        if err != nil {
            span.RecordError(err)
            return nil, err
        }
        
        results = append(results, mapped...)
    }
    
    span.SetAttributes(
        attribute.Int("results.count", len(results)),
    )
    
    return results, nil
}

// ParallelMap 并行映射
func ParallelMap[T, R any](
    ctx context.Context,
    items []T,
    fn Func[T, R],
    concurrency int,
) ([]R, error) {
    tracer := otel.Tracer("functional")
    
    ctx, span := tracer.Start(ctx, "functional.parallel_map",
        trace.WithAttributes(
            attribute.Int("items.count", len(items)),
            attribute.Int("concurrency", concurrency),
        ),
    )
    defer span.End()
    
    results := make([]R, len(items))
    errors := make([]error, len(items))
    
    // 创建工作 channel
    jobs := make(chan int, len(items))
    for i := range items {
        jobs <- i
    }
    close(jobs)
    
    // 启动 workers
    var wg sync.WaitGroup
    for w := 0; w < concurrency; w++ {
        wg.Add(1)
        
        go func() {
            defer wg.Done()
            
            for i := range jobs {
                result, err := fn(ctx, items[i])
                results[i] = result
                errors[i] = err
            }
        }()
    }
    
    wg.Wait()
    
    // 检查错误
    for _, err := range errors {
        if err != nil {
            span.RecordError(err)
            return nil, err
        }
    }
    
    return results, nil
}
```

---

## 高阶函数与追踪

### 完整的高阶函数实现

```go
package functional

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// Middleware 函数中间件类型
type Middleware[T, R any] func(Func[T, R]) Func[T, R]

// WithTracing 追踪中间件
func WithTracing[T, R any](name string) Middleware[T, R] {
    tracer := otel.Tracer("functional")
    
    return func(next Func[T, R]) Func[T, R] {
        return func(ctx context.Context, input T) (R, error) {
            ctx, span := tracer.Start(ctx, name)
            defer span.End()
            
            result, err := next(ctx, input)
            
            if err != nil {
                span.RecordError(err)
                span.SetStatus(codes.Error, err.Error())
            } else {
                span.SetStatus(codes.Ok, "")
            }
            
            return result, err
        }
    }
}

// WithRetry 重试中间件
func WithRetry[T, R any](maxRetries int, backoff time.Duration) Middleware[T, R] {
    tracer := otel.Tracer("functional")
    
    return func(next Func[T, R]) Func[T, R] {
        return func(ctx context.Context, input T) (R, error) {
            ctx, span := tracer.Start(ctx, "middleware.retry",
                trace.WithAttributes(
                    attribute.Int("max_retries", maxRetries),
                ),
            )
            defer span.End()
            
            var result R
            var err error
            
            for attempt := 0; attempt <= maxRetries; attempt++ {
                span.AddEvent("attempt", trace.WithAttributes(
                    attribute.Int("attempt", attempt),
                ))
                
                result, err = next(ctx, input)
                
                if err == nil {
                    span.SetAttributes(
                        attribute.Int("successful_attempt", attempt),
                    )
                    return result, nil
                }
                
                if attempt < maxRetries {
                    time.Sleep(backoff * time.Duration(attempt+1))
                }
            }
            
            span.RecordError(err)
            span.SetAttributes(
                attribute.Int("failed_attempts", maxRetries+1),
            )
            
            return result, err
        }
    }
}

// WithTimeout 超时中间件
func WithTimeout[T, R any](timeout time.Duration) Middleware[T, R] {
    tracer := otel.Tracer("functional")
    
    return func(next Func[T, R]) Func[T, R] {
        return func(ctx context.Context, input T) (R, error) {
            ctx, span := tracer.Start(ctx, "middleware.timeout",
                trace.WithAttributes(
                    attribute.Float64("timeout_ms", float64(timeout.Milliseconds())),
                ),
            )
            defer span.End()
            
            ctx, cancel := context.WithTimeout(ctx, timeout)
            defer cancel()
            
            type result struct {
                value R
                err   error
            }
            
            resultCh := make(chan result, 1)
            
            go func() {
                value, err := next(ctx, input)
                resultCh <- result{value, err}
            }()
            
            select {
            case res := <-resultCh:
                return res.value, res.err
                
            case <-ctx.Done():
                span.RecordError(ctx.Err())
                span.SetAttributes(attribute.Bool("timeout", true))
                
                var zero R
                return zero, ctx.Err()
            }
        }
    }
}

// WithCache 缓存中间件
func WithCache[T comparable, R any](cache *sync.Map) Middleware[T, R] {
    tracer := otel.Tracer("functional")
    
    return func(next Func[T, R]) Func[T, R] {
        return func(ctx context.Context, input T) (R, error) {
            ctx, span := tracer.Start(ctx, "middleware.cache")
            defer span.End()
            
            // 检查缓存
            if cached, ok := cache.Load(input); ok {
                span.SetAttributes(
                    attribute.Bool("cache_hit", true),
                )
                return cached.(R), nil
            }
            
            span.SetAttributes(
                attribute.Bool("cache_hit", false),
            )
            
            // 执行函数
            result, err := next(ctx, input)
            if err != nil {
                return result, err
            }
            
            // 存入缓存
            cache.Store(input, result)
            
            return result, nil
        }
    }
}

// Chain 链式组合中间件
func Chain[T, R any](middlewares ...Middleware[T, R]) Middleware[T, R] {
    return func(final Func[T, R]) Func[T, R] {
        // 从右向左应用中间件
        for i := len(middlewares) - 1; i >= 0; i-- {
            final = middlewares[i](final)
        }
        return final
    }
}

// 使用示例
func ExampleMiddlewareChain() Func[string, string] {
    // 定义基础函数
    baseFunc := func(ctx context.Context, input string) (string, error) {
        // 处理逻辑
        return "processed: " + input, nil
    }
    
    // 组合中间件
    enhanced := Chain(
        WithTracing[string, string]("process-string"),
        WithRetry[string, string](3, 100*time.Millisecond),
        WithTimeout[string, string](5*time.Second),
    )(baseFunc)
    
    return enhanced
}
```

---

## 函数组合模式

### 完整的函数组合实现

```go
package functional

import (
    "context"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// Compose 组合两个函数 (f ∘ g)
func Compose[A, B, C any](
    f Func[B, C],
    g Func[A, B],
) Func[A, C] {
    tracer := otel.Tracer("functional")
    
    return func(ctx context.Context, a A) (C, error) {
        ctx, span := tracer.Start(ctx, "compose")
        defer span.End()
        
        // 先执行 g
        b, err := g(ctx, a)
        if err != nil {
            span.RecordError(err)
            var zero C
            return zero, err
        }
        
        // 再执行 f
        c, err := f(ctx, b)
        if err != nil {
            span.RecordError(err)
            return c, err
        }
        
        return c, nil
    }
}

// Pipe 管道组合 (从左到右)
func Pipe[T any](fns ...Func[T, T]) Func[T, T] {
    tracer := otel.Tracer("functional")
    
    return func(ctx context.Context, input T) (T, error) {
        ctx, span := tracer.Start(ctx, "pipe",
            trace.WithAttributes(
                attribute.Int("functions.count", len(fns)),
            ),
        )
        defer span.End()
        
        current := input
        
        for i, fn := range fns {
            span.AddEvent("executing function", trace.WithAttributes(
                attribute.Int("function.index", i),
            ))
            
            result, err := fn(ctx, current)
            if err != nil {
                span.RecordError(err)
                span.SetAttributes(
                    attribute.Int("failed.function", i),
                )
                return current, err
            }
            
            current = result
        }
        
        return current, nil
    }
}

// ComposeN 组合多个函数
func ComposeN[T any](fns ...Func[T, T]) Func[T, T] {
    tracer := otel.Tracer("functional")
    
    return func(ctx context.Context, input T) (T, error) {
        ctx, span := tracer.Start(ctx, "compose_n",
            trace.WithAttributes(
                attribute.Int("functions.count", len(fns)),
            ),
        )
        defer span.End()
        
        current := input
        
        // 从右向左执行
        for i := len(fns) - 1; i >= 0; i-- {
            span.AddEvent("executing function", trace.WithAttributes(
                attribute.Int("function.index", i),
            ))
            
            result, err := fns[i](ctx, current)
            if err != nil {
                span.RecordError(err)
                return current, err
            }
            
            current = result
        }
        
        return current, nil
    }
}
```

---

## 柯里化与偏函数

```go
package functional

import (
    "context"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

// Curry2 二元函数柯里化
func Curry2[A, B, R any](fn func(context.Context, A, B) (R, error)) func(A) Func[B, R] {
    return func(a A) Func[B, R] {
        return func(ctx context.Context, b B) (R, error) {
            return fn(ctx, a, b)
        }
    }
}

// Curry3 三元函数柯里化
func Curry3[A, B, C, R any](fn func(context.Context, A, B, C) (R, error)) func(A) func(B) Func[C, R] {
    return func(a A) func(B) Func[C, R] {
        return func(b B) Func[C, R] {
            return func(ctx context.Context, c C) (R, error) {
                return fn(ctx, a, b, c)
            }
        }
    }
}

// Partial 偏函数应用
func Partial[A, B, R any](fn func(context.Context, A, B) (R, error), a A) Func[B, R] {
    tracer := otel.Tracer("functional")
    
    return func(ctx context.Context, b B) (R, error) {
        ctx, span := tracer.Start(ctx, "partial")
        defer span.End()
        
        return fn(ctx, a, b)
    }
}

// 使用示例
func ExampleCurrying() {
    // 定义加法函数
    add := func(ctx context.Context, a, b int) (int, error) {
        return a + b, nil
    }
    
    // 柯里化
    curriedAdd := Curry2(add)
    
    // 部分应用
    add5 := curriedAdd(5)
    
    // 使用
    ctx := context.Background()
    result, _ := add5(ctx, 3) // 结果: 8
    _ = result
}
```

---

## Monad 模式

### Result Monad

```go
package functional

import (
    "context"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// Result Monad - 封装成功或失败
type Result[T any] struct {
    value T
    err   error
}

// Ok 创建成功的 Result
func Ok[T any](value T) Result[T] {
    return Result[T]{value: value}
}

// Err 创建失败的 Result
func Err[T any](err error) Result[T] {
    return Result[T]{err: err}
}

// IsOk 检查是否成功
func (r Result[T]) IsOk() bool {
    return r.err == nil
}

// IsErr 检查是否失败
func (r Result[T]) IsErr() bool {
    return r.err != nil
}

// Unwrap 解包值（可能 panic）
func (r Result[T]) Unwrap() T {
    if r.err != nil {
        panic(r.err)
    }
    return r.value
}

// UnwrapOr 解包值或返回默认值
func (r Result[T]) UnwrapOr(defaultValue T) T {
    if r.err != nil {
        return defaultValue
    }
    return r.value
}

// Map 映射值
func (r Result[T]) Map(ctx context.Context, fn func(context.Context, T) (T, error)) Result[T] {
    tracer := otel.Tracer("functional")
    
    ctx, span := tracer.Start(ctx, "result.map")
    defer span.End()
    
    if r.err != nil {
        span.SetAttributes(attribute.Bool("has_error", true))
        return r
    }
    
    value, err := fn(ctx, r.value)
    if err != nil {
        span.RecordError(err)
        return Err[T](err)
    }
    
    return Ok(value)
}

// FlatMap 扁平化映射
func (r Result[T]) FlatMap(ctx context.Context, fn func(context.Context, T) Result[T]) Result[T] {
    tracer := otel.Tracer("functional")
    
    ctx, span := tracer.Start(ctx, "result.flatmap")
    defer span.End()
    
    if r.err != nil {
        span.SetAttributes(attribute.Bool("has_error", true))
        return r
    }
    
    return fn(ctx, r.value)
}

// AndThen 链式调用
func (r Result[T]) AndThen(ctx context.Context, fn Func[T, T]) Result[T] {
    if r.err != nil {
        return r
    }
    
    value, err := fn(ctx, r.value)
    if err != nil {
        return Err[T](err)
    }
    
    return Ok(value)
}

// OrElse 错误时执行备选方案
func (r Result[T]) OrElse(ctx context.Context, fn func(context.Context, error) Result[T]) Result[T] {
    if r.err == nil {
        return r
    }
    
    return fn(ctx, r.err)
}

// Match 模式匹配
func (r Result[T]) Match(
    ctx context.Context,
    onOk func(context.Context, T) error,
    onErr func(context.Context, error) error,
) error {
    if r.err != nil {
        return onErr(ctx, r.err)
    }
    return onOk(ctx, r.value)
}

// 使用示例
func ExampleResultMonad(ctx context.Context) {
    tracer := otel.Tracer("example")
    
    ctx, span := tracer.Start(ctx, "example.result_monad")
    defer span.End()
    
    result := Ok(10).
        Map(ctx, func(ctx context.Context, x int) (int, error) {
            return x * 2, nil
        }).
        Map(ctx, func(ctx context.Context, x int) (int, error) {
            return x + 5, nil
        }).
        AndThen(ctx, func(ctx context.Context, x int) (int, error) {
            if x > 100 {
                return 0, errors.New("too large")
            }
            return x, nil
        })
    
    finalValue := result.UnwrapOr(0)
    span.SetAttributes(
        attribute.Int("final_value", finalValue),
    )
}
```

### Option Monad

```go
package functional

// Option Monad - 封装可选值
type Option[T any] struct {
    value *T
}

// Some 创建有值的 Option
func Some[T any](value T) Option[T] {
    return Option[T]{value: &value}
}

// None 创建无值的 Option
func None[T any]() Option[T] {
    return Option[T]{value: nil}
}

// IsSome 检查是否有值
func (o Option[T]) IsSome() bool {
    return o.value != nil
}

// IsNone 检查是否无值
func (o Option[T]) IsNone() bool {
    return o.value == nil
}

// Unwrap 解包值
func (o Option[T]) Unwrap() T {
    if o.value == nil {
        panic("unwrap on None")
    }
    return *o.value
}

// UnwrapOr 解包值或返回默认值
func (o Option[T]) UnwrapOr(defaultValue T) T {
    if o.value == nil {
        return defaultValue
    }
    return *o.value
}

// Map 映射值
func MapOption[T, R any](ctx context.Context, o Option[T], fn func(context.Context, T) (R, error)) Option[R] {
    if o.value == nil {
        return None[R]()
    }
    
    result, err := fn(ctx, *o.value)
    if err != nil {
        return None[R]()
    }
    
    return Some(result)
}

// FlatMap 扁平化映射
func FlatMapOption[T, R any](ctx context.Context, o Option[T], fn func(context.Context, T) Option[R]) Option[R] {
    if o.value == nil {
        return None[R]()
    }
    
    return fn(ctx, *o.value)
}
```

---

## 函数式错误处理

```go
package functional

import (
    "context"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// Try 尝试执行函数并捕获 panic
func Try[T any](ctx context.Context, fn func(context.Context) (T, error)) (result T, err error) {
    tracer := otel.Tracer("functional")
    
    ctx, span := tracer.Start(ctx, "try")
    defer span.End()
    
    defer func() {
        if r := recover(); r != nil {
            err = fmt.Errorf("panic recovered: %v", r)
            span.RecordError(err)
            span.SetStatus(codes.Error, "panic")
        }
    }()
    
    result, err = fn(ctx)
    if err != nil {
        span.RecordError(err)
    }
    
    return
}

// Recover 错误恢复
func Recover[T any](
    ctx context.Context,
    fn Func[T, T],
    recovery func(context.Context, error) (T, error),
) Func[T, T] {
    tracer := otel.Tracer("functional")
    
    return func(ctx context.Context, input T) (T, error) {
        ctx, span := tracer.Start(ctx, "recover")
        defer span.End()
        
        result, err := fn(ctx, input)
        if err != nil {
            span.AddEvent("error occurred, attempting recovery")
            return recovery(ctx, err)
        }
        
        return result, nil
    }
}

// Fallback 失败时使用备选方案
func Fallback[T any](
    ctx context.Context,
    primary Func[T, T],
    fallback Func[T, T],
) Func[T, T] {
    tracer := otel.Tracer("functional")
    
    return func(ctx context.Context, input T) (T, error) {
        ctx, span := tracer.Start(ctx, "fallback")
        defer span.End()
        
        result, err := primary(ctx, input)
        if err == nil {
            span.SetAttributes(attribute.Bool("used_primary", true))
            return result, nil
        }
        
        span.AddEvent("primary failed, using fallback")
        span.SetAttributes(attribute.Bool("used_primary", false))
        
        return fallback(ctx, input)
    }
}
```

---

## 实战案例

### HTTP 请求处理的函数式实现

```go
package examples

import (
    "context"
    "encoding/json"
    "net/http"

    "go.opentelemetry.io/otel"
)

// Request 请求类型
type Request struct {
    UserID string
    Action string
}

// Response 响应类型
type Response struct {
    Status  string
    Message string
    Data    interface{}
}

// 函数式 HTTP 处理器
func FunctionalHTTPHandler() http.HandlerFunc {
    tracer := otel.Tracer("http-handler")
    
    // 定义处理步骤
    parseRequest := TracedFunc("parse_request", func(ctx context.Context, r *http.Request) (*Request, error) {
        var req Request
        if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
            return nil, err
        }
        return &req, nil
    })
    
    validateRequest := TracedFunc("validate_request", func(ctx context.Context, req *Request) (*Request, error) {
        if req.UserID == "" {
            return nil, errors.New("user_id required")
        }
        return req, nil
    })
    
    processRequest := TracedFunc("process_request", func(ctx context.Context, req *Request) (*Response, error) {
        // 业务逻辑
        return &Response{
            Status:  "success",
            Message: "processed",
        }, nil
    })
    
    // 组合处理流程
    handler := Compose(
        processRequest,
        Compose(validateRequest, parseRequest),
    )
    
    // 应用中间件
    enhanced := Chain(
        WithTracing[*http.Request, *Response]("http.handler"),
        WithRetry[*http.Request, *Response](3, 100*time.Millisecond),
        WithTimeout[*http.Request, *Response](5*time.Second),
    )(handler)
    
    // 返回 HTTP 处理函数
    return func(w http.ResponseWriter, r *http.Request) {
        ctx := r.Context()
        
        result, err := enhanced(ctx, r)
        if err != nil {
            http.Error(w, err.Error(), http.StatusInternalServerError)
            return
        }
        
        w.Header().Set("Content-Type", "application/json")
        json.NewEncoder(w).Encode(result)
    }
}
```

---

## 总结

本文档提供了完整的 Go 函数式编程与 OTLP 集成方案:

**核心模式**:

- ✅ 高阶函数 - 函数作为参数和返回值
- ✅ 函数组合 - Compose、Pipe、Chain
- ✅ 柯里化 - 部分函数应用
- ✅ Monad 模式 - Result、Option
- ✅ 函数式集合操作 - Map、Filter、Reduce
- ✅ 中间件模式 - 可组合的功能增强

**最佳实践**:

- ✅ 泛型提升类型安全
- ✅ Context 传播追踪信息
- ✅ 不可变数据结构
- ✅ 纯函数优先

**相关文档**:

- [Go泛型与OTLP类型安全集成](./23_Go泛型与OTLP类型安全集成.md)
- [Go高级并发模式与OTLP完整集成](./31_Go高级并发模式与OTLP完整集成.md)
- [Go错误处理与OTLP集成](./13_Go错误处理与OTLP集成.md)

---

**最后更新**: 2025年10月10日  
**维护者**: OTLP Go 集成项目组
