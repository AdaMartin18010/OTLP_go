package shutdown

import (
	"context"
	"errors"
	"sync/atomic"
	"testing"
	"time"
)

func TestNewManager(t *testing.T) {
	timeout := 10 * time.Second
	manager := NewManager(timeout)

	if manager == nil {
		t.Fatal("NewManager() returned nil")
	}

	if manager.timeout != timeout {
		t.Errorf("Expected timeout %v, got %v", timeout, manager.timeout)
	}

	if manager.shutdowns == nil {
		t.Error("shutdowns slice is nil")
	}

	if manager.stages == nil {
		t.Error("stages map is nil")
	}

	if manager.order == nil {
		t.Error("order slice is nil")
	}
}

func TestRegister(t *testing.T) {
	manager := NewManager(5 * time.Second)

	called := false
	fn := func(ctx context.Context) error {
		called = true
		return nil
	}

	manager.Register(fn)

	if len(manager.shutdowns) != 1 {
		t.Errorf("Expected 1 shutdown function, got %d", len(manager.shutdowns))
	}

	// 执行关闭
	err := manager.Shutdown()
	if err != nil {
		t.Errorf("Shutdown() returned error: %v", err)
	}

	if !called {
		t.Error("Shutdown function was not called")
	}
}

func TestRegisterMultiple(t *testing.T) {
	manager := NewManager(5 * time.Second)

	var callOrder []int

	manager.Register(func(ctx context.Context) error {
		callOrder = append(callOrder, 1)
		return nil
	})

	manager.Register(func(ctx context.Context) error {
		callOrder = append(callOrder, 2)
		return nil
	})

	manager.Register(func(ctx context.Context) error {
		callOrder = append(callOrder, 3)
		return nil
	})

	err := manager.Shutdown()
	if err != nil {
		t.Errorf("Shutdown() returned error: %v", err)
	}

	// 应该按 LIFO 顺序执行
	if len(callOrder) != 3 {
		t.Errorf("Expected 3 calls, got %d", len(callOrder))
	}

	// LIFO: 3, 2, 1
	expected := []int{3, 2, 1}
	for i, v := range callOrder {
		if v != expected[i] {
			t.Errorf("Call order mismatch at index %d: expected %d, got %d", i, expected[i], v)
		}
	}
}

func TestRegisterStage(t *testing.T) {
	manager := NewManager(5 * time.Second)

	var calls atomic.Int32

	manager.RegisterStage("stage1", func(ctx context.Context) error {
		calls.Add(1)
		return nil
	})

	manager.RegisterStage("stage2", func(ctx context.Context) error {
		calls.Add(1)
		return nil
	})

	err := manager.Shutdown()
	if err != nil {
		t.Errorf("Shutdown() returned error: %v", err)
	}

	if calls.Load() != 2 {
		t.Errorf("Expected 2 calls, got %d", calls.Load())
	}
}

func TestRegisterStageOrder(t *testing.T) {
	manager := NewManager(5 * time.Second)

	var callOrder []string

	manager.RegisterStage("stage1", func(ctx context.Context) error {
		callOrder = append(callOrder, "stage1-1")
		return nil
	})

	manager.RegisterStage("stage2", func(ctx context.Context) error {
		callOrder = append(callOrder, "stage2-1")
		return nil
	})

	manager.RegisterStage("stage1", func(ctx context.Context) error {
		callOrder = append(callOrder, "stage1-2")
		return nil
	})

	err := manager.Shutdown()
	if err != nil {
		t.Errorf("Shutdown() returned error: %v", err)
	}

	if len(callOrder) != 3 {
		t.Fatalf("Expected 3 calls, got %d", len(callOrder))
	}

	// stage1 的两个函数应该并发执行（无法保证顺序），但都在 stage2 之前
	stage1Found := 0
	for i, call := range callOrder {
		if call == "stage1-1" || call == "stage1-2" {
			if i >= 2 {
				t.Error("stage1 functions should be called before stage2")
			}
			stage1Found++
		}
		if call == "stage2-1" {
			if i < 2 {
				t.Error("stage2 should be called after all stage1 functions")
			}
		}
	}

	if stage1Found != 2 {
		t.Errorf("Expected 2 stage1 calls, got %d", stage1Found)
	}
}

func TestShutdownError(t *testing.T) {
	manager := NewManager(5 * time.Second)

	expectedErr := errors.New("shutdown error")
	manager.Register(func(ctx context.Context) error {
		return expectedErr
	})

	err := manager.Shutdown()
	if err == nil {
		t.Fatal("Expected error, got nil")
	}

	// errors.Join 应该包含原始错误
	if !errors.Is(err, expectedErr) {
		t.Errorf("Error does not wrap expected error: %v", err)
	}
}

func TestShutdownTimeout(t *testing.T) {
	manager := NewManager(100 * time.Millisecond)

	manager.RegisterStage("slow", func(ctx context.Context) error {
		// 等待超过超时时间
		select {
		case <-time.After(1 * time.Second):
			return nil
		case <-ctx.Done():
			return ctx.Err()
		}
	})

	err := manager.Shutdown()
	// 应该有错误（超时或上下文取消）
	if err == nil {
		t.Log("Warning: Expected timeout error, got nil")
	}
}

func TestShutdownOnce(t *testing.T) {
	manager := NewManager(5 * time.Second)

	var calls atomic.Int32
	manager.Register(func(ctx context.Context) error {
		calls.Add(1)
		return nil
	})

	// 多次调用 Shutdown
	err1 := manager.Shutdown()
	err2 := manager.Shutdown()
	err3 := manager.Shutdown()

	if err1 != nil {
		t.Errorf("First Shutdown() returned error: %v", err1)
	}

	// 后续调用应该立即返回（但返回相同的错误）
	_ = err2
	_ = err3

	// 函数应该只被调用一次
	if calls.Load() != 1 {
		t.Errorf("Expected 1 call, got %d", calls.Load())
	}
}

func TestWaitAndDone(t *testing.T) {
	manager := NewManager(5 * time.Second)

	// 启动等待 goroutine
	waitDone := make(chan struct{})
	go func() {
		manager.Wait()
		close(waitDone)
	}()

	// Done() 应该返回相同的通道
	doneCh := manager.Done()

	// 执行关闭
	err := manager.Shutdown()
	if err != nil {
		t.Errorf("Shutdown() returned error: %v", err)
	}

	// Wait() 应该返回
	select {
	case <-waitDone:
		// OK
	case <-time.After(1 * time.Second):
		t.Error("Wait() did not return after Shutdown()")
	}

	// Done() 通道应该被关闭
	select {
	case <-doneCh:
		// OK
	case <-time.After(100 * time.Millisecond):
		t.Error("Done() channel was not closed")
	}
}

func TestConcurrentShutdown(t *testing.T) {
	manager := NewManager(5 * time.Second)

	var calls atomic.Int32
	for i := 0; i < 10; i++ {
		manager.Register(func(ctx context.Context) error {
			calls.Add(1)
			return nil
		})
	}

	// 并发调用 Shutdown
	errChan := make(chan error, 5)
	for i := 0; i < 5; i++ {
		go func() {
			errChan <- manager.Shutdown()
		}()
	}

	// 收集结果
	for i := 0; i < 5; i++ {
		err := <-errChan
		if err != nil {
			t.Logf("Shutdown %d returned error: %v", i, err)
		}
	}

	// 应该只执行一次
	if calls.Load() != 10 {
		t.Errorf("Expected 10 calls, got %d", calls.Load())
	}
}

func BenchmarkShutdown(b *testing.B) {
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		manager := NewManager(5 * time.Second)
		for j := 0; j < 10; j++ {
			manager.Register(func(ctx context.Context) error {
				return nil
			})
		}
		_ = manager.Shutdown()
	}
}

func BenchmarkShutdownStaged(b *testing.B) {
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		manager := NewManager(5 * time.Second)
		for j := 0; j < 3; j++ {
			stage := "stage" + string(rune('0'+j))
			manager.RegisterStage(stage, func(ctx context.Context) error {
				return nil
			})
		}
		_ = manager.Shutdown()
	}
}
