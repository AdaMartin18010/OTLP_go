// Package context provides context propagation utilities for the OTLP Go SDK.
package context

import (
	"context"
	"testing"
	"time"
)

func TestMetadata(t *testing.T) {
	t.Run("NewMetadata", func(t *testing.T) {
		md := NewMetadata()
		if md == nil {
			t.Fatal("NewMetadata returned nil")
		}
		if md.Len() != 0 {
			t.Errorf("expected empty metadata, got %d items", md.Len())
		}
	})

	t.Run("GetSet", func(t *testing.T) {
		md := NewMetadata()
		md.Set("key1", "value1")

		val, ok := md.Get("key1")
		if !ok {
			t.Error("expected to find key1")
		}
		if val != "value1" {
			t.Errorf("expected value1, got %v", val)
		}

		_, ok = md.Get("nonexistent")
		if ok {
			t.Error("expected not to find nonexistent key")
		}
	})

	t.Run("Delete", func(t *testing.T) {
		md := NewMetadata()
		md.Set("key1", "value1")
		md.Delete("key1")

		_, ok := md.Get("key1")
		if ok {
			t.Error("expected key to be deleted")
		}
	})

	t.Run("Has", func(t *testing.T) {
		md := NewMetadata()
		md.Set("key1", "value1")

		if !md.Has("key1") {
			t.Error("expected Has to return true for existing key")
		}
		if md.Has("nonexistent") {
			t.Error("expected Has to return false for nonexistent key")
		}
	})

	t.Run("Keys", func(t *testing.T) {
		md := NewMetadata()
		md.Set("key1", "value1")
		md.Set("key2", "value2")

		keys := md.Keys()
		if len(keys) != 2 {
			t.Errorf("expected 2 keys, got %d", len(keys))
		}
	})

	t.Run("Len", func(t *testing.T) {
		md := NewMetadata()
		if md.Len() != 0 {
			t.Errorf("expected 0, got %d", md.Len())
		}

		md.Set("key1", "value1")
		if md.Len() != 1 {
			t.Errorf("expected 1, got %d", md.Len())
		}
	})

	t.Run("Clone", func(t *testing.T) {
		md := NewMetadata()
		md.Set("key1", "value1")

		cloned := md.Clone()
		cloned.Set("key2", "value2")

		// Original should not have key2
		if md.Has("key2") {
			t.Error("original metadata should not be modified")
		}

		// Clone should have both keys
		if !cloned.Has("key1") || !cloned.Has("key2") {
			t.Error("cloned metadata should have both keys")
		}
	})
}

func TestContextMetadata(t *testing.T) {
	t.Run("WithMetadata", func(t *testing.T) {
		md := NewMetadata()
		md.Set("key1", "value1")

		ctx := WithMetadata(context.Background(), md)
		retrieved := GetMetadata(ctx)

		if retrieved == nil {
			t.Fatal("expected metadata in context")
		}

		val, ok := retrieved.Get("key1")
		if !ok || val != "value1" {
			t.Errorf("expected value1, got %v", val)
		}
	})

	t.Run("WithMetadata_Nil", func(t *testing.T) {
		ctx := WithMetadata(context.Background(), nil)
		if ctx == nil {
			t.Error("expected non-nil context")
		}
	})

	t.Run("GetMetadata_Empty", func(t *testing.T) {
		ctx := context.Background()
		md := GetMetadata(ctx)
		if md != nil {
			t.Error("expected nil metadata for empty context")
		}
	})

	t.Run("GetMetadata_NilContext", func(t *testing.T) {
		md := GetMetadata(nil)
		if md != nil {
			t.Error("expected nil metadata for nil context")
		}
	})

	t.Run("GetMetadataValue", func(t *testing.T) {
		md := NewMetadata()
		md.Set("key1", "value1")
		ctx := WithMetadata(context.Background(), md)

		val, ok := GetMetadataValue(ctx, "key1")
		if !ok || val != "value1" {
			t.Errorf("expected value1, got %v", val)
		}

		_, ok = GetMetadataValue(ctx, "nonexistent")
		if ok {
			t.Error("expected not to find nonexistent key")
		}
	})

	t.Run("SetMetadataValue", func(t *testing.T) {
		ctx := context.Background()
		ctx = SetMetadataValue(ctx, "key1", "value1")

		val, ok := GetMetadataValue(ctx, "key1")
		if !ok || val != "value1" {
			t.Errorf("expected value1, got %v", val)
		}

		// Update existing value
		ctx = SetMetadataValue(ctx, "key1", "updated")
		val, ok = GetMetadataValue(ctx, "key1")
		if !ok || val != "updated" {
			t.Errorf("expected updated, got %v", val)
		}
	})
}

func TestDeadlineInfo(t *testing.T) {
	t.Run("WithDeadlineInfo", func(t *testing.T) {
		deadline := time.Now().Add(time.Hour)
		ctx := WithDeadlineInfo(context.Background(), deadline)

		info, ok := GetDeadlineInfo(ctx)
		if !ok {
			t.Fatal("expected deadline info")
		}

		if !info.Deadline.Equal(deadline) {
			t.Errorf("expected deadline %v, got %v", deadline, info.Deadline)
		}
	})

	t.Run("GetDeadlineInfo_NotFound", func(t *testing.T) {
		_, ok := GetDeadlineInfo(context.Background())
		if ok {
			t.Error("expected not to find deadline info")
		}
	})

	t.Run("GetDeadlineInfo_NilContext", func(t *testing.T) {
		_, ok := GetDeadlineInfo(nil)
		if ok {
			t.Error("expected not to find deadline info for nil context")
		}
	})
}

func TestTimeUntilDeadline(t *testing.T) {
	t.Run("WithDeadline", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(context.Background(), time.Second)
		defer cancel()

		remaining := TimeUntilDeadline(ctx)
		if remaining <= 0 || remaining > time.Second {
			t.Errorf("expected remaining between 0 and 1s, got %v", remaining)
		}
	})

	t.Run("NoDeadline", func(t *testing.T) {
		ctx := context.Background()
		remaining := TimeUntilDeadline(ctx)
		if remaining != 0 {
			t.Errorf("expected 0, got %v", remaining)
		}
	})

	t.Run("ExpiredDeadline", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(context.Background(), time.Millisecond)
		cancel()                          // Immediately cancel
		time.Sleep(10 * time.Millisecond) // Ensure deadline passed

		remaining := TimeUntilDeadline(ctx)
		if remaining != 0 {
			t.Errorf("expected 0 for expired deadline, got %v", remaining)
		}
	})
}

func TestIsDeadlineSet(t *testing.T) {
	t.Run("WithDeadline", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(context.Background(), time.Second)
		defer cancel()

		if !IsDeadlineSet(ctx) {
			t.Error("expected deadline to be set")
		}
	})

	t.Run("NoDeadline", func(t *testing.T) {
		ctx := context.Background()
		if IsDeadlineSet(ctx) {
			t.Error("expected no deadline")
		}
	})
}

func TestWithTimeoutExtended(t *testing.T) {
	ctx, cancel := WithTimeoutExtended(context.Background(), time.Second)
	defer cancel()

	deadline, ok := ctx.Deadline()
	if !ok {
		t.Error("expected deadline to be set")
	}

	expectedDeadline := time.Now().Add(time.Second)
	if deadline.Sub(expectedDeadline) > 100*time.Millisecond {
		t.Errorf("deadline too far from expected: %v", deadline.Sub(expectedDeadline))
	}
}

func TestWithTimeoutFromParent(t *testing.T) {
	t.Run("ShorterThanParent", func(t *testing.T) {
		parent, cancel := context.WithTimeout(context.Background(), time.Hour)
		defer cancel()

		ctx, cancel2 := WithTimeoutFromParent(parent, time.Second)
		defer cancel2()

		deadline, _ := ctx.Deadline()
		parentDeadline, _ := parent.Deadline()

		if deadline.After(parentDeadline) {
			t.Error("child deadline should not be after parent")
		}
	})

	t.Run("LongerThanParent", func(t *testing.T) {
		parent, cancel := context.WithTimeout(context.Background(), time.Second)
		defer cancel()

		ctx, cancel2 := WithTimeoutFromParent(parent, time.Hour)
		defer cancel2()

		deadline, _ := ctx.Deadline()
		parentDeadline, _ := parent.Deadline()

		if deadline.After(parentDeadline) {
			t.Error("child deadline should be capped at parent deadline")
		}
	})
}

func TestDetach(t *testing.T) {
	t.Run("PreservesValues", func(t *testing.T) {
		type key string
		k := key("test-key")

		ctx := context.WithValue(context.Background(), k, "test-value")
		detached := Detach(ctx)

		val := detached.Value(k)
		if val != "test-value" {
			t.Errorf("expected test-value, got %v", val)
		}
	})

	t.Run("IndependentCancellation", func(t *testing.T) {
		parent, cancel := context.WithCancel(context.Background())
		detached := Detach(parent)

		cancel() // Cancel parent

		// Detached context should not be cancelled
		select {
		case <-detached.Done():
			t.Error("detached context should not be cancelled")
		default:
			// Expected
		}
	})
}

func TestTextMapCarrier(t *testing.T) {
	t.Run("GetSet", func(t *testing.T) {
		carrier := make(TextMapCarrier)
		carrier.Set("key1", "value1")

		val := carrier.Get("key1")
		if val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}

		val = carrier.Get("nonexistent")
		if val != "" {
			t.Errorf("expected empty string, got %s", val)
		}
	})

	t.Run("Keys", func(t *testing.T) {
		carrier := make(TextMapCarrier)
		carrier.Set("key1", "value1")
		carrier.Set("key2", "value2")

		keys := carrier.Keys()
		if len(keys) != 2 {
			t.Errorf("expected 2 keys, got %d", len(keys))
		}
	})

	t.Run("NilCarrier", func(t *testing.T) {
		var carrier TextMapCarrier

		carrier.Set("key", "value") // Should not panic
		val := carrier.Get("key")
		if val != "" {
			t.Errorf("expected empty string from nil carrier, got %s", val)
		}

		keys := carrier.Keys()
		if keys != nil {
			t.Error("expected nil keys from nil carrier")
		}
	})
}

func TestHTTPHeadersCarrier(t *testing.T) {
	t.Run("GetSet", func(t *testing.T) {
		carrier := make(HTTPHeadersCarrier)
		carrier.Set("X-Custom-Header", "value1")

		val := carrier.Get("X-Custom-Header")
		if val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}
	})

	t.Run("AddAndValues", func(t *testing.T) {
		carrier := make(HTTPHeadersCarrier)
		carrier.Add("X-Custom-Header", "value1")
		carrier.Add("X-Custom-Header", "value2")

		values := carrier.Values("X-Custom-Header")
		if len(values) != 2 {
			t.Errorf("expected 2 values, got %d", len(values))
		}
	})

	t.Run("GetFirstValue", func(t *testing.T) {
		carrier := make(HTTPHeadersCarrier)
		carrier.Add("X-Custom-Header", "first")
		carrier.Add("X-Custom-Header", "second")

		val := carrier.Get("X-Custom-Header")
		if val != "first" {
			t.Errorf("expected first value, got %s", val)
		}
	})
}

func TestGRPCMetadataCarrier(t *testing.T) {
	t.Run("GetSet", func(t *testing.T) {
		carrier := make(GRPCMetadataCarrier)
		carrier.Set("grpc-metadata", "value1")

		val := carrier.Get("grpc-metadata")
		if val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}
	})

	t.Run("Append", func(t *testing.T) {
		carrier := make(GRPCMetadataCarrier)
		carrier.Append("grpc-metadata", "value1")
		carrier.Append("grpc-metadata", "value2")

		// Get returns first value
		val := carrier.Get("grpc-metadata")
		if val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}
	})
}

func TestCompositeCarrier(t *testing.T) {
	t.Run("GetFromFirst", func(t *testing.T) {
		carrier1 := make(TextMapCarrier)
		carrier1.Set("key1", "value1")

		carrier2 := make(TextMapCarrier)
		carrier2.Set("key2", "value2")

		composite := NewCompositeCarrier(carrier1, carrier2)

		val := composite.Get("key1")
		if val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}
	})

	t.Run("SetToAll", func(t *testing.T) {
		carrier1 := make(TextMapCarrier)
		carrier2 := make(TextMapCarrier)

		composite := NewCompositeCarrier(carrier1, carrier2)
		composite.Set("key1", "value1")

		if carrier1.Get("key1") != "value1" {
			t.Error("expected value1 in carrier1")
		}
		if carrier2.Get("key1") != "value1" {
			t.Error("expected value1 in carrier2")
		}
	})

	t.Run("Keys", func(t *testing.T) {
		carrier1 := make(TextMapCarrier)
		carrier1.Set("key1", "value1")

		carrier2 := make(TextMapCarrier)
		carrier2.Set("key2", "value2")

		composite := NewCompositeCarrier(carrier1, carrier2)
		keys := composite.Keys()

		if len(keys) != 2 {
			t.Errorf("expected 2 keys, got %d", len(keys))
		}
	})
}

func TestCompositePropagator(t *testing.T) {
	t.Run("InjectAndExtract", func(t *testing.T) {
		propagator1 := NewTraceContextPropagator()
		propagator2 := NewBaggagePropagator()

		composite := NewCompositePropagator(propagator1, propagator2)

		// Test Fields
		fields := composite.Fields()
		if len(fields) == 0 {
			t.Error("expected non-empty fields")
		}
	})

	t.Run("WithNilPropagator", func(t *testing.T) {
		composite := NewCompositePropagator(nil, NewTraceContextPropagator())

		ctx := context.Background()
		carrier := make(TextMapCarrier)

		// Should not panic
		composite.Inject(ctx, carrier)
		ctx = composite.Extract(ctx, carrier)

		if ctx == nil {
			t.Error("expected non-nil context")
		}
	})
}

func TestNoopPropagator(t *testing.T) {
	propagator := NoopPropagatorInstance

	ctx := context.Background()
	carrier := make(TextMapCarrier)

	// Inject should not panic
	propagator.Inject(ctx, carrier)

	// Extract should return same context
	result := propagator.Extract(ctx, carrier)
	if result != ctx {
		t.Error("expected same context from noop propagator")
	}

	// Fields should be nil
	if propagator.Fields() != nil {
		t.Error("expected nil fields from noop propagator")
	}
}

func TestSafeContext(t *testing.T) {
	t.Run("NewSafeContext", func(t *testing.T) {
		ctx := NewSafeContext(context.Background())
		if ctx == nil {
			t.Fatal("expected non-nil SafeContext")
		}
		if ctx.Context() == nil {
			t.Error("expected non-nil underlying context")
		}
	})

	t.Run("NewSafeContext_Nil", func(t *testing.T) {
		ctx := NewSafeContext(nil)
		if ctx == nil {
			t.Fatal("expected non-nil SafeContext")
		}
		if ctx.Context() == nil {
			t.Error("expected background context when nil provided")
		}
	})

	t.Run("WithCancel", func(t *testing.T) {
		ctx := NewSafeContext(context.Background())
		ctx2, cancel := ctx.WithCancel()
		defer cancel()

		if ctx2 == nil {
			t.Error("expected non-nil context from WithCancel")
		}
	})

	t.Run("WithTimeout", func(t *testing.T) {
		ctx := NewSafeContext(context.Background())
		ctx2, cancel := ctx.WithTimeout(time.Second)
		defer cancel()

		if ctx2 == nil {
			t.Error("expected non-nil context from WithTimeout")
		}
	})

	t.Run("WithValue", func(t *testing.T) {
		ctx := NewSafeContext(context.Background())
		ctx2 := ctx.WithValue("key", "value")

		val := ctx2.Value("key")
		if val != "value" {
			t.Errorf("expected value, got %v", val)
		}
	})

	t.Run("NilContextMethods", func(t *testing.T) {
		// Create a SafeContext with nil, then simulate nil context
		safe := &SafeContext{ctx: nil}

		if safe.Value("key") != nil {
			t.Error("expected nil from Value on nil context")
		}

		_, ok := safe.Deadline()
		if ok {
			t.Error("expected no deadline from nil context")
		}

		err := safe.Err()
		if err != context.Canceled {
			t.Errorf("expected Canceled error, got %v", err)
		}
	})
}
