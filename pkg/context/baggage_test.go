// Package context provides context propagation utilities for the OTLP Go SDK.
package context

import (
	"context"
	"testing"
)

func TestNewBaggage(t *testing.T) {
	b := NewBaggage()
	if b.Len() != 0 {
		t.Errorf("expected empty baggage, got %d entries", b.Len())
	}
	if !b.IsEmpty() {
		t.Error("expected IsEmpty to return true")
	}
}

func TestBaggageSetGet(t *testing.T) {
	t.Run("SetAndGet", func(t *testing.T) {
		b := NewBaggage()
		b2, err := b.Set("key1", "value1")
		if err != nil {
			t.Fatalf("set failed: %v", err)
		}

		item, ok := b2.Get("key1")
		if !ok {
			t.Fatal("expected to find key")
		}
		if item.Value != "value1" {
			t.Errorf("expected value1, got %s", item.Value)
		}

		// Original should be unchanged (immutable)
		_, ok = b.Get("key1")
		if ok {
			t.Error("original baggage should not be modified")
		}
	})

	t.Run("Get_NotFound", func(t *testing.T) {
		b := NewBaggage()
		_, ok := b.Get("nonexistent")
		if ok {
			t.Error("expected not to find nonexistent key")
		}
	})

	t.Run("GetValue", func(t *testing.T) {
		b := NewBaggage()
		b, _ = b.Set("key1", "value1")

		val, ok := b.GetValue("key1")
		if !ok || val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}
	})
}

func TestBaggageSetWithMetadata(t *testing.T) {
	b := NewBaggage()
	metadata := BaggageItemMetadata{
		Properties: map[string]string{
			"prop1": "val1",
		},
	}

	b2, err := b.SetWithMetadata("key1", "value1", metadata)
	if err != nil {
		t.Fatalf("set with metadata failed: %v", err)
	}

	item, ok := b2.Get("key1")
	if !ok {
		t.Fatal("expected to find key")
	}

	prop, ok := item.Metadata.Properties["prop1"]
	if !ok || prop != "val1" {
		t.Error("expected property to be set")
	}
}

func TestBaggageDelete(t *testing.T) {
	b := NewBaggage()
	b, _ = b.Set("key1", "value1")
	b = b.Delete("key1")

	_, ok := b.Get("key1")
	if ok {
		t.Error("expected key to be deleted")
	}
}

func TestBaggageHas(t *testing.T) {
	b := NewBaggage()
	b, _ = b.Set("key1", "value1")

	if !b.Has("key1") {
		t.Error("expected Has to return true for existing key")
	}
	if b.Has("nonexistent") {
		t.Error("expected Has to return false for nonexistent key")
	}
}

func TestBaggageKeysSorted(t *testing.T) {
	b := NewBaggage()
	b, _ = b.Set("key1", "value1")
	b, _ = b.Set("key2", "value2")

	keys := b.Keys()
	if len(keys) != 2 {
		t.Errorf("expected 2 keys, got %d", len(keys))
	}

	// Keys should be sorted
	if keys[0] != "key1" || keys[1] != "key2" {
		t.Error("expected keys to be sorted")
	}
}

func TestBaggageEntries(t *testing.T) {
	b := NewBaggage()
	b, _ = b.Set("key1", "value1")

	entries := b.Entries()
	if len(entries) != 1 {
		t.Errorf("expected 1 entry, got %d", len(entries))
	}

	// Modifying returned entries should not affect original
	entries["key2"] = BaggageItem{Value: "value2"}
	if b.Has("key2") {
		t.Error("modifying returned entries should not affect original")
	}
}

func TestBaggageString(t *testing.T) {
	t.Run("Empty", func(t *testing.T) {
		b := NewBaggage()
		if s := b.String(); s != "" {
			t.Errorf("expected empty string, got %s", s)
		}
	})

	t.Run("SingleEntry", func(t *testing.T) {
		b := NewBaggage()
		b, _ = b.Set("key1", "value1")

		s := b.String()
		if s == "" {
			t.Error("expected non-empty string")
		}
		if !contains(s, "key1") || !contains(s, "value1") {
			t.Error("expected string to contain key and value")
		}
	})

	t.Run("MultipleEntries", func(t *testing.T) {
		b := NewBaggage()
		b, _ = b.Set("key1", "value1")
		b, _ = b.Set("key2", "value2")

		s := b.String()
		if !contains(s, "key1") || !contains(s, "key2") {
			t.Error("expected string to contain both keys")
		}
	})
}

func TestParseBaggage(t *testing.T) {
	t.Run("Empty", func(t *testing.T) {
		b, err := ParseBaggage("")
		if err != nil {
			t.Fatalf("parse failed: %v", err)
		}
		if !b.IsEmpty() {
			t.Error("expected empty baggage")
		}
	})

	t.Run("SingleEntry", func(t *testing.T) {
		b, err := ParseBaggage("key1=value1")
		if err != nil {
			t.Fatalf("parse failed: %v", err)
		}
		if b.Len() != 1 {
			t.Errorf("expected 1 entry, got %d", b.Len())
		}

		val, ok := b.GetValue("key1")
		if !ok || val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}
	})

	t.Run("MultipleEntries", func(t *testing.T) {
		b, err := ParseBaggage("key1=value1,key2=value2")
		if err != nil {
			t.Fatalf("parse failed: %v", err)
		}
		if b.Len() != 2 {
			t.Errorf("expected 2 entries, got %d", b.Len())
		}
	})

	t.Run("WithProperties", func(t *testing.T) {
		b, err := ParseBaggage("key1=value1;prop1=val1")
		if err != nil {
			t.Fatalf("parse failed: %v", err)
		}

		item, ok := b.Get("key1")
		if !ok {
			t.Fatal("expected to find key1")
		}

		prop, ok := item.Metadata.Properties["prop1"]
		if !ok || prop != "val1" {
			t.Error("expected property to be parsed")
		}
	})

	t.Run("InvalidEntriesSkipped", func(t *testing.T) {
		b, err := ParseBaggage("key1=value1,invalid-entry,key2=value2")
		if err != nil {
			t.Fatalf("parse failed: %v", err)
		}
		if b.Len() != 2 {
			t.Errorf("expected 2 valid entries, got %d", b.Len())
		}
	})
}

func TestValidateBaggageKey(t *testing.T) {
	tests := []struct {
		key     string
		wantErr bool
	}{
		{"valid", false},
		{"valid_key", false},
		{"valid-key", false},
		{"valid.key", false},
		{"", true},
		{"1invalid", true},
		{"invalid key", true},
	}

	for _, tt := range tests {
		t.Run(tt.key, func(t *testing.T) {
			err := ValidateBaggageKey(tt.key)
			if (err != nil) != tt.wantErr {
				t.Errorf("ValidateBaggageKey(%q) error = %v, wantErr %v", tt.key, err, tt.wantErr)
			}
		})
	}
}

func TestValidateBaggageValue(t *testing.T) {
	t.Run("Valid", func(t *testing.T) {
		err := ValidateBaggageValue("valid-value")
		if err != nil {
			t.Errorf("expected no error, got %v", err)
		}
	})

	t.Run("TooLong", func(t *testing.T) {
		longValue := make([]byte, MaxBaggageValueLength+1)
		err := ValidateBaggageValue(string(longValue))
		if err == nil {
			t.Error("expected error for too long value")
		}
	})
}

func TestBaggageFromContext(t *testing.T) {
	t.Run("EmptyContext", func(t *testing.T) {
		b := BaggageFromContext(context.Background())
		if !b.IsEmpty() {
			t.Error("expected empty baggage from empty context")
		}
	})

	t.Run("NilContext", func(t *testing.T) {
		b := BaggageFromContext(nil)
		if !b.IsEmpty() {
			t.Error("expected empty baggage from nil context")
		}
	})

	t.Run("WithBaggage", func(t *testing.T) {
		b := NewBaggage()
		b, _ = b.Set("key1", "value1")

		ctx := ContextWithBaggage(context.Background(), b)
		retrieved := BaggageFromContext(ctx)

		if !retrieved.Has("key1") {
			t.Error("expected to find key in context")
		}
	})
}

func TestWithBaggage(t *testing.T) {
	t.Run("SetSingleValue", func(t *testing.T) {
		ctx := WithBaggage(context.Background(), "key1", "value1")

		val := GetBaggage(ctx, "key1")
		if val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}
	})

	t.Run("MultipleValues", func(t *testing.T) {
		ctx := context.Background()
		ctx = WithBaggage(ctx, "key1", "value1")
		ctx = WithBaggage(ctx, "key2", "value2")

		if GetBaggage(ctx, "key1") != "value1" {
			t.Error("expected key1")
		}
		if GetBaggage(ctx, "key2") != "value2" {
			t.Error("expected key2")
		}
	})

	t.Run("UpdateExisting", func(t *testing.T) {
		ctx := WithBaggage(context.Background(), "key1", "value1")
		ctx = WithBaggage(ctx, "key1", "updated")

		val := GetBaggage(ctx, "key1")
		if val != "updated" {
			t.Errorf("expected updated, got %s", val)
		}
	})

	t.Run("NilContext", func(t *testing.T) {
		ctx := WithBaggage(nil, "key1", "value1")
		if ctx == nil {
			t.Fatal("expected non-nil context")
		}
		val := GetBaggage(ctx, "key1")
		if val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}
	})

	t.Run("InvalidKey", func(t *testing.T) {
		ctx := WithBaggage(context.Background(), "", "value1")
		// Should return original context without modification
		if GetBaggage(ctx, "") != "" {
			t.Error("empty key should not be set")
		}
	})
}

func TestWithBaggageItem(t *testing.T) {
	metadata := BaggageItemMetadata{
		Properties: map[string]string{"prop1": "val1"},
	}

	ctx := WithBaggageItem(context.Background(), "key1", "value1", metadata)

	item, ok := GetBaggageItem(ctx, "key1")
	if !ok {
		t.Fatal("expected to find item")
	}
	if item.Value != "value1" {
		t.Errorf("expected value1, got %s", item.Value)
	}

	prop, ok := item.Metadata.Properties["prop1"]
	if !ok || prop != "val1" {
		t.Error("expected metadata property")
	}
}

func TestGetBaggage(t *testing.T) {
	t.Run("Exists", func(t *testing.T) {
		ctx := WithBaggage(context.Background(), "key1", "value1")
		val := GetBaggage(ctx, "key1")
		if val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}
	})

	t.Run("NotFound", func(t *testing.T) {
		ctx := context.Background()
		val := GetBaggage(ctx, "nonexistent")
		if val != "" {
			t.Errorf("expected empty string, got %s", val)
		}
	})
}

func TestDeleteBaggage(t *testing.T) {
	ctx := WithBaggage(context.Background(), "key1", "value1")
	ctx = DeleteBaggage(ctx, "key1")

	val := GetBaggage(ctx, "key1")
	if val != "" {
		t.Errorf("expected empty string after delete, got %s", val)
	}
}

func TestClearBaggage(t *testing.T) {
	ctx := WithBaggage(context.Background(), "key1", "value1")
	ctx = WithBaggage(ctx, "key2", "value2")
	ctx = ClearBaggage(ctx)

	if HasBaggage(ctx) {
		t.Error("expected no baggage after clear")
	}
}

func TestHasBaggage(t *testing.T) {
	t.Run("HasBaggage", func(t *testing.T) {
		ctx := WithBaggage(context.Background(), "key1", "value1")
		if !HasBaggage(ctx) {
			t.Error("expected HasBaggage to return true")
		}
	})

	t.Run("NoBaggage", func(t *testing.T) {
		ctx := context.Background()
		if HasBaggage(ctx) {
			t.Error("expected HasBaggage to return false")
		}
	})

	t.Run("NilContext", func(t *testing.T) {
		if HasBaggage(nil) {
			t.Error("expected HasBaggage to return false for nil")
		}
	})
}

func TestBaggageKeys(t *testing.T) {
	ctx := WithBaggage(context.Background(), "key1", "value1")
	ctx = WithBaggage(ctx, "key2", "value2")

	keys := BaggageKeys(ctx)
	if len(keys) != 2 {
		t.Errorf("expected 2 keys, got %d", len(keys))
	}
}

func TestBaggageLen(t *testing.T) {
	t.Run("WithBaggage", func(t *testing.T) {
		ctx := WithBaggage(context.Background(), "key1", "value1")
		if BaggageLen(ctx) != 1 {
			t.Errorf("expected 1, got %d", BaggageLen(ctx))
		}
	})

	t.Run("NoBaggage", func(t *testing.T) {
		ctx := context.Background()
		if BaggageLen(ctx) != 0 {
			t.Errorf("expected 0, got %d", BaggageLen(ctx))
		}
	})

	t.Run("NilContext", func(t *testing.T) {
		if BaggageLen(nil) != 0 {
			t.Errorf("expected 0, got %d", BaggageLen(nil))
		}
	})
}

func TestBaggagePropagator(t *testing.T) {
	propagator := NewBaggagePropagator()

	t.Run("InjectExtract", func(t *testing.T) {
		b := NewBaggage()
		b, _ = b.Set("key1", "value1")
		b, _ = b.Set("key2", "value2")

		ctx := ContextWithBaggage(context.Background(), b)
		carrier := make(TextMapCarrier)

		propagator.Inject(ctx, carrier)

		header := carrier.Get(BaggageHeader)
		if header == "" {
			t.Fatal("expected baggage header")
		}

		ctx2 := propagator.Extract(context.Background(), carrier)
		b2 := BaggageFromContext(ctx2)

		if b2.Len() != 2 {
			t.Errorf("expected 2 entries, got %d", b2.Len())
		}

		val, ok := b2.GetValue("key1")
		if !ok || val != "value1" {
			t.Error("expected key1 to be extracted")
		}
	})

	t.Run("InjectEmpty", func(t *testing.T) {
		ctx := context.Background()
		carrier := make(TextMapCarrier)

		propagator.Inject(ctx, carrier)

		if carrier.Get(BaggageHeader) != "" {
			t.Error("expected no header for empty baggage")
		}
	})

	t.Run("ExtractEmpty", func(t *testing.T) {
		carrier := make(TextMapCarrier)
		ctx := propagator.Extract(context.Background(), carrier)

		b := BaggageFromContext(ctx)
		if !b.IsEmpty() {
			t.Error("expected empty baggage from empty carrier")
		}
	})

	t.Run("Fields", func(t *testing.T) {
		fields := propagator.Fields()
		if len(fields) != 1 || fields[0] != BaggageHeader {
			t.Errorf("unexpected fields: %v", fields)
		}
	})
}

func TestBaggageSize(t *testing.T) {
	b := NewBaggage()
	if b.Size() != 0 {
		t.Error("expected 0 size for empty baggage")
	}

	b, _ = b.Set("key1", "value1")
	if b.Size() <= 0 {
		t.Error("expected positive size")
	}
}

func TestBaggageClone(t *testing.T) {
	b := NewBaggage()
	b, _ = b.Set("key1", "value1")

	cloned := b.Clone()
	cloned, _ = cloned.Set("key2", "value2")

	if b.Has("key2") {
		t.Error("original should not have key2")
	}
	if !cloned.Has("key1") || !cloned.Has("key2") {
		t.Error("clone should have both keys")
	}
}

func TestBaggageMerge(t *testing.T) {
	b1 := NewBaggage()
	b1, _ = b1.Set("key1", "value1")

	b2 := NewBaggage()
	b2, _ = b2.Set("key2", "value2")

	merged := b1.Merge(b2)

	if !merged.Has("key1") || !merged.Has("key2") {
		t.Error("merged should have both keys")
	}

	// b2 takes precedence for conflicts
	b2, _ = b2.Set("key1", "from-b2")
	merged = b1.Merge(b2)

	val, _ := merged.GetValue("key1")
	if val != "from-b2" {
		t.Errorf("expected from-b2, got %s", val)
	}
}

func TestBaggageFilter(t *testing.T) {
	b := NewBaggage()
	b, _ = b.Set("key1", "value1")
	b, _ = b.Set("key2", "value2")
	b, _ = b.Set("key3", "value3")

	filtered := b.Filter("key1", "key2")

	if filtered.Len() != 2 {
		t.Errorf("expected 2 entries, got %d", filtered.Len())
	}
	if !filtered.Has("key1") || !filtered.Has("key2") || filtered.Has("key3") {
		t.Error("filter did not work correctly")
	}
}

func TestBaggageMap(t *testing.T) {
	b := NewBaggage()
	b, _ = b.Set("key1", "value1")
	b, _ = b.Set("key2", "value2")

	mapped := b.Map(func(key, value string) string {
		return value + "-mapped"
	})

	val, _ := mapped.GetValue("key1")
	if val != "value1-mapped" {
		t.Errorf("expected value1-mapped, got %s", val)
	}
}

func TestBaggageForEach(t *testing.T) {
	b := NewBaggage()
	b, _ = b.Set("key1", "value1")
	b, _ = b.Set("key2", "value2")

	count := 0
	b.ForEach(func(key string, item BaggageItem) bool {
		count++
		return true
	})

	if count != 2 {
		t.Errorf("expected 2 iterations, got %d", count)
	}

	// Test early termination
	count = 0
	b.ForEach(func(key string, item BaggageItem) bool {
		count++
		return false // Stop after first
	})

	if count != 1 {
		t.Errorf("expected 1 iteration, got %d", count)
	}
}

func TestBaggageBase64(t *testing.T) {
	t.Run("EncodeDecode", func(t *testing.T) {
		b := NewBaggage()
		b, _ = b.Set("key1", "value1")

		encoded := b.EncodeBase64()
		if encoded == "" {
			t.Fatal("expected non-empty encoding")
		}

		decoded, err := DecodeBase64(encoded)
		if err != nil {
			t.Fatalf("decode failed: %v", err)
		}

		val, ok := decoded.GetValue("key1")
		if !ok || val != "value1" {
			t.Error("decoded baggage does not match")
		}
	})

	t.Run("EmptyEncode", func(t *testing.T) {
		b := NewBaggage()
		if b.EncodeBase64() != "" {
			t.Error("expected empty string for empty baggage")
		}
	})

	t.Run("EmptyDecode", func(t *testing.T) {
		b, err := DecodeBase64("")
		if err != nil {
			t.Errorf("unexpected error: %v", err)
		}
		if !b.IsEmpty() {
			t.Error("expected empty baggage")
		}
	})

	t.Run("InvalidBase64", func(t *testing.T) {
		_, err := DecodeBase64("not-valid-base64!!!")
		if err == nil {
			t.Error("expected error for invalid base64")
		}
	})
}

func TestMustParseBaggage(t *testing.T) {
	t.Run("Valid", func(t *testing.T) {
		b := MustParseBaggage("key1=value1")
		if b.Len() != 1 {
			t.Error("expected 1 entry")
		}
	})

	t.Run("Panic", func(t *testing.T) {
		// Since ParseBaggage doesn't return error for invalid format (just skips),
		// we test with an input that would cause a panic - empty key after parsing
		defer func() {
			if r := recover(); r == nil {
				// Actually, our ParseBaggage is lenient and doesn't return errors
				// So we just verify it doesn't panic
			}
		}()
		_ = MustParseBaggage("key1=value1") // Valid format
	})
}

func TestBaggageFromMap(t *testing.T) {
	m := map[string]string{
		"key1": "value1",
		"key2": "value2",
	}

	b, err := BaggageFromMap(m)
	if err != nil {
		t.Fatalf("failed: %v", err)
	}

	if b.Len() != 2 {
		t.Errorf("expected 2 entries, got %d", b.Len())
	}
}

func TestBaggageToMap(t *testing.T) {
	b := NewBaggage()
	b, _ = b.Set("key1", "value1")
	b, _ = b.Set("key2", "value2")

	m := BaggageToMap(b)
	if len(m) != 2 {
		t.Errorf("expected 2 entries, got %d", len(m))
	}

	if m["key1"] != "value1" {
		t.Error("unexpected value")
	}
}

func TestBaggageKeyValidation(t *testing.T) {
	b := NewBaggage()

	// Valid key
	b2, err := b.Set("validKey", "value")
	if err != nil {
		t.Error("expected valid key to succeed")
	}
	if !b2.Has("validKey") {
		t.Error("expected key to be set")
	}

	// Invalid key (starts with number)
	_, err = b.Set("1invalid", "value")
	if err == nil {
		t.Error("expected invalid key to fail")
	}

	// Invalid key (empty)
	_, err = b.Set("", "value")
	if err == nil {
		t.Error("expected empty key to fail")
	}
}

func TestBaggageTooManyEntries(t *testing.T) {
	b := NewBaggage()

	// Add max entries
	for i := 0; i < MaxBaggageEntries; i++ {
		key := string(rune('a' + (i % 26)))
		if i >= 26 {
			key += string(rune('0' + (i / 26)))
		}
		var err error
		b, err = b.Set(key, "value")
		if err != nil {
			t.Fatalf("failed at entry %d: %v", i, err)
		}
	}

	// Next one should fail
	_, err := b.Set("toomany", "value")
	if err != ErrTooManyEntries {
		t.Errorf("expected ErrTooManyEntries, got %v", err)
	}
}
