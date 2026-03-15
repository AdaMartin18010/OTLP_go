// Package main shows anti-patterns that should be avoided in Go programming.
//
// These are common mistakes and bad practices with explanations of why
// they are problematic and how to fix them.
package main

import (
	"context"
	"errors"
	"fmt"
	"os"
)

// ============================================================================
// Anti-pattern 1: Bad Error Handling
// ============================================================================

// BadErrorHandling demonstrates wrong error handling
func BadErrorHandling() error {
	err := doSomething()
	if err != nil {
		// BAD: Losing original error information
		return errors.New("something failed")
	}
	return nil
}

// GoodErrorHandling demonstrates proper error handling
func GoodErrorHandling() error {
	err := doSomething()
	if err != nil {
		// GOOD: Wrapping error preserves context
		return fmt.Errorf("doing something: %w", err)
	}
	return nil
}

// ============================================================================
// Anti-pattern 2: Resource Leak
// ============================================================================

// BadResourceManagement demonstrates wrong resource management
func BadResourceManagement() {
	// BAD: Forgetting to close file
	f, _ := os.Open("file.txt")
	// Process file...
	// Forgot to call f.Close()
	_ = f
}

// GoodResourceManagement demonstrates proper resource management
func GoodResourceManagement() error {
	// GOOD: Using defer to ensure closure
	f, err := os.Open("file.txt")
	if err != nil {
		return err
	}
	defer f.Close()
	// Process file...
	return nil
}

// ============================================================================
// Anti-pattern 3: Wrong Defer Usage
// ============================================================================

// BadDeferInLoop demonstrates wrong defer usage in loop
func BadDeferInLoop() {
	// BAD: Defer in loop accumulates
	for i := 0; i < 1000; i++ {
		f, _ := os.Open(fmt.Sprintf("file%d.txt", i))
		defer f.Close() // Accumulates 1000 deferred calls!
		_ = f
	}
}

// GoodDeferInLoop demonstrates proper resource handling in loop
func GoodDeferInLoop() {
	// GOOD: Using function wrapper
	for i := 0; i < 1000; i++ {
		func() {
			f, err := os.Open(fmt.Sprintf("file%d.txt", i))
			if err != nil {
				return
			}
			defer f.Close()
			// Process file...
		}()
	}
}

// ============================================================================
// Anti-pattern 4: Context Misuse
// ============================================================================

// BadContextUsage demonstrates wrong context usage
func BadContextUsage() {
	// BAD: Not cancelling context
	ctx, _ := context.WithTimeout(context.Background(), 0)
	// Use ctx...
	// Forgot to call cancel causes goroutine leak
	_ = ctx
}

// GoodContextUsage demonstrates proper context usage
func GoodContextUsage() {
	// GOOD: Using defer to cancel
	ctx, cancel := context.WithTimeout(context.Background(), 0)
	defer cancel()
	// Use ctx...
	_ = ctx
}

// ============================================================================
// Anti-pattern 5: Slice Allocation
// ============================================================================

// BadSliceAllocation demonstrates wrong slice allocation
func BadSliceAllocation(n int) []int {
	// BAD: Not preallocating capacity
	var result []int
	for i := 0; i < n; i++ {
		result = append(result, i)
	}
	return result
}

// GoodSliceAllocation demonstrates proper slice allocation
func GoodSliceAllocation(n int) []int {
	// GOOD: Preallocating capacity
	result := make([]int, 0, n)
	for i := 0; i < n; i++ {
		result = append(result, i)
	}
	return result
}

// ============================================================================
// Helper Functions
// ============================================================================

func doSomething() error {
	return nil
}

// ============================================================================
// Main Function
// ============================================================================

func main() {
	fmt.Println("Anti-pattern Examples")
	fmt.Println("These codes demonstrate patterns that should be avoided")
	fmt.Println("Please refer to BEST_PRACTICES.md for correct approaches")
}