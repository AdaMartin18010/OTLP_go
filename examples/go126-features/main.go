// Package main 展示 Go 1.21-1.26 新特性
// 此文件作为团队学习参考
package main

import (
	"fmt"
	"maps"
	"math/rand/v2"
	"os"
	"slices"

	"log/slog"
)

func main() {
	// ===== 1. slog - 结构化日志 (Go 1.21) =====
	logger := slog.New(slog.NewJSONHandler(os.Stdout, nil))
	logger.Info("Application started",
		"version", "1.0.0",
		"env", "production",
	)

	// ===== 2. math/rand/v2 (Go 1.22) =====
	// 更好的性能，自动种子
	for i := range 5 {
		fmt.Printf("Random %d: %d\n", i, rand.IntN(100))
	}

	// ===== 3. range over integers (Go 1.22) =====
	fmt.Println("Range over integers:")
	for i := range 3 {
		fmt.Printf("  Index: %d\n", i)
	}

	// ===== 4. min/max 内置函数 (Go 1.21) =====
	a, b := 10, 20
	fmt.Printf("min(%d, %d) = %d\n", a, b, min(a, b))
	fmt.Printf("max(%d, %d) = %d\n", a, b, max(a, b))

	// ===== 5. slices 包 (Go 1.21) =====
	nums := []int{3, 1, 4, 1, 5, 9, 2, 6}
	slices.Sort(nums)
	fmt.Printf("Sorted: %v\n", nums)

	// 二分查找
	idx, found := slices.BinarySearch(nums, 5)
	fmt.Printf("Found 5 at index %d: %v\n", idx, found)

	// ===== 6. maps 包 (Go 1.21) =====
	m1 := map[string]int{"a": 1, "b": 2}
	m2 := maps.Clone(m1)
	fmt.Printf("Cloned map: %v\n", m2)

	// 判断相等
	fmt.Printf("Maps equal: %v\n", maps.Equal(m1, m2))

	// ===== 7. clear 内置函数 (Go 1.21) =====
	clear(m2)
	fmt.Printf("After clear: %v\n", m2)

	// ===== 8. 泛型函数类型推导 (Go 1.21+) =====
	result := min(3.14, 2.71) // 自动推导 float64
	fmt.Printf("min float: %v\n", result)

	logger.Info("Demo completed")
}
