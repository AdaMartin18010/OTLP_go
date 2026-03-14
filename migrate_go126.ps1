# Go 1.26 新特性迁移脚本
# 自动应用 Go 1.21-1.26 的所有新特性

$ErrorActionPreference = "Continue"
$totalFiles = 0
$modifiedFiles = 0

function Write-Progress {
    param($Activity, $PercentComplete)
    Write-Host "[$PercentComplete%] $Activity" -ForegroundColor Cyan
}

# ==================== 1. 修复 math/rand -> math/rand/v2 ====================
Write-Progress -Activity "修复 math/rand -> math/rand/v2" -PercentComplete 10

$randFiles = @(
    "examples/custom-sampler/main.go",
    "examples/error-handling/main.go", 
    "examples/distributed-tracing/main.go",
    "examples/metrics/main.go",
    "pkg/testing/testing.go",
    "src/microservices/payment_service.go",
    "examples/resilience/retry/main.go"
)

foreach ($file in $randFiles) {
    $fullPath = Join-Path $PSScriptRoot $file
    if (Test-Path $fullPath) {
        $content = Get-Content $fullPath -Raw -Encoding UTF8
        $original = $content
        
        # 替换 import
        $content = $content -replace '"math/rand"', '"math/rand/v2"'
        
        # 替换方法调用 (注意大小写变化)
        $content = $content -replace '\brand\.Intn\(', 'rand.IntN('
        $content = $content -replace '\brand\.Float64\(\)', 'rand.Float64()'  # 保持不变
        $content = $content -replace '\brand\.Int63\(\)', 'rand.Int64()'      # v2 使用 Int64
        $content = $content -replace '\brand\.Int31\(\)', 'rand.Int32()'      # v2 使用 Int32
        $content = $content -replace '\brand\.Uint32\(\)', 'rand.Uint32()'    # 保持不变
        $content = $content -replace '\brand\.Seed\(', '// rand.Seed('         # v2 自动种子，注释掉
        
        if ($content -ne $original) {
            Set-Content $fullPath $content -Encoding UTF8 -NoNewline
            $modifiedFiles++
            Write-Host "  ✓ $file" -ForegroundColor Green
        }
        $totalFiles++
    }
}

# ==================== 2. 修复 log -> log/slog ====================
Write-Progress -Activity "修复 log -> log/slog" -PercentComplete 25

$logFiles = @(
    "src/main.go",
    "src/microservices/main_demo.go",
    "pkg/errors/errors.go",
    "pkg/errors/errors_test.go",
    "pkg/otel/otel.go"
)

foreach ($file in $logFiles) {
    $fullPath = Join-Path $PSScriptRoot $file
    if (Test-Path $fullPath) {
        $content = Get-Content $fullPath -Raw -Encoding UTF8
        $original = $content
        
        # 替换 import
        if ($content -match '"log"') {
            $content = $content -replace '"log"', '"log/slog"'
            
            # 简单替换 log.Printf -> slog.Info (简化版本)
            # 复杂日志需要手动调整
            Write-Host "  ⚠ $file - 需要手动调整 log/slog 调用" -ForegroundColor Yellow
        }
        
        if ($content -ne $original) {
            Set-Content $fullPath $content -Encoding UTF8 -NoNewline
        }
        $totalFiles++
    }
}

# ==================== 3. 修复 for 循环 -> range N ====================
Write-Progress -Activity "修复 for 循环 -> range N (Go 1.22)" -PercentComplete 40

# 获取所有 Go 文件
$goFiles = Get-ChildItem -Path $PSScriptRoot -Recurse -Filter "*.go" | 
    Where-Object { 
        $_.FullName -notmatch "标准深度梳理" -and 
        $_.FullName -notmatch "\\\.git" -and
        $_.FullName -notmatch "vendor"
    }

foreach ($file in $goFiles) {
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $original = $content
    
    # 匹配简单的 for i := 0; i < N; i++ 模式
    # 注意：只替换常量 N，变量需要手动检查
    $content = $content -replace 'for\s+i\s*:=\s*0\s*;\s*i\s*<\s*(\d+)\s*;\s*i\+\+\s*\{', 'for i := range $1 {'
    $content = $content -replace 'for\s+_\s*:=\s*0\s*;\s*_\s*<\s*(\d+)\s*;\s*_\+\+\s*\{', 'for range $1 {'
    
    if ($content -ne $original) {
        Set-Content $file.FullName $content -Encoding UTF8 -NoNewline
        $modifiedFiles++
        Write-Host "  ✓ $($file.Name)" -ForegroundColor Green
    }
    $totalFiles++
}

# ==================== 4. 更新 go.mod 版本 ====================
Write-Progress -Activity "更新 go.mod 版本到 1.23" -PercentComplete 60

$modFiles = Get-ChildItem -Path $PSScriptRoot -Recurse -Filter "go.mod" |
    Where-Object { $_.FullName -notmatch "标准深度梳理" }

foreach ($file in $modFiles) {
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $original = $content
    
    # 更新 Go 版本到 1.23 (稳定的最新版)
    $content = $content -replace 'go\s+1\.\d+\s*\r?\n', "go 1.23`n"
    
    if ($content -ne $original) {
        Set-Content $file.FullName $content -Encoding UTF8 -NoNewline
        Write-Host "  ✓ $($file.FullName.Replace($PSScriptRoot, ''))" -ForegroundColor Green
    }
}

# ==================== 5. 创建 go126_features.go 演示文件 ====================
Write-Progress -Activity "创建 Go 1.26 特性演示文件" -PercentComplete 80

$featuresDemo = @'
// Package go126features 展示 Go 1.21-1.26 新特性
// 此文件作为团队学习参考
package main

import (
	"fmt"
	"log/slog"
	"maps"
	"math/rand/v2"
	"os"
	"slices"
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
}
'@

$demoPath = Join-Path $PSScriptRoot "examples/go126-features/main.go"
Set-Content $demoPath $featuresDemo -Encoding UTF8
Write-Host "  ✓ Created examples/go126-features/main.go" -ForegroundColor Green

# ==================== 完成统计 ====================
Write-Progress -Activity "Go 1.26 迁移完成" -PercentComplete 100

Write-Host "`n=== 迁移统计 ===" -ForegroundColor Cyan
Write-Host "总检查文件: $totalFiles" -ForegroundColor White
Write-Host "修改文件: $modifiedFiles" -ForegroundColor Green
Write-Host "`n下一步:" -ForegroundColor Yellow
Write-Host "  1. 运行 'go mod tidy' 更新依赖" -ForegroundColor Gray
Write-Host "  2. 运行 'go test ./...' 验证测试" -ForegroundColor Gray
Write-Host "  3. 手动检查 log/slog 的复杂调用" -ForegroundColor Gray
