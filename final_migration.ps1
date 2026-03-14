# Go 1.26 最终迁移脚本 - 100% 完成
# 修复所有遗漏的旧模式代码

$ErrorActionPreference = "Continue"
$fixedCount = 0

function Fix-File {
    param($Path, $Replacements)
    $fullPath = Join-Path $PSScriptRoot $Path
    if (-not (Test-Path $fullPath)) { return }
    
    $content = Get-Content $fullPath -Raw -Encoding UTF8
    $original = $content
    
    foreach ($rep in $Replacements) {
        $content = $content -replace $rep.Pattern, $rep.Replacement
    }
    
    if ($content -ne $original) {
        Set-Content $fullPath $content -Encoding UTF8 -NoNewline
        $script:fixedCount++
        Write-Host "  ✓ $Path" -ForegroundColor Green
    }
}

Write-Host "`n=== Go 1.26 最终迁移开始 ===`n" -ForegroundColor Cyan

# 1. 修复所有剩余的 for i:=0; i<N; i++ 循环
Write-Host "[1/5] 修复传统 for 循环..." -ForegroundColor Yellow
$forLoopFiles = @(
    @{Path="benchmarks/export_test.go"; Pattern='for\s+i\s*:=\s*0\s*;\s*i\s*<\s*count\s*;\s*i\+\+'; Replacement='for i := range count'},
    @{Path="benchmarks/export_test.go"; Pattern='for\s+j\s*:=\s*0\s*;\s*j\s*<\s*count\s*;\s*j\+\+'; Replacement='for j := range count'},
    @{Path="examples/batch-export/main.go"; Pattern='for\s+i\s*:=\s*0\s*;\s*i\s*<\s*spanCount\s*;\s*i\+\+'; Replacement='for i := range spanCount'},
    @{Path="pkg/concurrency/semaphore_test.go"; Pattern='for\s+i\s*:=\s*0\s*;\s*i\s*<\s*iterations\s*;\s*i\+\+'; Replacement='for i := range iterations'},
    @{Path="pkg/pool/pool_test.go"; Pattern='for\s+i\s*:=\s*0\s*;\s*i\s*<\s*iterations\s*;\s*i\+\+'; Replacement='for i := range iterations'},
    @{Path="pkg/shutdown/manager_test.go"; Pattern='for\s+j\s*:=\s*0\s*;\s*j\s*<\s*10\s*;\s*j\+\+'; Replacement='for j := range 10'},
    @{Path="pkg/shutdown/manager_test.go"; Pattern='for\s+j\s*:=\s*0\s*;\s*j\s*<\s*3\s*;\s*j\+\+'; Replacement='for j := range 3'},
    @{Path="pkg/performance/performance_test.go"; Pattern='for\s+i\s*:=\s*0\s*;\s*i\s*<\s*goroutines\s*;\s*i\+\+'; Replacement='for i := range goroutines'},
    @{Path="pkg/performance/performance_test.go"; Pattern='for\s+j\s*:=\s*0\s*;\s*j\s*<\s*updatesPerGoroutine\s*;\s*j\+\+'; Replacement='for j := range updatesPerGoroutine'},
    @{Path="pkg/performance/performance.go"; Pattern='for\s+i\s*:=\s*0\s*;\s*i\s*<\s*iterations\s*;\s*i\+\+'; Replacement='for i := range iterations'}
)

foreach ($file in $forLoopFiles) {
    Fix-File -Path $file.Path -Replacements @(@{Pattern=$file.Pattern; Replacement=$file.Replacement})
}

# 2. 修复 min 函数
Write-Host "`n[2/5] 应用 min/max 内置函数..." -ForegroundColor Yellow
Fix-File -Path "pkg/concurrency/semaphore.go" -Replacements @(
    @{Pattern='if\s+a\s*<\s*b\s*\{\s*\n\s*return\s+a\s*\n\s*\}\s*\n\s*return\s+b'; Replacement='return min(a, b)'}
)
Fix-File -Path "src/pkg/concurrency/semaphore.go" -Replacements @(
    @{Pattern='if\s+a\s*<\s*b\s*\{\s*\n\s*return\s+a\s*\n\s*\}\s*\n\s*return\s+b'; Replacement='return min(a, b)'}
)

# 3. 修复 examples 目录下的 for 循环
Write-Host "`n[3/5] 修复 examples 目录..." -ForegroundColor Yellow
$exampleFiles = Get-ChildItem -Path "examples" -Recurse -Filter "*.go" | Where-Object { $_.Name -match "main\.go$" }
foreach ($file in $exampleFiles) {
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $original = $content
    
    # 修复 for i := 0; i < iterations; i++
    $content = $content -replace 'for\s+i\s*:=\s*0\s*;\s*i\s*<\s*iterations\s*;\s*i\+\+', 'for i := range iterations'
    # 修复 for i := 0; i < workers; i++
    $content = $content -replace 'for\s+i\s*:=\s*0\s*;\s*i\s*<\s*workers\s*;\s*i\+\+', 'for i := range workers'
    # 修复 for i := 0; i < allocCount; i++
    $content = $content -replace 'for\s+i\s*:=\s*0\s*;\s*i\s*<\s*allocCount\s*;\s*i\+\+', 'for i := range allocCount'
    # 修复 for i := 0; i < spanCount; i++
    $content = $content -replace 'for\s+i\s*:=\s*0\s*;\s*i\s*<\s*spanCount\s*;\s*i\+\+', 'for i := range spanCount'
    
    if ($content -ne $original) {
        Set-Content $file.FullName $content -Encoding UTF8 -NoNewline
        $fixedCount++
        Write-Host "  ✓ $($file.FullName.Replace($PSScriptRoot, ''))" -ForegroundColor Green
    }
}

# 4. 修复 pkg/security 中的 for 循环
Write-Host "`n[4/5] 修复 security 测试..." -ForegroundColor Yellow
Fix-File -Path "pkg/security/security_test.go" -Replacements @(
    @{Pattern='for\s+j\s*:=\s*0\s*;\s*j\s*<\s*10\s*;\s*j\+\+'; Replacement='for j := range 10'}
)

# 5. 修复标准深度梳理目录下的文件
Write-Host "`n[5/5] 修复标准深度梳理目录..." -ForegroundColor Yellow
$stdFiles = Get-ChildItem -Path "标准深度梳理_2025_10" -Recurse -Filter "*.go" -ErrorAction SilentlyContinue
foreach ($file in $stdFiles) {
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $original = $content
    
    $content = $content -replace 'for\s+i\s*:=\s*0\s*;\s*i\s*<\s*(\w+)\s*;\s*i\+\+', 'for i := range $1'
    $content = $content -replace 'for\s+j\s*:=\s*0\s*;\s*j\s*<\s*(\w+)\s*;\s*j\+\+', 'for j := range $1'
    
    if ($content -ne $original) {
        Set-Content $file.FullName $content -Encoding UTF8 -NoNewline
        $fixedCount++
        Write-Host "  ✓ $($file.FullName.Replace($PSScriptRoot, ''))" -ForegroundColor Green
    }
}

Write-Host "`n=== 最终迁移完成 ===" -ForegroundColor Green
Write-Host "修复文件数: $fixedCount" -ForegroundColor Cyan
Write-Host "`n请运行 'go build ./...' 和 'go test ./...' 验证" -ForegroundColor Yellow
