# 测试所有示例代码
# Usage: .\test_all_examples.ps1

Write-Host "🧪 Testing all OTLP Go examples..." -ForegroundColor Cyan
Write-Host ""

# 切换到项目根目录
Set-Location $PSScriptRoot

# 示例列表
$examples = @(
    "basic",
    "context-propagation",
    "custom-sampler",
    "batch-export",
    "metrics",
    "performance\span-pool",
    "performance\zero-alloc",
    "resilience\circuit-breaker",
    "resilience\retry",
    "custom-processor",
    "distributed-tracing",
    "go125-features",
    "memory-optimization",
    "performance-tuning",
    "error-handling",
    "custom-components"
)

$successCount = 0
$failCount = 0
$failedExamples = @()

foreach ($example in $examples) {
    $examplePath = "examples\$example"
    
    if (!(Test-Path $examplePath)) {
        Write-Host "⚠️  Skipping $example (path not found)" -ForegroundColor Yellow
        continue
    }
    
    Write-Host "📦 Testing $example..." -ForegroundColor Yellow
    
    Push-Location $examplePath
    
    # 检查是否有 go.mod
    if (Test-Path "go.mod") {
        Write-Host "   📥 Downloading dependencies..." -ForegroundColor Gray
        go mod download 2>&1 | Out-Null
    }
    
    # 编译检查
    Write-Host "   🔨 Compiling..." -ForegroundColor Gray
    $output = go build -o temp.exe main.go 2>&1
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "   ✅ $example compiled successfully" -ForegroundColor Green
        Remove-Item temp.exe -ErrorAction SilentlyContinue
        $successCount++
    } else {
        Write-Host "   ❌ $example failed to compile" -ForegroundColor Red
        Write-Host "   Error: $output" -ForegroundColor Red
        $failCount++
        $failedExamples += $example
    }
    
    Pop-Location
    Write-Host ""
}

# 显示总结
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "📊 Test Summary" -ForegroundColor Cyan
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host ""
Write-Host "✅ Successful: $successCount" -ForegroundColor Green
Write-Host "❌ Failed:     $failCount" -ForegroundColor Red
Write-Host ""

if ($failCount -gt 0) {
    Write-Host "Failed examples:" -ForegroundColor Red
    foreach ($example in $failedExamples) {
        Write-Host "  - $example" -ForegroundColor Red
    }
    Write-Host ""
    exit 1
} else {
    Write-Host "🎉 All examples compiled successfully!" -ForegroundColor Green
    exit 0
}

