# 运行所有基准测试并生成报告
# Usage: .\run_benchmarks.ps1

Write-Host "🏃 Running OTLP Go Benchmarks..." -ForegroundColor Cyan
Write-Host ""

# 切换到项目根目录
Set-Location $PSScriptRoot

# 创建结果目录
$resultsDir = "benchmark_results"
if (!(Test-Path $resultsDir)) {
    New-Item -ItemType Directory -Path $resultsDir | Out-Null
}

$timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
$resultFile = "$resultsDir\benchmark_$timestamp.txt"

Write-Host "📊 Running Span benchmarks..." -ForegroundColor Yellow
Set-Location benchmarks

# 运行所有基准测试
go test -bench=. -benchmem -benchtime=3s -run=^$ | Tee-Object -FilePath "..\$resultFile"

if ($LASTEXITCODE -eq 0) {
    Write-Host ""
    Write-Host "✅ Benchmark complete!" -ForegroundColor Green
    Write-Host "📄 Results saved to: $resultFile" -ForegroundColor Cyan
    
    # 显示摘要
    Write-Host ""
    Write-Host "📈 Benchmark Summary:" -ForegroundColor Cyan
    Write-Host ""
    Get-Content "..\$resultFile" | Select-String "Benchmark"
} else {
    Write-Host ""
    Write-Host "❌ Benchmark failed!" -ForegroundColor Red
    exit 1
}

Set-Location ..

Write-Host ""
Write-Host "🎉 All done!" -ForegroundColor Green

