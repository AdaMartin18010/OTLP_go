# 运行所有代码质量检查
# Usage: .\check_all.ps1

Write-Host "🔍 Running all code quality checks..." -ForegroundColor Cyan
Write-Host ""

# 切换到项目根目录
Set-Location $PSScriptRoot

$errorCount = 0

# 1. 格式化检查
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "📝 Step 1/5: Checking code formatting..." -ForegroundColor Yellow
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
$unformatted = go fmt ./...
if ($unformatted) {
    Write-Host "✅ Formatted files:" -ForegroundColor Green
    $unformatted | ForEach-Object { Write-Host "   - $_" -ForegroundColor Gray }
} else {
    Write-Host "✅ All files are properly formatted" -ForegroundColor Green
}
Write-Host ""

# 2. Vet 检查
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "🔎 Step 2/5: Running go vet..." -ForegroundColor Yellow
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
go vet ./...
if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ No issues found by go vet" -ForegroundColor Green
} else {
    Write-Host "❌ Go vet found issues" -ForegroundColor Red
    $errorCount++
}
Write-Host ""

# 3. 模块验证
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "📦 Step 3/5: Verifying modules..." -ForegroundColor Yellow
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
go mod verify
if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ All modules verified" -ForegroundColor Green
} else {
    Write-Host "❌ Module verification failed" -ForegroundColor Red
    $errorCount++
}
Write-Host ""

# 4. 构建检查
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "🏗️  Step 4/5: Building all code..." -ForegroundColor Yellow
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
go build ./...
if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ All code builds successfully" -ForegroundColor Green
} else {
    Write-Host "❌ Build failed" -ForegroundColor Red
    $errorCount++
}
Write-Host ""

# 5. 基准测试快速检查
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "🏃 Step 5/5: Running quick benchmark check..." -ForegroundColor Yellow
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Push-Location benchmarks
go test -bench=BenchmarkSpanCreation -benchtime=1s -run=^$ | Select-String "Benchmark"
if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ Benchmark test passed" -ForegroundColor Green
} else {
    Write-Host "❌ Benchmark test failed" -ForegroundColor Red
    $errorCount++
}
Pop-Location
Write-Host ""

# 总结
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "📊 Check Summary" -ForegroundColor Cyan
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host ""

if ($errorCount -eq 0) {
    Write-Host "🎉 All checks passed!" -ForegroundColor Green
    Write-Host ""
    Write-Host "✅ Code formatting: OK" -ForegroundColor Green
    Write-Host "✅ Go vet:          OK" -ForegroundColor Green
    Write-Host "✅ Module verify:   OK" -ForegroundColor Green
    Write-Host "✅ Build:           OK" -ForegroundColor Green
    Write-Host "✅ Benchmarks:      OK" -ForegroundColor Green
    Write-Host ""
    Write-Host "Ready to commit! 🚀" -ForegroundColor Cyan
    exit 0
} else {
    Write-Host "❌ $errorCount check(s) failed" -ForegroundColor Red
    Write-Host ""
    Write-Host "Please fix the issues above before committing." -ForegroundColor Yellow
    exit 1
}

