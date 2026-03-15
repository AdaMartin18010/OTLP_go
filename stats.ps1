#!/usr/bin/env pwsh
# 项目统计脚本

Write-Host "╔══════════════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║                      项目统计信息                                ║" -ForegroundColor Cyan
Write-Host "╚══════════════════════════════════════════════════════════════════╝" -ForegroundColor Cyan

# 代码统计
$goFiles = Get-ChildItem -Recurse -Filter "*.go" | Where-Object { $_.FullName -notmatch "docs|archive|.git" }
$totalLines = ($goFiles | Get-Content | Measure-Object).Count
$totalFiles = $goFiles.Count

Write-Host "`n📊 代码统计:" -ForegroundColor Yellow
Write-Host "  Go 文件数: $totalFiles" -ForegroundColor White
Write-Host "  代码行数: $totalLines" -ForegroundColor White

# 模块统计
$mods = Get-ChildItem -Recurse -Filter "go.mod" | Where-Object { $_.FullName -notmatch "docs|archive|.git" }
Write-Host "`n📦 模块统计:" -ForegroundColor Yellow
Write-Host "  总模块数: $($mods.Count)" -ForegroundColor White
Write-Host "  Examples: $((Get-ChildItem examples -Filter go.mod -ErrorAction SilentlyContinue).Count)" -ForegroundColor White
Write-Host "  Packages: $((Get-ChildItem pkg -Filter go.mod -ErrorAction SilentlyContinue).Count)" -ForegroundColor White

# 测试统计
$testFiles = Get-ChildItem -Recurse -Filter "*_test.go" | Where-Object { $_.FullName -notmatch "docs|archive|.git" }
Write-Host "`n🧪 测试统计:" -ForegroundColor Yellow
Write-Host "  测试文件数: $($testFiles.Count)" -ForegroundColor White

# 文档统计
$docs = Get-ChildItem -Filter "*.md" | Where-Object { $_.Name -notmatch "^ACHIEVEMENTS|^COMPLETION|^FINAL|^PROGRESS" }
Write-Host "`n📄 文档统计:" -ForegroundColor Yellow
Write-Host "  主要文档: $($docs.Count)" -ForegroundColor White

# 依赖版本
Write-Host "`n🔧 依赖版本:" -ForegroundColor Yellow
$otelVersion = go list -m -json go.opentelemetry.io/otel 2>$null | ConvertFrom-Json | Select-Object -ExpandProperty Version
Write-Host "  OpenTelemetry: $otelVersion" -ForegroundColor White

# Git 统计（如果有）
if (Test-Path .git) {
    Write-Host "`n📝 Git 统计:" -ForegroundColor Yellow
    $commits = git rev-list --count HEAD 2>$null
    if ($commits) {
        Write-Host "  提交数: $commits" -ForegroundColor White
    }
    $branch = git branch --show-current 2>$null
    if ($branch) {
        Write-Host "  当前分支: $branch" -ForegroundColor White
    }
}

Write-Host "`n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Gray
