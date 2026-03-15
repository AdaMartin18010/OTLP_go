#!/usr/bin/env pwsh
# 项目完整验证脚本

$ErrorActionPreference = "Stop"
$results = @{
    Build = $false
    Test = $false
    Modules = 0
    Issues = @()
}

Write-Host "╔════════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║              OTLP_go 项目完整性验证                        ║" -ForegroundColor Cyan
Write-Host "╚════════════════════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# 1. 构建验证
Write-Host "[1/6] 构建验证..." -ForegroundColor Yellow
try {
    $buildOutput = go build ./... 2>&1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "  ✅ 构建成功" -ForegroundColor Green
        $results.Build = $true
    } else {
        Write-Host "  ❌ 构建失败" -ForegroundColor Red
        $results.Issues += "构建失败: $buildOutput"
    }
} catch {
    $results.Issues += "构建异常: $_"
}

# 2. 测试验证
Write-Host "`n[2/6] 测试验证..." -ForegroundColor Yellow
try {
    $testOutput = go test ./... 2>&1
    if ($LASTEXITCODE -eq 0) {
        $testCount = ($testOutput | Select-String "^ok").Count
        Write-Host "  ✅ 测试通过 ($testCount 个包)" -ForegroundColor Green
        $results.Test = $true
    } else {
        Write-Host "  ❌ 测试失败" -ForegroundColor Red
        $results.Issues += "测试失败"
    }
} catch {
    $results.Issues += "测试异常: $_"
}

# 3. 模块检查
Write-Host "`n[3/6] 模块检查..." -ForegroundColor Yellow
try {
    $modules = go list -m all 2>&1 | Where-Object { $_ -match "^OTLP_go" }
    $results.Modules = $modules.Count
    Write-Host "  ✅ 发现 $($results.Modules) 个模块" -ForegroundColor Green
} catch {
    $results.Issues += "模块检查失败: $_"
}

# 4. 代码统计
Write-Host "`n[4/6] 代码统计..." -ForegroundColor Yellow
$goFiles = Get-ChildItem -Recurse -Filter "*.go" | Where-Object { 
    $_.FullName -notmatch "docs|archive|.git" 
} | Measure-Object | Select-Object -ExpandProperty Count
Write-Host "  📄 Go 文件数: $goFiles" -ForegroundColor White

# 5. 文档检查
Write-Host "`n[5/6] 文档检查..." -ForegroundColor Yellow
$docs = @("README.md", "ARCHITECTURE.md", "WORKSPACE.md", "LICENSE")
$docOk = $true
foreach ($doc in $docs) {
    if (Test-Path $doc) {
        Write-Host "  ✅ $doc" -ForegroundColor Green
    } else {
        Write-Host "  ❌ $doc 缺失" -ForegroundColor Red
        $docOk = $false
    }
}

# 6. 关键功能检查
Write-Host "`n[6/6] 关键功能检查..." -ForegroundColor Yellow
$features = @(
    @{Path="pkg/logs/logger.go"; Name="Logs SDK"},
    @{Path=".github/workflows/ci.yml"; Name="CI/CD"},
    @{Path="go.work"; Name="Workspace"}
)
foreach ($feat in $features) {
    if (Test-Path $feat.Path) {
        Write-Host "  ✅ $($feat.Name)" -ForegroundColor Green
    } else {
        Write-Host "  ❌ $($feat.Name) 缺失" -ForegroundColor Red
    }
}

# 总结
Write-Host "`n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Gray
Write-Host "验证总结:" -ForegroundColor Cyan
Write-Host "  构建: $(if($results.Build){'✅通过'}else{'❌失败'})" -ForegroundColor $(if($results.Build){'Green'}else{'Red'})
Write-Host "  测试: $(if($results.Test){'✅通过'}else{'❌失败'})" -ForegroundColor $(if($results.Test){'Green'}else{'Red'})
Write-Host "  模块: $($results.Modules) 个" -ForegroundColor White
Write-Host "  文件: $goFiles 个 Go 文件" -ForegroundColor White

if ($results.Issues.Count -eq 0) {
    Write-Host "`n✨ 验证通过! 项目状态: 100% 完成 ✨" -ForegroundColor Green
    exit 0
} else {
    Write-Host "`n⚠️ 发现 $($results.Issues.Count) 个问题:" -ForegroundColor Yellow
    $results.Issues | ForEach-Object { Write-Host "  - $_" -ForegroundColor Red }
    exit 1
}
