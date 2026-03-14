# 手动修复脚本 - 处理复杂的 log -> slog 转换

$files = @(
    @{Path="src/microservices/main_demo.go"; Changes=@(
        @{From='"log"'; To='"log/slog"'},
        @{From='log\.Printf\("'; To='slog.Info("'},
        @{From='log\.Fatal'; To='slog.Error'}
    )},
    @{Path="pkg/otel/otel.go"; Changes=@(
        @{From='"log"'; To='"log/slog"'},
        @{From='log\.Printf\('; 'slog.Info('},
        @{From='log\.Fatal'; To='slog.Error'}
    )}
)

foreach ($file in $files) {
    $fullPath = Join-Path $PSScriptRoot $file.Path
    if (Test-Path $fullPath) {
        $content = Get-Content $fullPath -Raw -Encoding UTF8
        foreach ($change in $file.Changes) {
            $content = $content -replace $change.From, $change.To
        }
        Set-Content $fullPath $content -Encoding UTF8
        Write-Host "✓ Fixed $($file.Path)" -ForegroundColor Green
    }
}
