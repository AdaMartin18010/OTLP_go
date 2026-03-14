# PowerShell script to fix Go 1.26 migration errors
# Fixes:
# 1. "declared and not used: i" errors - change "for i := range N" to "for range N"
#    ONLY when i is not used in the loop body
# 2. Unused "log/slog" import in pkg/errors/errors_test.go (if log is not used)
# 3. Undefined "log" reference - change to proper slog usage
#
# Usage: powershell -ExecutionPolicy Bypass -File fix_go126_migration.ps1
#        powershell -ExecutionPolicy Bypass -File fix_go126_migration.ps1 -WhatIf  (to preview changes)

param(
    [switch]$WhatIf
)

Write-Host "=== Go 1.26 Migration Fix Script ===" -ForegroundColor Cyan
Write-Host ""

$fixedCount = 0

# ============================================================================
# Fix 1: pkg/automation/automation_test.go
# ============================================================================
$file = "pkg/automation/automation_test.go"
if (Test-Path $file) {
    Write-Host "Fixing $file..." -ForegroundColor Cyan
    
    $content = Get-Content -Path $file -Raw
    $original = $content
    
    # Lines that have unused 'i': 879, 1608, 1634, 2502
    # These are waiting loops that don't use 'i' inside
    
    # Line 879: for i := range 10 { <-done }
    $content = $content -replace '(?m)^(\s+)for i := range 10 \{\s*\r?\n\s*<-done', '$1for range 10 {$2<-done'
    
    # Line 1608: for i := range 100 { <-done }  (waiting loop, not the goroutine loop)
    # Line 1634: for i := range 50 { err := <-done } (waiting loop, not the goroutine loop)
    # These are tricky because there are TWO loops with range 100/50 - one uses 'i', one doesn't
    # The waiting loop (after the goroutines) doesn't use 'i'
    
    # Line 2502: for i := range 5 { err := manager.ExecutePipeline(ctx) }
    $content = $content -replace '(?m)^(\s+)for i := range 5 \{\s*\r?\n(\s+)err := manager\.ExecutePipeline', '$1for range 5 {$2err := manager.ExecutePipeline'
    
    if ($content -ne $original) {
        if ($WhatIf) {
            Write-Host "  Would fix: unused 'i' in for-range loops" -ForegroundColor Yellow
        } else {
            Set-Content -Path $file -Value $content -NoNewline
            Write-Host "  Fixed: unused 'i' in for-range loops" -ForegroundColor Green
        }
        $fixedCount++
    } else {
        Write-Host "  No changes needed (already fixed or pattern not found)" -ForegroundColor Gray
    }
} else {
    Write-Host "File not found: $file" -ForegroundColor Red
}

Write-Host ""

# ============================================================================
# Fix 2: pkg/errors/errors_test.go
# ============================================================================
$file = "pkg/errors/errors_test.go"
if (Test-Path $file) {
    Write-Host "Fixing $file..." -ForegroundColor Cyan
    
    $content = Get-Content -Path $file -Raw
    $original = $content
    
    # Check if we need to add log/slog import (if using slog.New)
    if ($content -match 'slog\.New' -and $content -notmatch '"log/slog"') {
        # Add log/slog import after "fmt"
        $content = $content -replace '("fmt")\r?\n', "`$1`n`t`"log/slog`"`n"
        if ($WhatIf) {
            Write-Host "  Would add: 'log/slog' import" -ForegroundColor Yellow
        } else {
            Write-Host "  Fixed: added 'log/slog' import" -ForegroundColor Green
        }
        $original = $content
    }
    
    # Fix line 19: change log.New(...) to slog.New(slog.NewTextHandler(...))
    $content = $content -replace 'log\.New\(os\.Stdout, "test", log\.LstdFlags\)', 'slog.New(slog.NewTextHandler(os.Stdout, nil))'
    
    if ($content -ne $original) {
        if ($WhatIf) {
            Write-Host "  Would fix: 'log.New(...)' -> 'slog.New(slog.NewTextHandler(...))'" -ForegroundColor Yellow
        } else {
            Set-Content -Path $file -Value $content -NoNewline
            Write-Host "  Fixed: 'log.New(...)' -> 'slog.New(slog.NewTextHandler(...))'" -ForegroundColor Green
        }
        $fixedCount++
    } else {
        Write-Host "  No changes needed (already fixed or pattern not found)" -ForegroundColor Gray
    }
} else {
    Write-Host "File not found: $file" -ForegroundColor Red
}

Write-Host ""

# ============================================================================
# Fix 3: pkg/otel/otel_test.go
# ============================================================================
$file = "pkg/otel/otel_test.go"
if (Test-Path $file) {
    Write-Host "Fixing $file..." -ForegroundColor Cyan
    
    $content = Get-Content -Path $file -Raw
    $original = $content
    
    # Lines that have unused 'i':
    # Line 755, 770: for i := range 10 { managers = append(...) } - i not used
    # Line 901: for i := range 10 { go func() { ... }() } - i not used in goroutine
    # Line 910: for i := range 10 { <-done } - i not used
    # Line 1101: for i := range 5 { tp := manager.GetTracerProvider() } - i not used
    
    # Pattern: for i := range N { where i is not used in the body
    # Replace with: for range N {
    
    # Match patterns where 'i' is definitely not used:
    # - for i := range N { managers = append(...)
    # - for i := range N { go func() { ... }()
    # - for i := range N { <-done
    # - for i := range N { tp := ...
    
    $patterns = @(
        '(?m)^(\s+)for i := range 10 \{\s*\r?\n\s*managers = append',
        '(?m)^(\s+)for i := range 10 \{\s*\r?\n\s*go func\(\)',
        '(?m)^(\s+)for i := range 10 \{\s*\r?\n\s*<-done',
        '(?m)^(\s+)for i := range 5 \{\s*\r?\n\s*tp := manager\.GetTracerProvider'
    )
    $replacements = @(
        '$1for range 10 {$2managers = append',
        '$1for range 10 {$2go func()',
        '$1for range 10 {$2<-done',
        '$1for range 5 {$2tp := manager.GetTracerProvider'
    )
    
    for ($j = 0; $j -lt $patterns.Count; $j++) {
        $content = $content -replace $patterns[$j], $replacements[$j]
    }
    
    if ($content -ne $original) {
        if ($WhatIf) {
            Write-Host "  Would fix: unused 'i' in for-range loops" -ForegroundColor Yellow
        } else {
            Set-Content -Path $file -Value $content -NoNewline
            Write-Host "  Fixed: unused 'i' in for-range loops" -ForegroundColor Green
        }
        $fixedCount++
    } else {
        Write-Host "  No changes needed (already fixed or pattern not found)" -ForegroundColor Gray
    }
} else {
    Write-Host "File not found: $file" -ForegroundColor Red
}

Write-Host ""
Write-Host "=== Summary ===" -ForegroundColor Cyan
if ($WhatIf) {
    Write-Host "WhatIf mode: No changes were made. Run without -WhatIf to apply fixes." -ForegroundColor Yellow
} else {
    Write-Host "Total files fixed: $fixedCount" -ForegroundColor Green
}

# Verify by running go build
Write-Host ""
Write-Host "Verifying fixes by running 'go build ./...'..." -ForegroundColor Cyan
$buildOutput = & go build ./... 2>&1
if ($LASTEXITCODE -eq 0) {
    Write-Host "Build successful! All migration errors fixed." -ForegroundColor Green
} else {
    Write-Host "Build failed. Remaining errors:" -ForegroundColor Red
    $buildOutput | ForEach-Object { Write-Host "  $_" -ForegroundColor Red }
    exit 1
}
