#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Fixes UTF-8 BOM issues in go.mod files by removing the BOM if present.

.DESCRIPTION
    This script reads each specified go.mod file as bytes, checks for UTF-8 BOM
    (0xEF 0xBB 0xBF), removes it if present, and writes the file back without BOM.

.NOTES
    UTF-8 BOM bytes: 0xEF 0xBB 0xBF (239 187 191 in decimal)
#>

# List of go.mod files to process (relative to project root)
$goModFiles = @(
    "go.mod",
    "examples/batch-export/go.mod",
    "examples/context-propagation/go.mod",
    "examples/custom-processor/go.mod",
    "examples/custom-sampler/go.mod",
    "examples/distributed-tracing/go.mod",
    "examples/logs/go.mod",
    "examples/metrics/go.mod",
    "examples/microservices/go.mod",
    "examples/performance/go.mod",
    "examples/resilience/go.mod",
    "pkg/automation/go.mod",
    "pkg/concurrency/go.mod",
    "pkg/config/go.mod",
    "pkg/context/go.mod",
    "pkg/errors/go.mod",
    "pkg/options/go.mod",
    "pkg/otel/go.mod",
    "pkg/performance/go.mod",
    "pkg/pool/go.mod",
    "pkg/profiling/go.mod",
    "pkg/resource/go.mod",
    "pkg/runtime/go.mod",
    "pkg/security/go.mod",
    "pkg/shutdown/go.mod"
)

# UTF-8 BOM bytes
$BOM = [byte[]]@(0xEF, 0xBB, 0xBF)

$projectRoot = $PSScriptRoot
$fixedFiles = @()
$alreadyClean = @()
$notFound = @()

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "UTF-8 BOM Fix Script for go.mod files" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

foreach ($relativePath in $goModFiles) {
    $fullPath = Join-Path $projectRoot $relativePath
    
    if (-not (Test-Path $fullPath)) {
        Write-Host "[NOT FOUND] $relativePath" -ForegroundColor Yellow
        $notFound += $relativePath
        continue
    }
    
    # Read file as bytes
    $bytes = [System.IO.File]::ReadAllBytes($fullPath)
    
    # Check if file has BOM
    $hasBOM = $bytes.Length -ge 3 -and 
              $bytes[0] -eq $BOM[0] -and 
              $bytes[1] -eq $BOM[1] -and 
              $bytes[2] -eq $BOM[2]
    
    if ($hasBOM) {
        # Remove BOM by taking everything after the first 3 bytes
        $newBytes = $bytes[3..($bytes.Length - 1)]
        [System.IO.File]::WriteAllBytes($fullPath, $newBytes)
        Write-Host "[FIXED] $relativePath" -ForegroundColor Green
        $fixedFiles += $relativePath
    } else {
        Write-Host "[OK] $relativePath (no BOM)" -ForegroundColor DarkGray
        $alreadyClean += $relativePath
    }
}

Write-Host ""
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Summary" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Files fixed: $($fixedFiles.Count)" -ForegroundColor Green
Write-Host "Files already clean: $($alreadyClean.Count)" -ForegroundColor DarkGray
Write-Host "Files not found: $($notFound.Count)" -ForegroundColor Yellow

if ($fixedFiles.Count -gt 0) {
    Write-Host ""
    Write-Host "Fixed files:" -ForegroundColor Green
    foreach ($file in $fixedFiles) {
        Write-Host "  - $file" -ForegroundColor Green
    }
}

if ($notFound.Count -gt 0) {
    Write-Host ""
    Write-Host "Files not found:" -ForegroundColor Yellow
    foreach ($file in $notFound) {
        Write-Host "  - $file" -ForegroundColor Yellow
    }
}

Write-Host ""
Write-Host "BOM fix operation completed!" -ForegroundColor Cyan
