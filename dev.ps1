#!/usr/bin/env pwsh
# 开发助手脚本

param(
    [Parameter()]
    [ValidateSet("build", "test", "clean", "watch", "tidy", "example")]
    [string]$Command = "build"
)

switch ($Command) {
    "build" {
        Write-Host "Building project..." -ForegroundColor Cyan
        go build ./...
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✅ Build successful" -ForegroundColor Green
        }
    }
    "test" {
        Write-Host "Running tests..." -ForegroundColor Cyan
        go test -race -v ./... 2>&1 | Select-String "^(ok|FAIL|---)"
    }
    "clean" {
        Write-Host "Cleaning..." -ForegroundColor Cyan
        go clean -cache
        Remove-Item -Force -ErrorAction SilentlyContinue coverage.out, coverage.html
        Write-Host "✅ Cleaned" -ForegroundColor Green
    }
    "watch" {
        Write-Host "Starting file watcher... (requires 'air' tool)" -ForegroundColor Cyan
        if (Get-Command air -ErrorAction SilentlyContinue) {
            air
        } else {
            Write-Host "Installing air..." -ForegroundColor Yellow
            go install github.com/cosmtrek/air@latest
            air
        }
    }
    "tidy" {
        Write-Host "Tidying modules..." -ForegroundColor Cyan
        go mod tidy
        go work sync
        Write-Host "✅ Modules tidied" -ForegroundColor Green
    }
    "example" {
        Write-Host "Running logs example..." -ForegroundColor Cyan
        go run examples/logs-sdk/main.go
    }
}
