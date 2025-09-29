REM 启动 Collector 与 App（分别在新 PowerShell 进程中），并等待健康就绪

REM 启动 Collector
Start-Process powershell -ArgumentList '-NoProfile -ExecutionPolicy Bypass -Command ./run-collector.ps1'

REM 等待 Collector 监听 4317（最多 10 秒）
$ok = $false
for ($i=0; $i -lt 10; $i++) {
  $conn = Get-NetTCPConnection -LocalPort 4317 -State Listen -ErrorAction SilentlyContinue
  if ($conn) { $ok = $true; break }
  Start-Sleep -Milliseconds 700
}
if (-not $ok) { Write-Output "Collector 未在 4317 就绪，继续启动应用..." }

REM 启动应用
Start-Process powershell -ArgumentList '-NoProfile -ExecutionPolicy Bypass -Command ./run-app.ps1'

REM 等待健康就绪（最多 10 秒）
$ready = $false
for ($i=0; $i -lt 10; $i++) {
  try {
    $resp = Invoke-WebRequest -UseBasicParsing http://localhost:8080/healthz -TimeoutSec 2
    if ($resp.StatusCode -eq 200) { $ready = $true; break }
  } catch { }
  Start-Sleep -Milliseconds 700
}

if ($ready) {
  Write-Output "App 就绪：http://localhost:8080 ；健康检查通过。"
} else {
  Write-Output "App 未在超时内就绪，仍已拉起，可稍后重试健康检查。"
}

Write-Output "Collector 与 App 已启动。Collector: configs/collector.yaml, App: http://localhost:8080"
