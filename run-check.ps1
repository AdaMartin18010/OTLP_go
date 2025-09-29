@echo off
REM 检查健康与示例接口

try {
  $health = Invoke-WebRequest -UseBasicParsing http://localhost:8080/healthz -TimeoutSec 2
  Write-Output ("/healthz: {0} {1}" -f $health.StatusCode, $health.Content)
} catch {
  Write-Output "/healthz: fail"
}

try {
  $hello = Invoke-WebRequest -UseBasicParsing http://localhost:8080/hello -TimeoutSec 2
  Write-Output ("/hello: {0} {1}" -f $hello.StatusCode, $hello.Content)
} catch {
  Write-Output "/hello: fail"
}

