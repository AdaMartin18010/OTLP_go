@echo off
param(
  [string]$Action = "up"
)

if ($Action -eq "up") {
  docker compose up --build -d
  Write-Output "docker compose 已启动：app(http://localhost:8080)、collector(4317/4318)"
} elseif ($Action -eq "down") {
  docker compose down -v
  Write-Output "docker compose 已停止并清理卷。"
} elseif ($Action -eq "logs") {
  docker compose logs -f --tail=200
} else {
  Write-Output "用法: ./run-docker.ps1 [up|down|logs]，默认 up"
}

