# OPAMP 样例配置与流程

- Agent 声明能力（示意）：

```yaml
capabilities:
  accept:
    - remote_config
    - certificates
    - package_available
  plugins:
    - ottl
    - wasm
```

- 远程配置（带哈希/签名）：

```yaml
remote_config:
  version: 2025-09-01
  config_hash: "0xabcde"
  signature: "0xcafe"
  content:
    collector:
      processors:
        transform:
          traces:
            - set(status.message, "hotfix")
```

- 升级流程（时序要点）：
  1. Server 下发 `package_available{version, hash, signature}`
  2. Agent 下载→校验→原子替换→重启自报 `agent_identify{version}`
  3. Server 标记升级完成，按标签下发 OTTL 规则
  4. 健康异常触发自动回滚（对齐 formal-proof I3）
