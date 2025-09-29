# OTTL 示例与最佳实践

- 脱敏（生产环境对日志 body 做哈希）：

```yaml
processor:
  transform:
    error_mode: ignore
    traces:
      - set(attributes["user.id"], SHA256(attributes["user.id"])) where resource.attributes["env"] == "prod"
    logs:
      - set(body, SHA256(body)) where resource.attributes["env"] == "prod"
```

- 降维聚合（仅保留关键标签，降低后端高基数）：

```yaml
processor:
  transform:
    metrics:
      - keep_keys(attributes, ["cluster", "node"]) 
```

- 动态路由（按租户分流到不同 exporter）：

```yaml
processor:
  transform:
    traces:
      - route() where resource.attributes["tenant"] == "A"
```

- 异常标记（超时 span 标注）：

```yaml
processor:
  transform:
    traces:
      - set(status.message, "timeout_threshold_exceeded") where duration > 3s
```

- Tail Sampling 提示：先以 transform 标注异常，再在 tail_sampling 中按 `status`/属性采样，提高保真度并降低成本。
