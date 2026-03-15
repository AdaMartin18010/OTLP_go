# Elasticsearch语义约定详解

> **搜索与分析引擎**: Elasticsearch Tracing与Metrics完整规范  
> **最后更新**: 2025年10月8日

---

## 目录

- [Elasticsearch语义约定详解](#elasticsearch语义约定详解)
  - [目录](#目录)
  - [1. Elasticsearch概述](#1-elasticsearch概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 核心架构](#12-核心架构)
  - [2. Elasticsearch通用属性](#2-elasticsearch通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. 操作类型属性](#3-操作类型属性)
    - [3.1 索引操作](#31-索引操作)
    - [3.2 搜索操作](#32-搜索操作)
  - [4. Go实现示例](#4-go实现示例)
    - [4.1 基本操作](#41-基本操作)
    - [4.2 批量操作](#42-批量操作)
  - [5. Python实现示例](#5-python实现示例)
    - [5.1 elasticsearch-py](#51-elasticsearch-py)
  - [6. Metrics定义](#6-metrics定义)
  - [7. 最佳实践](#7-最佳实践)

---

## 1. Elasticsearch概述

### 1.1 核心特性

```text
Elasticsearch - 分布式搜索与分析引擎

核心特性:
✅ 全文搜索
✅ 实时索引
✅ RESTful API
✅ 分布式架构
✅ JSON文档存储
✅ 聚合分析
✅ 地理空间查询
```

### 1.2 核心架构

```text
Cluster → Nodes → Indices → Shards → Documents
```

---

## 2. Elasticsearch通用属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `db.system` | string | 数据库系统 | `"elasticsearch"` |
| `db.operation` | string | 操作类型 | `"search"`, `"index"` |
| `db.elasticsearch.index` | string | 索引名称 | `"logs-2025"` |
| `net.peer.name` | string | ES节点地址 | `"es.example.com"` |
| `net.peer.port` | int | ES端口 | `9200` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `db.statement` | string | 查询DSL | `"{\"query\":{\"match_all\":{}}}"` |
| `db.elasticsearch.cluster.name` | string | 集群名称 | `"production"` |
| `db.response.returned_count` | int | 返回文档数 | `10` |

---

## 3. 操作类型属性

### 3.1 索引操作

| 操作 | db.operation | 描述 |
|------|--------------|------|
| Index | `"index"` | 索引文档 |
| Update | `"update"` | 更新文档 |
| Delete | `"delete"` | 删除文档 |
| Bulk | `"bulk"` | 批量操作 |

### 3.2 搜索操作

| 操作 | db.operation | 描述 |
|------|--------------|------|
| Search | `"search"` | 搜索文档 |
| Count | `"count"` | 计数 |
| Scroll | `"scroll"` | 滚动查询 |

---

## 4. Go实现示例

### 4.1 基本操作

```go
func IndexDocumentWithTracing(
    ctx context.Context,
    client *elasticsearch.Client,
    index string,
    docID string,
    doc interface{},
) error {
    tracer := otel.Tracer("es-client")
    
    ctx, span := tracer.Start(ctx, "elasticsearch.index",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemElasticsearch,
            semconv.DBOperationKey.String("index"),
            attribute.String("db.elasticsearch.index", index),
        ),
    )
    defer span.End()
    
    // 索引文档
    body, _ := json.Marshal(doc)
    res, err := client.Index(
        index,
        bytes.NewReader(body),
        client.Index.WithDocumentID(docID),
        client.Index.WithContext(ctx),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "index failed")
        return err
    }
    defer res.Body.Close()
    
    span.SetStatus(codes.Ok, "indexed")
    return nil
}
```

### 4.2 批量操作

```go
func BulkIndexWithTracing(
    ctx context.Context,
    client *elasticsearch.Client,
    docs []interface{},
) error {
    tracer := otel.Tracer("es-client")
    
    ctx, span := tracer.Start(ctx, "elasticsearch.bulk",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemElasticsearch,
            semconv.DBOperationKey.String("bulk"),
            attribute.Int("db.elasticsearch.bulk_size", len(docs)),
        ),
    )
    defer span.End()
    
    // 构建批量请求
    var buf bytes.Buffer
    for _, doc := range docs {
        meta := map[string]interface{}{
            "index": map[string]interface{}{
                "_index": "myindex",
            },
        }
        json.NewEncoder(&buf).Encode(meta)
        json.NewEncoder(&buf).Encode(doc)
    }
    
    // 执行批量操作
    res, err := client.Bulk(
        bytes.NewReader(buf.Bytes()),
        client.Bulk.WithContext(ctx),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "bulk failed")
        return err
    }
    defer res.Body.Close()
    
    span.SetStatus(codes.Ok, "bulk completed")
    return nil
}
```

---

## 5. Python实现示例

### 5.1 elasticsearch-py

```python
from elasticsearch import Elasticsearch
from opentelemetry import trace

tracer = trace.get_tracer(__name__)

def index_document_with_tracing(client: Elasticsearch, index: str, doc: dict):
    """索引文档with tracing"""
    with tracer.start_as_current_span(
        "elasticsearch.index",
        kind=SpanKind.CLIENT,
        attributes={
            "db.system": "elasticsearch",
            "db.operation": "index",
            "db.elasticsearch.index": index,
        }
    ) as span:
        try:
            response = client.index(index=index, document=doc)
            span.set_status(Status(StatusCode.OK))
            return response
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

def search_with_tracing(client: Elasticsearch, index: str, query: dict):
    """搜索with tracing"""
    with tracer.start_as_current_span(
        "elasticsearch.search",
        kind=SpanKind.CLIENT,
        attributes={
            "db.system": "elasticsearch",
            "db.operation": "search",
            "db.elasticsearch.index": index,
        }
    ) as span:
        try:
            response = client.search(index=index, query=query)
            
            hits = response['hits']['total']['value']
            span.set_attribute("db.response.returned_count", hits)
            span.set_status(Status(StatusCode.OK))
            
            return response
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise
```

---

## 6. Metrics定义

| Metric | 类型 | 描述 |
|--------|------|------|
| `db.client.operation.duration` | Histogram | 操作延迟 |
| `db.client.operations` | Counter | 操作次数 |
| `db.elasticsearch.indexing.rate` | Gauge | 索引速率 |
| `db.elasticsearch.search.rate` | Gauge | 搜索速率 |

---

## 7. 最佳实践

```text
性能优化:
1. 批量索引 ⭐⭐⭐⭐⭐
2. 合理分片数
3. 使用过滤器缓存
4. 异步操作

监控指标:
- 搜索延迟
- 索引速率
- 集群健康状态
- JVM堆使用
```

---

**文档状态**: ✅ 完成  
**Elasticsearch版本**: 7.x / 8.x  
**适用场景**: 全文搜索、日志分析、实时分析

**关键特性**:

- ✅ 索引与搜索操作追踪
- ✅ 批量操作支持
- ✅ Go/Python示例
- ✅ 性能优化建议
