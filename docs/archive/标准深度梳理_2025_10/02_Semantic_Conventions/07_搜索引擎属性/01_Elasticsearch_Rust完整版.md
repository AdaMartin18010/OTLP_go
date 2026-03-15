# Elasticsearch 追踪 - Rust 完整实现指南

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - elasticsearch: 8.20.0
> - opentelemetry: 0.31.0
> - tracing: 0.1.41
> - tokio: 1.47.1
> - 更新日期: 2025-10-08

## 目录

- [Elasticsearch 追踪 - Rust 完整实现指南](#elasticsearch-追踪---rust-完整实现指南)
  - [目录](#目录)
  - [概述](#概述)
    - [Elasticsearch 特性](#elasticsearch-特性)
    - [Rust 集成优势](#rust-集成优势)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml](#cargotoml)
  - [Elasticsearch 语义约定](#elasticsearch-语义约定)
    - [OpenTelemetry 属性](#opentelemetry-属性)
    - [Rust 实现](#rust-实现)
  - [客户端初始化](#客户端初始化)
    - [创建 Elasticsearch 客户端](#创建-elasticsearch-客户端)
  - [索引操作追踪](#索引操作追踪)
    - [索引管理](#索引管理)
  - [文档操作追踪](#文档操作追踪)
    - [CRUD 操作](#crud-操作)
  - [搜索操作追踪](#搜索操作追踪)
    - [全文搜索](#全文搜索)
  - [批量操作追踪](#批量操作追踪)
    - [Bulk API](#bulk-api)
  - [聚合查询追踪](#聚合查询追踪)
    - [聚合分析](#聚合分析)
  - [性能优化](#性能优化)
    - [1. 批量操作优化](#1-批量操作优化)
    - [2. 并发搜索](#2-并发搜索)
  - [最佳实践](#最佳实践)
    - [1. 索引映射定义](#1-索引映射定义)
    - [2. 错误重试策略](#2-错误重试策略)
  - [完整示例](#完整示例)
    - [main.rs](#mainrs)
  - [总结](#总结)

---

## 概述

### Elasticsearch 特性

- **全文搜索**: 强大的文本分析和搜索能力
- **分布式架构**: 水平扩展、自动分片
- **RESTful API**: HTTP/JSON 接口
- **实时性**: 近实时搜索和分析
- **多租户**: 索引级别隔离

### Rust 集成优势

- **类型安全**: 强类型查询 DSL
- **异步性能**: Tokio 高效 HTTP 客户端
- **内存安全**: 无数据竞争
- **零成本抽象**: 追踪开销最小化

---

## 核心依赖配置

### Cargo.toml

```toml
[package]
name = "elasticsearch-otlp"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Elasticsearch 客户端
elasticsearch = "8.20.0"
url = "2.5.4"

# OpenTelemetry 核心
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["http-json"] }

# Tracing 生态
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.19", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.29.0"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }
futures = "0.3.31"

# 序列化
serde = { version = "1.0.216", features = ["derive"] }
serde_json = "1.0.138"

# 错误处理
thiserror = "2.0.9"
anyhow = "1.0.95"

# 工具
chrono = { version = "0.4.39", features = ["serde"] }
uuid = { version = "1.11.0", features = ["v4", "serde"] }

[dev-dependencies]
criterion = { version = "0.6.0", features = ["async_tokio"] }
tokio-test = "0.4.4"
testcontainers = "0.23.1"
testcontainers-modules = { version = "0.11.4", features = ["elastic"] }
```

---

## Elasticsearch 语义约定

### OpenTelemetry 属性

| 属性名 | 类型 | 必需 | 描述 | 示例 |
|--------|------|------|------|------|
| `db.system` | string | ✅ | 数据库系统标识符 | `elasticsearch` |
| `db.name` | string | ✅ | 索引名称 | `products` |
| `db.operation` | string | ✅ | 操作类型 | `search`, `index`, `bulk` |
| `db.statement` | string | ❌ | 查询语句（可选） | `{"query": {"match": {...}}}` |
| `db.elasticsearch.cluster.name` | string | ❌ | 集群名称 | `production-cluster` |
| `db.elasticsearch.node.name` | string | ❌ | 节点名称 | `node-1` |
| `db.elasticsearch.path_parts.index` | string | ✅ | 索引名称 | `products` |
| `db.elasticsearch.path_parts.id` | string | ❌ | 文档 ID | `doc-123` |
| `http.request.method` | string | ✅ | HTTP 方法 | `GET`, `POST`, `PUT` |
| `http.response.status_code` | integer | ✅ | HTTP 状态码 | `200`, `404` |
| `net.peer.name` | string | ✅ | ES 服务器地址 | `localhost` |
| `net.peer.port` | integer | ✅ | ES 服务器端口 | `9200` |

### Rust 实现

```rust
use opentelemetry::KeyValue;
use tracing::Span;

/// Elasticsearch 追踪属性
#[derive(Debug, Clone)]
pub struct ElasticsearchAttributes {
    pub index: String,
    pub operation: String,
    pub document_id: Option<String>,
    pub query: Option<String>,
    pub cluster_name: Option<String>,
    pub node_url: String,
    pub http_method: String,
}

impl ElasticsearchAttributes {
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("db.system", "elasticsearch"),
            KeyValue::new("db.name", self.index.clone()),
            KeyValue::new("db.operation", self.operation.clone()),
            KeyValue::new("db.elasticsearch.path_parts.index", self.index.clone()),
            KeyValue::new("http.request.method", self.http_method.clone()),
        ];

        if let Some(doc_id) = &self.document_id {
            attrs.push(KeyValue::new("db.elasticsearch.path_parts.id", doc_id.clone()));
        }

        if let Some(query) = &self.query {
            attrs.push(KeyValue::new("db.statement", query.clone()));
        }

        if let Some(cluster) = &self.cluster_name {
            attrs.push(KeyValue::new("db.elasticsearch.cluster.name", cluster.clone()));
        }

        attrs
    }

    pub fn record_to_span(&self, span: &Span) {
        span.record("db.system", "elasticsearch");
        span.record("db.name", self.index.as_str());
        span.record("db.operation", self.operation.as_str());
        span.record("http.request.method", self.http_method.as_str());

        if let Some(doc_id) = &self.document_id {
            span.record("db.elasticsearch.path_parts.id", doc_id.as_str());
        }

        if let Some(query) = &self.query {
            span.record("db.statement", query.as_str());
        }
    }
}
```

---

## 客户端初始化

### 创建 Elasticsearch 客户端

```rust
use elasticsearch::{
    auth::Credentials,
    http::transport::{SingleNodeConnectionPool, TransportBuilder},
    Elasticsearch,
};
use tracing::{info, instrument};
use url::Url;

/// Elasticsearch 客户端配置
pub struct EsConfig {
    pub url: String,
    pub username: Option<String>,
    pub password: Option<String>,
    pub cluster_name: Option<String>,
}

/// 带追踪的 Elasticsearch 客户端
pub struct TracedEsClient {
    client: Elasticsearch,
    node_url: String,
    cluster_name: Option<String>,
}

impl TracedEsClient {
    /// 创建客户端
    #[instrument(skip(config), fields(
        db.system = "elasticsearch",
        node.url = %config.url
    ))]
    pub async fn new(config: EsConfig) -> Result<Self, elasticsearch::Error> {
        info!("Initializing Elasticsearch client");

        let url = Url::parse(&config.url)
            .map_err(|e| elasticsearch::Error::from(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                e,
            )))?;

        let conn_pool = SingleNodeConnectionPool::new(url);
        let mut transport_builder = TransportBuilder::new(conn_pool);

        // 添加认证
        if let (Some(username), Some(password)) = (&config.username, &config.password) {
            transport_builder = transport_builder
                .auth(Credentials::Basic(username.clone(), password.clone()));
        }

        let transport = transport_builder.build()?;
        let client = Elasticsearch::new(transport);

        // 测试连接
        let info_response = client.info().send().await?;
        let cluster_name = info_response
            .json::<serde_json::Value>()
            .await?
            .get("cluster_name")
            .and_then(|v| v.as_str())
            .map(String::from);

        info!(
            cluster_name = ?cluster_name,
            "Elasticsearch client initialized"
        );

        Ok(Self {
            client,
            node_url: config.url,
            cluster_name: cluster_name.or(config.cluster_name),
        })
    }

    pub fn client(&self) -> &Elasticsearch {
        &self.client
    }
}
```

---

## 索引操作追踪

### 索引管理

```rust
use serde_json::json;
use tracing::{error, info, instrument, warn};

impl TracedEsClient {
    /// 创建索引
    #[instrument(
        skip(self, settings),
        fields(
            db.system = "elasticsearch",
            db.operation = "create_index",
            db.elasticsearch.path_parts.index = %index_name,
            http.request.method = "PUT"
        )
    )]
    pub async fn create_index(
        &self,
        index_name: &str,
        settings: Option<serde_json::Value>,
        mappings: Option<serde_json::Value>,
    ) -> Result<(), elasticsearch::Error> {
        info!(index = %index_name, "Creating index");

        let mut body = json!({});

        if let Some(s) = settings {
            body["settings"] = s;
        }

        if let Some(m) = mappings {
            body["mappings"] = m;
        }

        let response = self
            .client
            .indices()
            .create(elasticsearch::indices::IndicesCreateParts::Index(index_name))
            .body(body)
            .send()
            .await?;

        let status = response.status_code();

        if response.status_code().is_success() {
            info!(
                index = %index_name,
                status = status.as_u16(),
                "Index created successfully"
            );
        } else {
            error!(
                index = %index_name,
                status = status.as_u16(),
                "Failed to create index"
            );
        }

        Ok(())
    }

    /// 删除索引
    #[instrument(
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "delete_index",
            db.elasticsearch.path_parts.index = %index_name,
            http.request.method = "DELETE"
        )
    )]
    pub async fn delete_index(&self, index_name: &str) -> Result<(), elasticsearch::Error> {
        info!(index = %index_name, "Deleting index");

        let response = self
            .client
            .indices()
            .delete(elasticsearch::indices::IndicesDeleteParts::Index(&[index_name]))
            .send()
            .await?;

        if response.status_code().is_success() {
            info!(index = %index_name, "Index deleted successfully");
        } else {
            warn!(index = %index_name, "Failed to delete index");
        }

        Ok(())
    }

    /// 检查索引是否存在
    #[instrument(
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "exists_index",
            db.elasticsearch.path_parts.index = %index_name,
            http.request.method = "HEAD"
        )
    )]
    pub async fn index_exists(&self, index_name: &str) -> Result<bool, elasticsearch::Error> {
        info!(index = %index_name, "Checking index existence");

        let response = self
            .client
            .indices()
            .exists(elasticsearch::indices::IndicesExistsParts::Index(&[index_name]))
            .send()
            .await?;

        let exists = response.status_code().is_success();

        info!(
            index = %index_name,
            exists = exists,
            "Index existence checked"
        );

        Ok(exists)
    }
}
```

---

## 文档操作追踪

### CRUD 操作

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Product {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    pub name: String,
    pub description: String,
    pub price: f64,
    pub category: String,
    pub in_stock: bool,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

impl TracedEsClient {
    /// 索引文档（创建或更新）
    #[instrument(
        skip(self, document),
        fields(
            db.system = "elasticsearch",
            db.operation = "index",
            db.elasticsearch.path_parts.index = %index_name,
            db.elasticsearch.path_parts.id = %document_id,
            http.request.method = "PUT",
            product.name = %document.name
        )
    )]
    pub async fn index_document(
        &self,
        index_name: &str,
        document_id: &str,
        document: &Product,
    ) -> Result<String, elasticsearch::Error> {
        info!(
            index = %index_name,
            doc_id = %document_id,
            "Indexing document"
        );

        let response = self
            .client
            .index(elasticsearch::IndexParts::IndexId(index_name, document_id))
            .body(document)
            .send()
            .await?;

        let status = response.status_code();
        let json: serde_json::Value = response.json().await?;

        let result = json["result"].as_str().unwrap_or("unknown").to_string();

        info!(
            index = %index_name,
            doc_id = %document_id,
            result = %result,
            status = status.as_u16(),
            "Document indexed"
        );

        Ok(result)
    }

    /// 获取文档
    #[instrument(
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "get",
            db.elasticsearch.path_parts.index = %index_name,
            db.elasticsearch.path_parts.id = %document_id,
            http.request.method = "GET"
        )
    )]
    pub async fn get_document(
        &self,
        index_name: &str,
        document_id: &str,
    ) -> Result<Option<Product>, elasticsearch::Error> {
        info!(
            index = %index_name,
            doc_id = %document_id,
            "Getting document"
        );

        let response = self
            .client
            .get(elasticsearch::GetParts::IndexId(index_name, document_id))
            .send()
            .await?;

        if !response.status_code().is_success() {
            if response.status_code() == 404 {
                info!(
                    index = %index_name,
                    doc_id = %document_id,
                    "Document not found"
                );
                return Ok(None);
            }
            return Err(response.error_for_status_code().unwrap_err());
        }

        let json: serde_json::Value = response.json().await?;
        let source = json["_source"].clone();
        let product: Product = serde_json::from_value(source)
            .map_err(|e| elasticsearch::Error::from(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                e,
            )))?;

        info!(
            index = %index_name,
            doc_id = %document_id,
            "Document retrieved"
        );

        Ok(Some(product))
    }

    /// 更新文档
    #[instrument(
        skip(self, update_doc),
        fields(
            db.system = "elasticsearch",
            db.operation = "update",
            db.elasticsearch.path_parts.index = %index_name,
            db.elasticsearch.path_parts.id = %document_id,
            http.request.method = "POST"
        )
    )]
    pub async fn update_document(
        &self,
        index_name: &str,
        document_id: &str,
        update_doc: serde_json::Value,
    ) -> Result<(), elasticsearch::Error> {
        info!(
            index = %index_name,
            doc_id = %document_id,
            "Updating document"
        );

        let body = json!({
            "doc": update_doc
        });

        let response = self
            .client
            .update(elasticsearch::UpdateParts::IndexId(index_name, document_id))
            .body(body)
            .send()
            .await?;

        if response.status_code().is_success() {
            info!(
                index = %index_name,
                doc_id = %document_id,
                "Document updated successfully"
            );
        } else {
            error!(
                index = %index_name,
                doc_id = %document_id,
                "Failed to update document"
            );
        }

        Ok(())
    }

    /// 删除文档
    #[instrument(
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "delete",
            db.elasticsearch.path_parts.index = %index_name,
            db.elasticsearch.path_parts.id = %document_id,
            http.request.method = "DELETE"
        )
    )]
    pub async fn delete_document(
        &self,
        index_name: &str,
        document_id: &str,
    ) -> Result<bool, elasticsearch::Error> {
        info!(
            index = %index_name,
            doc_id = %document_id,
            "Deleting document"
        );

        let response = self
            .client
            .delete(elasticsearch::DeleteParts::IndexId(index_name, document_id))
            .send()
            .await?;

        let json: serde_json::Value = response.json().await?;
        let result = json["result"].as_str().unwrap_or("not_found");

        let deleted = result == "deleted";

        if deleted {
            info!(
                index = %index_name,
                doc_id = %document_id,
                "Document deleted"
            );
        } else {
            warn!(
                index = %index_name,
                doc_id = %document_id,
                result = %result,
                "Document not deleted"
            );
        }

        Ok(deleted)
    }
}
```

---

## 搜索操作追踪

### 全文搜索

```rust
impl TracedEsClient {
    /// 搜索文档
    #[instrument(
        skip(self, query),
        fields(
            db.system = "elasticsearch",
            db.operation = "search",
            db.elasticsearch.path_parts.index = %index_name,
            http.request.method = "POST"
        )
    )]
    pub async fn search(
        &self,
        index_name: &str,
        query: serde_json::Value,
        size: Option<i64>,
    ) -> Result<Vec<Product>, elasticsearch::Error> {
        info!(index = %index_name, "Searching documents");

        let query_str = serde_json::to_string(&query)
            .unwrap_or_else(|_| "{}".to_string());

        // 记录查询语句到 Span
        tracing::Span::current().record("db.statement", &query_str);

        let mut search_builder = self
            .client
            .search(elasticsearch::SearchParts::Index(&[index_name]))
            .body(json!({
                "query": query
            }));

        if let Some(s) = size {
            search_builder = search_builder.size(s);
        }

        let response = search_builder.send().await?;

        let json: serde_json::Value = response.json().await?;

        let hits = json["hits"]["hits"].as_array().unwrap_or(&vec![]);
        let mut products = Vec::new();

        for hit in hits {
            if let Ok(product) = serde_json::from_value::<Product>(hit["_source"].clone()) {
                products.push(product);
            }
        }

        let total = json["hits"]["total"]["value"].as_i64().unwrap_or(0);

        info!(
            index = %index_name,
            results_count = products.len(),
            total_hits = total,
            "Search completed"
        );

        Ok(products)
    }

    /// Match 查询
    #[instrument(
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "search",
            query.type = "match",
            query.field = %field,
            query.value = %value
        )
    )]
    pub async fn match_query(
        &self,
        index_name: &str,
        field: &str,
        value: &str,
    ) -> Result<Vec<Product>, elasticsearch::Error> {
        info!(
            field = %field,
            value = %value,
            "Executing match query"
        );

        let query = json!({
            "match": {
                field: value
            }
        });

        self.search(index_name, query, Some(100)).await
    }

    /// Term 查询
    #[instrument(
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "search",
            query.type = "term",
            query.field = %field
        )
    )]
    pub async fn term_query(
        &self,
        index_name: &str,
        field: &str,
        value: &str,
    ) -> Result<Vec<Product>, elasticsearch::Error> {
        info!(
            field = %field,
            value = %value,
            "Executing term query"
        );

        let query = json!({
            "term": {
                field: value
            }
        });

        self.search(index_name, query, Some(100)).await
    }

    /// Range 查询
    #[instrument(
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "search",
            query.type = "range",
            query.field = %field
        )
    )]
    pub async fn range_query(
        &self,
        index_name: &str,
        field: &str,
        gte: Option<f64>,
        lte: Option<f64>,
    ) -> Result<Vec<Product>, elasticsearch::Error> {
        info!(
            field = %field,
            gte = ?gte,
            lte = ?lte,
            "Executing range query"
        );

        let mut range = json!({});

        if let Some(g) = gte {
            range["gte"] = json!(g);
        }

        if let Some(l) = lte {
            range["lte"] = json!(l);
        }

        let query = json!({
            "range": {
                field: range
            }
        });

        self.search(index_name, query, Some(100)).await
    }

    /// Bool 查询（组合查询）
    #[instrument(
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "search",
            query.type = "bool"
        )
    )]
    pub async fn bool_query(
        &self,
        index_name: &str,
        must: Vec<serde_json::Value>,
        should: Vec<serde_json::Value>,
        must_not: Vec<serde_json::Value>,
    ) -> Result<Vec<Product>, elasticsearch::Error> {
        info!("Executing bool query");

        let query = json!({
            "bool": {
                "must": must,
                "should": should,
                "must_not": must_not
            }
        });

        self.search(index_name, query, Some(100)).await
    }
}
```

---

## 批量操作追踪

### Bulk API

```rust
use elasticsearch::BulkParts;

impl TracedEsClient {
    /// 批量索引文档
    #[instrument(
        skip(self, documents),
        fields(
            db.system = "elasticsearch",
            db.operation = "bulk",
            db.elasticsearch.path_parts.index = %index_name,
            http.request.method = "POST",
            batch.size = documents.len()
        )
    )]
    pub async fn bulk_index(
        &self,
        index_name: &str,
        documents: Vec<(String, Product)>,
    ) -> Result<usize, elasticsearch::Error> {
        info!(
            index = %index_name,
            batch_size = documents.len(),
            "Bulk indexing documents"
        );

        let mut body: Vec<serde_json::Value> = Vec::new();

        for (doc_id, product) in documents {
            // 索引操作元数据
            body.push(json!({
                "index": {
                    "_id": doc_id
                }
            }));

            // 文档数据
            body.push(serde_json::to_value(&product).unwrap());
        }

        let response = self
            .client
            .bulk(BulkParts::Index(index_name))
            .body(body)
            .send()
            .await?;

        let json: serde_json::Value = response.json().await?;

        let errors = json["errors"].as_bool().unwrap_or(false);
        let items = json["items"].as_array().unwrap_or(&vec![]);
        let successful_count = items.len();

        if errors {
            warn!(
                index = %index_name,
                "Some bulk operations failed"
            );
        }

        info!(
            index = %index_name,
            successful_count = successful_count,
            "Bulk indexing completed"
        );

        Ok(successful_count)
    }

    /// 批量删除文档
    #[instrument(
        skip(self, document_ids),
        fields(
            db.system = "elasticsearch",
            db.operation = "bulk",
            db.elasticsearch.path_parts.index = %index_name,
            batch.size = document_ids.len()
        )
    )]
    pub async fn bulk_delete(
        &self,
        index_name: &str,
        document_ids: Vec<String>,
    ) -> Result<usize, elasticsearch::Error> {
        info!(
            index = %index_name,
            batch_size = document_ids.len(),
            "Bulk deleting documents"
        );

        let mut body: Vec<serde_json::Value> = Vec::new();

        for doc_id in document_ids {
            body.push(json!({
                "delete": {
                    "_id": doc_id
                }
            }));
        }

        let response = self
            .client
            .bulk(BulkParts::Index(index_name))
            .body(body)
            .send()
            .await?;

        let json: serde_json::Value = response.json().await?;
        let items = json["items"].as_array().unwrap_or(&vec![]);

        info!(
            index = %index_name,
            deleted_count = items.len(),
            "Bulk deletion completed"
        );

        Ok(items.len())
    }
}
```

---

## 聚合查询追踪

### 聚合分析

```rust
impl TracedEsClient {
    /// 聚合查询
    #[instrument(
        skip(self, aggregations),
        fields(
            db.system = "elasticsearch",
            db.operation = "search",
            query.type = "aggregation",
            db.elasticsearch.path_parts.index = %index_name
        )
    )]
    pub async fn aggregate(
        &self,
        index_name: &str,
        aggregations: serde_json::Value,
    ) -> Result<serde_json::Value, elasticsearch::Error> {
        info!(index = %index_name, "Executing aggregation query");

        let body = json!({
            "size": 0,
            "aggs": aggregations
        });

        let response = self
            .client
            .search(elasticsearch::SearchParts::Index(&[index_name]))
            .body(body)
            .send()
            .await?;

        let json: serde_json::Value = response.json().await?;
        let aggs = json["aggregations"].clone();

        info!(
            index = %index_name,
            "Aggregation completed"
        );

        Ok(aggs)
    }

    /// Terms 聚合（分组统计）
    #[instrument(
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "aggregation",
            aggregation.type = "terms",
            aggregation.field = %field
        )
    )]
    pub async fn terms_aggregation(
        &self,
        index_name: &str,
        field: &str,
        size: i64,
    ) -> Result<Vec<(String, i64)>, elasticsearch::Error> {
        info!(
            field = %field,
            size = size,
            "Executing terms aggregation"
        );

        let aggs = json!({
            "terms_agg": {
                "terms": {
                    "field": field,
                    "size": size
                }
            }
        });

        let result = self.aggregate(index_name, aggs).await?;

        let buckets = result["terms_agg"]["buckets"].as_array().unwrap_or(&vec![]);
        let mut results = Vec::new();

        for bucket in buckets {
            if let (Some(key), Some(count)) = (bucket["key"].as_str(), bucket["doc_count"].as_i64()) {
                results.push((key.to_string(), count));
            }
        }

        info!(
            results_count = results.len(),
            "Terms aggregation completed"
        );

        Ok(results)
    }

    /// Stats 聚合（统计分析）
    #[instrument(
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "aggregation",
            aggregation.type = "stats",
            aggregation.field = %field
        )
    )]
    pub async fn stats_aggregation(
        &self,
        index_name: &str,
        field: &str,
    ) -> Result<serde_json::Value, elasticsearch::Error> {
        info!(field = %field, "Executing stats aggregation");

        let aggs = json!({
            "stats_agg": {
                "stats": {
                    "field": field
                }
            }
        });

        let result = self.aggregate(index_name, aggs).await?;

        Ok(result["stats_agg"].clone())
    }
}
```

---

## 性能优化

### 1. 批量操作优化

```rust
use std::time::Duration;
use tokio::sync::mpsc;
use tokio::time::interval;

pub async fn batched_indexer(
    client: std::sync::Arc<TracedEsClient>,
    index_name: String,
    mut rx: mpsc::Receiver<(String, Product)>,
) {
    let mut batch = Vec::new();
    let mut interval_timer = interval(Duration::from_millis(100));
    const MAX_BATCH_SIZE: usize = 500;

    loop {
        tokio::select! {
            Some(item) = rx.recv() => {
                batch.push(item);

                if batch.len() >= MAX_BATCH_SIZE {
                    index_batch(&client, &index_name, &mut batch).await;
                }
            }
            _ = interval_timer.tick() => {
                if !batch.is_empty() {
                    index_batch(&client, &index_name, &mut batch).await;
                }
            }
        }
    }
}

async fn index_batch(
    client: &TracedEsClient,
    index_name: &str,
    batch: &mut Vec<(String, Product)>,
) {
    if batch.is_empty() {
        return;
    }

    let documents = batch.drain(..).collect();

    match client.bulk_index(index_name, documents).await {
        Ok(count) => {
            info!(indexed_count = count, "Batch indexed successfully");
        }
        Err(e) => {
            error!(error = %e, "Failed to index batch");
        }
    }
}
```

### 2. 并发搜索

```rust
use futures::stream::{self, StreamExt};

pub async fn concurrent_search(
    client: std::sync::Arc<TracedEsClient>,
    index_name: &str,
    queries: Vec<serde_json::Value>,
    concurrency: usize,
) -> Vec<Vec<Product>> {
    stream::iter(queries)
        .map(|query| {
            let client = Arc::clone(&client);
            let index = index_name.to_string();

            async move {
                client.search(&index, query, Some(100)).await.unwrap_or_default()
            }
        })
        .buffer_unordered(concurrency)
        .collect()
        .await
}
```

---

## 最佳实践

### 1. 索引映射定义

```rust
pub fn product_mapping() -> serde_json::Value {
    json!({
        "properties": {
            "name": {
                "type": "text",
                "analyzer": "standard"
            },
            "description": {
                "type": "text",
                "analyzer": "standard"
            },
            "price": {
                "type": "double"
            },
            "category": {
                "type": "keyword"
            },
            "in_stock": {
                "type": "boolean"
            },
            "created_at": {
                "type": "date"
            }
        }
    })
}
```

### 2. 错误重试策略

```rust
use std::time::Duration;
use tokio::time::sleep;

pub async fn retry_es_operation<F, Fut, T>(
    operation: F,
    max_retries: u32,
) -> Result<T, elasticsearch::Error>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = Result<T, elasticsearch::Error>>,
{
    let mut retries = 0;

    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) if retries < max_retries => {
                warn!(
                    error = %e,
                    retry = retries + 1,
                    "ES operation failed, retrying"
                );

                retries += 1;
                sleep(Duration::from_millis(100 * 2u64.pow(retries))).await;
            }
            Err(e) => return Err(e),
        }
    }
}
```

---

## 完整示例

### main.rs

```rust
use anyhow::Result;
use opentelemetry::global;
use opentelemetry_sdk::{runtime, trace as sdktrace, Resource};
use opentelemetry_otlp::WithExportConfig;
use tracing::info;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OpenTelemetry
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("http://localhost:4318/v1/traces"),
        )
        .with_trace_config(
            sdktrace::Config::default()
                .with_resource(Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", "elasticsearch-demo"),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    info!("Starting Elasticsearch OTLP tracing demo");

    // 创建客户端
    let config = EsConfig {
        url: "http://localhost:9200".to_string(),
        username: None,
        password: None,
        cluster_name: None,
    };

    let client = TracedEsClient::new(config).await?;

    // 创建索引
    let index_name = "products";
    if !client.index_exists(index_name).await? {
        client
            .create_index(index_name, None, Some(product_mapping()))
            .await?;
    }

    // 索引文档
    let product = Product {
        id: None,
        name: "Laptop".to_string(),
        description: "High-performance laptop".to_string(),
        price: 1299.99,
        category: "electronics".to_string(),
        in_stock: true,
        created_at: chrono::Utc::now(),
    };

    client
        .index_document(index_name, "prod-1", &product)
        .await?;

    // 搜索文档
    let results = client
        .match_query(index_name, "name", "laptop")
        .await?;

    info!(results_count = results.len(), "Search completed");

    // 关闭追踪
    global::shutdown_tracer_provider();

    Ok(())
}
```

---

## 总结

本文档提供了 Elasticsearch 在 Rust 1.90 环境下的完整 OpenTelemetry 集成方案：

1. ✅ **索引管理**: 创建、删除、检查索引
2. ✅ **文档操作**: CRUD 完整实现
3. ✅ **搜索功能**: Match, Term, Range, Bool 查询
4. ✅ **批量操作**: Bulk API 高效处理
5. ✅ **聚合分析**: Terms, Stats 聚合
6. ✅ **性能优化**: 批处理、并发搜索
7. ✅ **最佳实践**: 映射定义、错误重试

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT
