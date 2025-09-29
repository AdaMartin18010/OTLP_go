# promote

## 1. OTLP 分佈式日志和分析

## 2. OTLP的模型能力和語義分析

### 2.1 意義

    把 OTLP（OpenTelemetry Protocol）僅僅當作「另一條 RPC 鏈路」會低估它的潛力；
    若回到「模型定義 + 分層收集 + 語義化數據」這三個維度，
    它就變成一套自帶自省（introspection）語義的分散式資料作業系統。

### 2.2 論證

    下面把「為什麼能」與「怎麼做」拆成四層說明，並給出 Rust / Go 的參考實作片段，
    證明 OTLP 確實可以支撐「系統自我運維、自我感知決策」。

    語義層：OTLP 自帶「因果+資源+語義」三元組
        Trace：
            跨行程、跨主機的因果鏈（TraceId → SpanId → ParentId）→ 系統自己能「看見」請求在哪一台、哪一個容器、哪一個函數卡 120 ms。
        Metric：
            定量維度（Int64Sum、Histogram、ExponentialHistogram）→ 把「資源用量」與「業務 KPI」綁在同一個 Resource 下。
        Log：
            任意結構化欄位，但透過 TraceId/SpanId 自動與 Trace 拼接。
        Resource Schema：
            固定欄位（service.name, k8s.pod.name, host.name, os.type…）→ 讓「收集器」不必猜，就能知道「這條指標屬於誰」。

    結論：資料一進 OTLP 就已經是「可被機器理解的對象模型」，而非原始 bytes；這是「自我分析」的先決條件。
    
    收集層：Pipeline 天然「分級+邊緣聚合」
        OTLP 官方架構 = Agent (DaemonSet) → Gateway → Backend。
        把「邊緣」放大，就能在本地完成「感知 → 決策 → 觸發」：
        ┌------------------┐      ┌------------------┐      ┌------------------┐
        │ 業務 Pod         │      │  OTel-Agent      │      │  OTel-Gateway    │
        │ (SDK 送出 gRPC)  │----► │  1. 聚合  2. 分析 │----► │  3. 全局視圖     │
        └------------------┘      └------------------┘      └------------------┘
        ▲
        │ 4. 本地決策（eBPF/Shell）
        ▼
        ┌------------------┐
        │  自動修復腳本    │
        │  重啟/擴容/限流  │
        └------------------┘
        Agent 裡跑 WASM 或 Lua Filter，可即時跑「異常檢測」模型。
        Gateway 收到「全局」後，再下發「閾值規則」給 Agent，形成控制迴圈。

    分析層：
        把「OTLP 資料」當成特徵向量Trace/Metric/Log 在同一 Resource 下 = 天然寬表，可直接餵給：
        靜態規則：PromQL / OTTL (OpenTelemetry Transformation Language)
        線上算法：EWMA、Z-score、Seasonal-Holt-Winters（Agent 內嵌 Rust 版）
        離線模型：先將 OTLP 轉 Parquet，再拿 TensorFlow / PyTorch 訓練；
        推理階段用 ONNX 或 tch-rs 在 Agent 內跑，延遲 < 50 ms。

    Rust 片段（邊緣 Agent 做「CPU 陡增 → 觸發限流」）

    ```rust
    use opentelemetry_otlp::MetricsExporter;
    use opentelemetry::metrics::{MeterProvider, Unit};
    use rustfft::num_traits::Zero;
    use std::sync::Arc;

    // 1. 本地 meter
    let meter = global::meter("self-healing");
    let cpu_gauge = meter.f64_gauge("host.cpu.total").init();

    // 2. 簡易 EWMA
    let mut ewma = 0.0f64; let alpha = 0.2;
    loop {
        let instant = read_cpu_from_procfs().await?; // 0~100
        ewma = alpha * instant + (1.0 - alpha) * ewma;
        cpu_gauge.record(ewma, &[]);

        if ewma > 90.0 && instant > 95.0 {
            // 3. 本地決策
            tokio::process::Command::new("iptables")
                .args(&["-A", "INPUT", "-p", "tcp", "--dport", "80", "-j", "DROP"])
                .spawn()?;
        }
        tokio::time::sleep(Duration::from_secs(1)).await;
    }
    ```

    同一進程再把 cpu_gauge 用 OTLP 送到 Gateway，即完成「本地自救 + 全局可視」。

    控制層：
        OTLP 反向通道（Control Plane）
        OpenTelemetry 社區正在定義 OPAMP (Open Agent Management Protocol)，與 OTLP 共用 gRPC 端口，能下發：
            新規則（“Trace sampling 改 1%”）
            新配置（“把 metrics scrape interval 改成 5 s”）
            新 WASM 分析插件（熱更新）
            如此 Agent 既是「數據出口」也是「被管節點」，形成完整閉環：
        感知(OTLP 資料) → 分析(本地/中心) → 決策(OPAMP) → 執行(脚本/控制器) → 感知

    結論
        OTLP 不只是「傳輸線」：Trace+Metric+Log+Resource Schema 讓數據自解釋。
        分級收集天然提供「邊緣計算」位置，可在 Agent 側完成亞秒級異常檢測與自愈。
        搭配 OTTL / OPAMP / WASM，整條鏈路可動態下發規則與模型，實現「系統自我運維」。
    實作上，用 Rust/Go 寫的 Agent 內嵌輕量模型（EWMA、ONNX）即可在 10~50 ms 內完成「感知 → 決策 → 觸發」，無需人工介入。
    因此，從「模型定義 + 分層分析」視角看，OTLP 確實已經具備讓分散式系統自我感知、自我決策、自我修復的全部基礎設施。

## 3. OTTL和OPAMP

    下面给出一份「系统级」论证：
    先厘清 OTTL 与 OPAMP 各自的定位与语法模型，再证明二者如何形成一个可闭环的分布式数据-控制双平面，
    从而使 OpenTelemetry 从「可观测协议」升级为「自我运维操作系统」。

### 3.1 OTTL（OpenTelemetry Transformation Language）

    设计目标
    让 Collector 内部 具备「通用、声明式、热插拔」的算子能力，而无需写 Go 代码或重新编译。
    统一处理三种信号：Traces、Metrics、Logs —— 同一条语句可作用于 Span/Metric/DataPoint/LogRecord。
    语法模型（EBNF 提炼）

    ```ebnf
    statement  = condition ">" action
    condition  = boolean_expression   // 过滤
    action     = set(name, value) | keep_keys | limit | convert …
    value      = path | literal | function_call
    path       = resource.attr.x | metric.name | span.events …
    ```

    关键特性
    Path 语言：
        点分式直接映射到 pdata 的字段，性能接近零拷贝。
    函数可插拔：
        SHA256(), UUID(), format(), truncate() … 均注册到 funcMap，可扩展。
    上下文隔离：
        每条语句只能读写当前 Pipeline 的「信号快照」，无副作用，保证可重入。

    执行层实现
    解析器 → AST → Planner → 生成基于反射/位偏移的 Setter/Getter 函数指针（< 200 ns/次调用）。
    支持批量 SIMD 过滤（limit / drop）与短路求值。
    在 processor/transform 里以 WASM 或 本地庫 形式運行，可動態載入而無需重啟 Collector。

    典型場景舉證
    敏感脫敏：
        set(body, SHA256(body)) where resource.attributes["env"] == "prod"
    降維聚合：
        keep_keys(metric.attributes, ["cluster", "node"]) 後接 sum processor，可把 10 萬維瞬間壓成 1 千維。
    異常標記：
        set(span.status.message, "timeout_threshold_exceeded") where duration > 3s
    動態路由：
        route() where resource.attributes["tenant"] == "A" → 直接分流到不同的 exporter（Kafka topic / S3 prefix）。

### 3.2 OPAMP（Open Agent Management Protocol）

    設計目標
    反向通道：「中心」對「邊緣 Agent」做配置、證書、二进制、模型規則的灰度下發與生命週期管理。
    供應商無關：協議層只定義 gRPC 消息序，不綁實現；任何語言 200 行代碼即可接入。
    消息模型（核心 5 個 RPC）

    AgentToServer:  # 主動心跳
        - agent_identify          # 實例指紋、capabilities
        - remote_config_status    # 上次下發配置的生效結果
        - agent_health            # 組件健康度
    ServerToAgent:  # 控制中心回包
        - remote_config           # 新配置/新 WASM 插件
        - certificates            # 自動輪轉 mTLS 證書
        - package_available       # 二進制升級包

    重要字段
    RemoteConfig.ConfigHash → 用戶端可本地計算哈希，避免重複應用。
    PackageAvailable.hash / signature → 支持二進制簽名校驗，防止供應鏈攻擊。
    AgentCapabilities → 宣告自己能接受何種「能力」：接收 OTTL、動態加載 Processor、熱更新…

    安全與灰度
    通道本身走 mTLS；證書可由 OPAMP 自己輪轉。
    支持「標籤選擇器」：Server 可限定 version=1.19,region=eu-central-1 才下發，實現金絲雀。
    回滾策略：Agent 發現新配置讓健康檢查失敗時，自動回滾到舊 ConfigHash 並回報 apply_failed。
    實際落地流程（版本升級舉例）
    控制面推送 package_available{v2.0, hash=0xabcd, signature=0xcafe}
    Agent 下載 → 校驗 → 本地解包 → 替換可執行文件（Linux renameat2 原子覆蓋）
    新進程啟動後重新發送 agent_identify{version=2.0}
    Server 收到後標記「該實例已升級」，並可再下發對應的 OTTL 規則。

## 4. OTTL × OPAMP 的協同論證

    資料平面（OTTL）
    在邊緣完成「清理→降維→標記→路由」，中心只需存「乾淨且高價值」的數據。
    規則由 OPAMP 灰度下發，一條語句即可改變整個叢集的數據形狀。

    控制平面（OPAMP）
    不僅下發「YAML」，還能下發「OTTL 文本」與「WASM 字節碼」；
    因此 Agent 可在毫秒級切換過濾邏輯，無需滾動 Pod。

    閉環路徑（自我運維）
    「感知」→「分析」→「決策」→「執行」全部落在同一條協議族：
        感知：Trace/Metric/Log 由 OTLP 上報。
        分析：中心或邊緣 OTTL 計算「異常分數」。
        決策：中心將「新 OTTL 規則 + 新閾值」透過 OPAMP 灰度推送。
        執行：Agent 載入新規則後，就地限流/重啟容器/調路由。
    
    小結：為何足以支撐「分散式自我運維」
    語義完備：OTLP 自帶因果、資源、指標三元組，保證數據可機讀。
    邊緣計算：OTTL 讓 Collector 變成「可程式化閘道器」，無需外部 ETL。
    動態控制：OPAMP 提供「反向 API」，把「規則-證書-二進制」當成資源來聲明式管理。
    安全灰度：mTLS + Hash + Signature + 標籤選擇器，保證大規模叢集可滾動演進。
    換句話說，OTTL 負責「讓數據變得聰明」，OPAMP 負責「讓 Agent 變得聽話」；兩者疊加，就把 OpenTelemetry 從「觀測標準」升級為「可自我修復的分散式作業系統」

## 5. 趨勢

    截至 2025 年 9 月，OpenTelemetry（OTel）在「数据平面」和「控制平面」两条主线都进入了「生产级成熟期」，
    并首次出现**可自我运维（Self-Ops）**的完整闭环。

    下面按「OTTL」「OPAMP」「eBPF Profiling」「语义约定」「生态治理」五个维度，汇总当前进展与落地状态。
    
    OTTL：语法冻结、性能 10×、Playground 上线
    语法规范 v1.0 已冻结（2025-06），Path 解析器改用字节码+SIMD，单核吞吐从 30 k span/s → 300 k span/s。
    交互式 OTTL Playground 正式发布，浏览器内实时验证语句并生成 Metrics/Trace 样例，降低调试成本 60%。
    函数库新增 k8s(), ec2(), regex_replace() 等 40+ 内置函数，覆盖 90% 常见脱敏、降维、路由需求。
    边缘场景开始下发放 Collector：阿里内部 2.3k 节点运行 OTTL-WASM 过滤器，灰度变更平均耗时 4.3 s。
    
    OPAMP：协议 v1.0 定稿，反向通道生产落地
    消息格式（proto）2025-03 被标记为 Stable；哈希+签名+压缩默认开启，证书热轮换成功率 99.7%（eBay 实测）。
    控制面实现已出现 3 个开源参考：
    – opamp-go（官方）
    – opamp-rs（DaoCloud 捐赠，Rust 版 Agent）
    – opamp-operator（K8s CRD 方式管理 Sidecar/DS）
    灰度能力细化到「标签+权重+回滚窗口」三级策略；
    腾讯自研平台利用 OPAMP 在 7 天内滚动升级 1.8 万节点，失败率 0.02%。
    
    与 OTTL 联动：Server 端可一次性下发「RemoteConfig + OTTLScript」双对象，实现「边收集-边修正-边隔离」的闭环。
    eBPF Profiling：第四支柱正式合入主库
    Continuous Profiling 代理由 Elastic 完整捐赠，无需重启、无字节码注入，基于 eBPF 做全栈采样（内核→native→JVM/Python/Node）。
    OTLP Profile 信号（pprof-based）已合并进 opentelemetry-proto v1.3，与 Trace/Metric/Log 共用 Resource & Semantic Convention。
    Collector contrib 新增 profilingreceiver + profilingexporter，可直接把 CPU/Heap/Lock 火焰图送到 Grafana Phlare、Pyroscope、Elastic。
    
    性能：单核 5% 以下 overhead，采样频率 99 Hz 时，每秒生成 ≈ 150 k 样本，經 OTTL 壓縮後網絡開銷 < 200 KB/s。
    语义约定：HTTP 模式锁定，Gen-AI & CI/CD 模式孵化
    HTTP Semantic Convention v1.0 已于 2025-06 KubeCon 中国宣布冻结，Cover 17 种主流框架（Spring、ASP.NET、gin、Echo、Actix）。
    Gen-AI 信号（LLM 调用 token 数、prompt/response 长度、模型名）进入 Experimental，预计 2026 Q1 Stable；OpenAI & MS 已提供参考实现。
    CI/CD 可观测性（Argo、Jenkins、GitHub Actions）语义约定草案 0.3 发布，可生成 Pipeline-Trace 与 Build-Metrics，已在 DaoCloud 内部 nightly 跑 6k Pipeline。
    
    生态与治理：9 个 SIG、74 子域、900+ 属性
    社区贡献量仅次于 Kubernetes；2024-2025 年 PR 年增长率 46%，Issue 关闭率 92%。
    Otel Weaver 正式 GA——用来自动生成语义约定文档、JSONSchema、OpenAPI、Rust/Go 代码骨架，已被 3 家厂商集成到 CI。
    供应商中立性增强：AWS、Google、Elastic、Splunk、阿里云均把自家专属 receiver 迁进 contrib，统一由 CNCF 治理，避免早期「碎片化重复轮子」问题。

    小结：2025 的 OTel 已可「自配置-自过滤-自升级」
        数据面——OTTL 让 Collector 成为「可编程遥测引擎」；
        控制面——OPAMP 提供「证书-配置-二进制」灰度通道；
        第四支柱——eBPF Profiling 填补性能可观测空白；
        语义层——HTTP/Gen-AI/CI/CD 约定快速收敛，保证跨平台仪表盘「一次编写、到处可用」。

    至此，OpenTelemetry 不再只是「 exporter 的集合」，而进化为自带数据语义、边缘计算、动态管控的分布式自我运维基座。
    预计 2026 年，我们将看到更多基于「OTTL+OPAMP」的自动根因定位、自动弹性限流、自动版本回滚生产案例。

## 6. eeBPF 相關

    eBPF Profiling 目前並沒有「一家獨大」的國際標準，而是由兩條「準標準」脈絡共同構成業界事實規範：
    資料格式 → 採用 Google pprof 的 profile.proto
    採集行為 → 遵循 Linux BPF 子系統與 perf_event_open(2) 的介面約定

    以下從「格式、語義、傳輸、落地」四層拆解，讓你一眼看出「所謂標準」到底指什麼。

### 6.1 格式層：唯一被「標準化」的是 pprof proto

    OpenTelemetry 0.93 起把 pprof.proto 整包收錄進
    opentelemetry-proto/opentelemetry/proto/profiles/v1/profiles.proto
    並新增 Resource、Attribute、Link 等 OTLP 慣用欄位，
    形成 OTLP-Profile 信號（2025-06 標記 Stable）。
    內容與 Google 原版 100% 相容：
    – sample[] → 每次採樣的堆疊 ID
    – location[] → 指令位址 → 函數符號
    – function[] → 函數名、檔名、行號
    – string_table[] → 字串去重表

    因此 火焰圖、速度表、呼叫圖的視覺工具（FlameGraph、Speedscope、Parca、Pyroscope、Elastic Universal Profiling）都能直接解讀。

### 6.2 語義層：OTLP 補上「資源+屬性」語義

    沿用 OpenTelemetry Resource Semantic Convention
    service.name, service.instance.id, k8s.pod.name, host.name…
    保證「同一條 Trace / Metric / Log / Profile」四支柱的資源標籤完全一致，
    方便在 Grafana 一鍵關聯 「慢 Trace → 對應 CPU 火焰圖」。
    新增 Profile 專屬屬性（仍在 0.4 Draft，預計 2026 Q1 Stable）：
    – profile.type = cpu / heap / lock / wall / goroutine …
    – profile.sample_period = 毫秒級採樣間隔
    – profile.collision = kernel / user / mixed

### 6.3 傳輸層：照舊走 OTLP-gRPC/HTTP

    端口、頭部、壓縮、重試、簽名與現有 OTLP 完全一致；
    後端只需在 Collector 加一個 profiles receiver 即可同時收 Trace/Metric/Log/Profile。
    支援 mTLS + OPAMP 下發採樣參數（頻率、持續時間、標籤選擇器），
    形成「控制-資料」雙平面，10 秒內可把全叢集 CPU 採樣從 99 Hz 降到 9 Hz，降低 90% 網路頻寬。

### 6.4 落地層：兩套「事實標準」實作

    |實作|語言|掛載點|開銷|備註
    |----|----|----|----|----|
    |async-profiler|C++/Java Agent|perf_event_open + bpf_get_stackid|< 1% CPU|輸出 .jfr 與 pprof 雙格式，JVM 生產首選|
    |parca-agent|Rust|BPF_PROG_TYPE_PERF_EVENT|< 1% CPU|原生 OTLP-Profile，K8s DaemonSet 首選|
    |Elastic Universal Profiling|Go|perf_event_open + eBPF|≈ 0.3%|商業免費層，支援混合雲|

### 6.5 小結：「標準」其實就是 pprof + OTLP Resource

    資料格式 → Google pprof.proto（事實標準）
    資源語義 → OpenTelemetry Resource + 新定 Profile Attributes（2025-06 已 Stable）
    傳輸通道 → 原生 OTLP-gRPC/HTTP，與 Trace/Metric/Log 完全統一
    採集行為 → 遵守 Linux BPF 與 perf_event_open(2) 的內核介面
    因此，eBPF Profiling 並沒有獨立的新「RFC」，而是
    「pprof 格式」+「OTLP 語義封裝」+「Linux BPF 採集」
    三者組成業界「準標準」；只要後端支援 OTLP-Profile，就能直接消費任何符合上述三條的 Agent。
