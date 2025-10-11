/**
 * OpenTelemetry Collector Configuration Generator
 * Version: 1.0.0
 * Based on: OTLP v1.3.0, Collector v0.113.0
 */

// Form submission handler
document.getElementById('configForm').addEventListener('submit', function(e) {
    e.preventDefault();
    generateConfig();
});

function generateConfig() {
    const formData = getFormData();
    const config = buildConfig(formData);
    const deployCommands = buildDeployCommands(formData);
    const validateScript = buildValidateScript(formData);
    
    // Display results
    document.getElementById('configOutput').textContent = config;
    document.getElementById('deployOutput').textContent = deployCommands;
    document.getElementById('validateOutput').textContent = validateScript;
    
    // Update statistics
    updateStats(config, formData);
    
    // Update recommendations
    updateRecommendations(formData);
}

function getFormData() {
    const form = document.getElementById('configForm');
    const formData = new FormData(form);
    
    const data = {
        deploymentMode: formData.get('deploymentMode'),
        environment: formData.get('environment'),
        signals: formData.getAll('signals'),
        receivers: formData.getAll('receivers'),
        processors: formData.getAll('processors'),
        exporterType: formData.get('exporterType'),
        exporterEndpoint: formData.get('exporterEndpoint'),
        batchSize: parseInt(formData.get('batchSize')),
        memoryLimit: parseInt(formData.get('memoryLimit')),
        compression: formData.get('compression'),
        enableTLS: document.getElementById('enableTLS').checked,
        enableAuth: document.getElementById('enableAuth').checked
    };
    
    // Always include batch processor
    if (!data.processors.includes('batch')) {
        data.processors.push('batch');
    }
    
    return data;
}

function buildConfig(data) {
    const config = [];
    
    config.push(`# OpenTelemetry Collector Configuration`);
    config.push(`# Generated: ${new Date().toISOString()}`);
    config.push(`# Mode: ${data.deploymentMode}`);
    config.push(`# Environment: ${data.environment}`);
    config.push(`# Collector Version: v0.113.0`);
    config.push(``);
    
    // Receivers
    config.push(...buildReceivers(data));
    config.push(``);
    
    // Processors
    config.push(...buildProcessors(data));
    config.push(``);
    
    // Exporters
    config.push(...buildExporters(data));
    config.push(``);
    
    // Extensions
    config.push(...buildExtensions(data));
    config.push(``);
    
    // Service
    config.push(...buildService(data));
    
    return config.join('\n');
}

function buildReceivers(data) {
    const receivers = ['receivers:'];
    
    if (data.receivers.includes('otlp')) {
        receivers.push(`  otlp:`);
        receivers.push(`    protocols:`);
        receivers.push(`      grpc:`);
        receivers.push(`        endpoint: 0.0.0.0:4317`);
        if (data.deploymentMode === 'gateway') {
            receivers.push(`        max_recv_msg_size_mib: 16`);
        }
        receivers.push(`      http:`);
        receivers.push(`        endpoint: 0.0.0.0:4318`);
        receivers.push(`        cors:`);
        receivers.push(`          allowed_origins:`);
        receivers.push(`            - "*"`);
    }
    
    if (data.receivers.includes('prometheus')) {
        receivers.push(``);
        receivers.push(`  prometheus:`);
        receivers.push(`    config:`);
        receivers.push(`      scrape_configs:`);
        receivers.push(`        - job_name: 'otel-collector'`);
        receivers.push(`          scrape_interval: 10s`);
        receivers.push(`          static_configs:`);
        receivers.push(`            - targets: ['localhost:8888']`);
    }
    
    if (data.receivers.includes('jaeger')) {
        receivers.push(``);
        receivers.push(`  jaeger:`);
        receivers.push(`    protocols:`);
        receivers.push(`      grpc:`);
        receivers.push(`        endpoint: 0.0.0.0:14250`);
        receivers.push(`      thrift_http:`);
        receivers.push(`        endpoint: 0.0.0.0:14268`);
    }
    
    if (data.receivers.includes('zipkin')) {
        receivers.push(``);
        receivers.push(`  zipkin:`);
        receivers.push(`    endpoint: 0.0.0.0:9411`);
    }
    
    return receivers;
}

function buildProcessors(data) {
    const processors = ['processors:'];
    
    // Memory Limiter (always first)
    if (data.processors.includes('memory_limiter')) {
        processors.push(`  memory_limiter:`);
        processors.push(`    check_interval: 1s`);
        processors.push(`    limit_mib: ${data.memoryLimit}`);
        processors.push(`    spike_limit_mib: ${Math.floor(data.memoryLimit * 0.25)}`);
        processors.push(``);
    }
    
    // Filter (for health checks)
    if (data.processors.includes('filter')) {
        processors.push(`  filter/healthcheck:`);
        processors.push(`    traces:`);
        processors.push(`      span:`);
        processors.push(`        - 'attributes["http.target"] == "/health"'`);
        processors.push(`        - 'attributes["http.target"] == "/ready"'`);
        processors.push(`        - 'attributes["http.target"] == "/metrics"'`);
        processors.push(``);
    }
    
    // Resource
    if (data.processors.includes('resource')) {
        processors.push(`  resource:`);
        processors.push(`    attributes:`);
        processors.push(`      - key: deployment.environment`);
        processors.push(`        value: ${data.environment}`);
        processors.push(`        action: upsert`);
        processors.push(`      - key: service.instance.id`);
        processors.push(`        value: \${HOSTNAME}`);
        processors.push(`        action: insert`);
        if (data.deploymentMode === 'agent') {
            processors.push(`      - key: k8s.pod.name`);
            processors.push(`        value: \${K8S_POD_NAME}`);
            processors.push(`        action: insert`);
            processors.push(`      - key: k8s.namespace.name`);
            processors.push(`        value: \${K8S_NAMESPACE}`);
            processors.push(`        action: insert`);
        }
        processors.push(``);
    }
    
    // Attributes
    if (data.processors.includes('attributes')) {
        processors.push(`  attributes:`);
        processors.push(`    actions:`);
        processors.push(`      # Redact sensitive data`);
        processors.push(`      - key: http.url`);
        processors.push(`        pattern: "(password|token|secret)=([^&]+)"`);
        processors.push(`        replacement: "$1=***"`);
        processors.push(`        action: update`);
        processors.push(`      # Hash PII`);
        processors.push(`      - key: user.email`);
        processors.push(`        action: hash`);
        processors.push(``);
    }
    
    // Tail Sampling (production only)
    if (data.processors.includes('tail_sampling') && data.environment === 'production') {
        processors.push(`  tail_sampling:`);
        processors.push(`    decision_wait: 10s`);
        processors.push(`    num_traces: 100000`);
        processors.push(`    expected_new_traces_per_sec: 10000`);
        processors.push(`    policies:`);
        processors.push(`      # Keep all errors`);
        processors.push(`      - name: errors`);
        processors.push(`        type: status_code`);
        processors.push(`        status_code:`);
        processors.push(`          status_codes: [ERROR]`);
        processors.push(`      # Keep slow requests (>500ms)`);
        processors.push(`      - name: slow-requests`);
        processors.push(`        type: latency`);
        processors.push(`        latency:`);
        processors.push(`          threshold_ms: 500`);
        processors.push(`      # Sample 10% of normal traffic`);
        processors.push(`      - name: normal-traffic`);
        processors.push(`        type: probabilistic`);
        processors.push(`        probabilistic:`);
        processors.push(`          sampling_percentage: 10`);
        processors.push(``);
    }
    
    // Batch (always last)
    processors.push(`  batch:`);
    processors.push(`    timeout: 10s`);
    processors.push(`    send_batch_size: ${data.batchSize}`);
    processors.push(`    send_batch_max_size: ${data.batchSize * 2}`);
    
    return processors;
}

function buildExporters(data) {
    const exporters = ['exporters:'];
    
    switch (data.exporterType) {
        case 'otlp':
            exporters.push(`  otlp:`);
            exporters.push(`    endpoint: ${data.exporterEndpoint}`);
            if (data.enableTLS) {
                exporters.push(`    tls:`);
                exporters.push(`      insecure: false`);
                exporters.push(`      cert_file: /etc/otel/certs/client.crt`);
                exporters.push(`      key_file: /etc/otel/certs/client.key`);
                exporters.push(`      ca_file: /etc/otel/certs/ca.crt`);
            } else {
                exporters.push(`    tls:`);
                exporters.push(`      insecure: true`);
            }
            if (data.enableAuth) {
                exporters.push(`    headers:`);
                exporters.push(`      authorization: "Bearer \${OTEL_AUTH_TOKEN}"`);
            }
            break;
            
        case 'prometheus':
            exporters.push(`  prometheus:`);
            exporters.push(`    endpoint: "0.0.0.0:8889"`);
            exporters.push(`    namespace: otel`);
            exporters.push(`    const_labels:`);
            exporters.push(`      environment: ${data.environment}`);
            break;
            
        case 'jaeger':
            exporters.push(`  jaeger:`);
            exporters.push(`    endpoint: ${data.exporterEndpoint}`);
            if (!data.enableTLS) {
                exporters.push(`    tls:`);
                exporters.push(`      insecure: true`);
            }
            break;
            
        case 'elasticsearch':
            exporters.push(`  elasticsearch:`);
            exporters.push(`    endpoints: [${data.exporterEndpoint}]`);
            exporters.push(`    logs_index: otel-logs`);
            exporters.push(`    traces_index: otel-traces`);
            if (data.enableAuth) {
                exporters.push(`    auth:`);
                exporters.push(`      authenticator: basicauth/elastic`);
            }
            break;
            
        case 'loki':
            exporters.push(`  loki:`);
            exporters.push(`    endpoint: http://${data.exporterEndpoint}/loki/api/v1/push`);
            exporters.push(`    labels:`);
            exporters.push(`      resource:`);
            exporters.push(`        service.name: "service_name"`);
            exporters.push(`        deployment.environment: "${data.environment}"`);
            break;
            
        case 'kafka':
            exporters.push(`  kafka:`);
            exporters.push(`    brokers:`);
            exporters.push(`      - ${data.exporterEndpoint}`);
            exporters.push(`    protocol_version: 2.0.0`);
            exporters.push(`    topic: otlp_spans`);
            break;
            
        case 'alicloud':
            exporters.push(`  alibabacloud_logservice/sls:`);
            exporters.push(`    endpoint: ${data.exporterEndpoint || 'cn-hangzhou.log.aliyuncs.com'}`);
            exporters.push(`    project: \${ALIYUN_SLS_PROJECT}`);
            exporters.push(`    logstore: \${ALIYUN_SLS_LOGSTORE}`);
            exporters.push(`    access_key_id: \${ALIYUN_ACCESS_KEY_ID}`);
            exporters.push(`    access_key_secret: \${ALIYUN_ACCESS_KEY_SECRET}`);
            break;
            
        case 'tencentcloud':
            exporters.push(`  tencentcloud_cls:`);
            exporters.push(`    endpoint: ${data.exporterEndpoint || 'ap-guangzhou.cls.tencentyun.com'}`);
            exporters.push(`    topic_id: \${TENCENT_CLS_TOPIC_ID}`);
            exporters.push(`    secret_id: \${TENCENT_SECRET_ID}`);
            exporters.push(`    secret_key: \${TENCENT_SECRET_KEY}`);
            break;
            
        case 'huaweicloud':
            exporters.push(`  huaweicloud_lts:`);
            exporters.push(`    endpoint: ${data.exporterEndpoint || 'https://lts.cn-north-4.myhuaweicloud.com'}`);
            exporters.push(`    project_id: \${HUAWEI_PROJECT_ID}`);
            exporters.push(`    log_group_id: \${HUAWEI_LOG_GROUP_ID}`);
            exporters.push(`    log_stream_id: \${HUAWEI_LOG_STREAM_ID}`);
            exporters.push(`    access_key: \${HUAWEI_ACCESS_KEY}`);
            exporters.push(`    secret_key: \${HUAWEI_SECRET_KEY}`);
            break;
    }
    
    // Add compression
    if (data.compression !== 'none' && ['otlp', 'jaeger'].includes(data.exporterType)) {
        exporters.push(`    compression: ${data.compression}`);
    }
    
    // Retry and queue settings for production
    if (data.environment === 'production' && ['otlp', 'jaeger', 'elasticsearch'].includes(data.exporterType)) {
        exporters.push(`    retry_on_failure:`);
        exporters.push(`      enabled: true`);
        exporters.push(`      initial_interval: 1s`);
        exporters.push(`      max_interval: 30s`);
        exporters.push(`      max_elapsed_time: 5m`);
        exporters.push(`    sending_queue:`);
        exporters.push(`      enabled: true`);
        exporters.push(`      num_consumers: 20`);
        exporters.push(`      queue_size: 10000`);
    }
    
    // Debug exporter for non-production
    if (data.environment !== 'production') {
        exporters.push(``);
        exporters.push(`  logging:`);
        exporters.push(`    verbosity: detailed`);
        exporters.push(`    sampling_initial: 5`);
        exporters.push(`    sampling_thereafter: 200`);
    }
    
    return exporters;
}

function buildExtensions(data) {
    const extensions = ['extensions:'];
    
    // Health check
    extensions.push(`  health_check:`);
    extensions.push(`    endpoint: 0.0.0.0:13133`);
    extensions.push(``);
    
    // PProf for production
    if (data.environment === 'production') {
        extensions.push(`  pprof:`);
        extensions.push(`    endpoint: 127.0.0.1:1777`);
        extensions.push(``);
    }
    
    // zPages for debugging
    if (data.environment !== 'production') {
        extensions.push(`  zpages:`);
        extensions.push(`    endpoint: 0.0.0.0:55679`);
        extensions.push(``);
    }
    
    // File storage for persistent queue
    if (data.environment === 'production') {
        extensions.push(`  file_storage:`);
        extensions.push(`    directory: /var/lib/otelcol/file_storage`);
        extensions.push(`    timeout: 10s`);
    }
    
    return extensions;
}

function buildService(data) {
    const service = ['service:'];
    
    // Extensions
    const extensionsList = ['health_check'];
    if (data.environment === 'production') {
        extensionsList.push('pprof');
    } else {
        extensionsList.push('zpages');
    }
    
    service.push(`  extensions: [${extensionsList.join(', ')}]`);
    service.push(``);
    
    // Telemetry
    service.push(`  telemetry:`);
    service.push(`    logs:`);
    service.push(`      level: ${data.environment === 'production' ? 'info' : 'debug'}`);
    service.push(`      encoding: json`);
    service.push(`    metrics:`);
    service.push(`      level: detailed`);
    service.push(`      address: 0.0.0.0:8888`);
    service.push(``);
    
    // Pipelines
    service.push(`  pipelines:`);
    
    // Build processor pipeline
    const processorPipeline = [];
    if (data.processors.includes('memory_limiter')) processorPipeline.push('memory_limiter');
    if (data.processors.includes('filter')) processorPipeline.push('filter/healthcheck');
    if (data.processors.includes('resource')) processorPipeline.push('resource');
    if (data.processors.includes('attributes')) processorPipeline.push('attributes');
    if (data.processors.includes('tail_sampling') && data.environment === 'production') {
        processorPipeline.push('tail_sampling');
    }
    processorPipeline.push('batch');
    
    const receivers = data.receivers.length > 0 ? data.receivers : ['otlp'];
    const mainExporter = data.exporterType === 'alicloud' ? 'alibabacloud_logservice/sls' :
                         data.exporterType === 'tencentcloud' ? 'tencentcloud_cls' :
                         data.exporterType === 'huaweicloud' ? 'huaweicloud_lts' :
                         data.exporterType;
    
    const exporters = data.environment === 'production' ? [mainExporter] : [mainExporter, 'logging'];
    
    // Traces pipeline
    if (data.signals.includes('traces')) {
        service.push(`    traces:`);
        service.push(`      receivers: [${receivers.join(', ')}]`);
        service.push(`      processors: [${processorPipeline.join(', ')}]`);
        service.push(`      exporters: [${exporters.join(', ')}]`);
    }
    
    // Metrics pipeline
    if (data.signals.includes('metrics')) {
        const metricsProcessors = processorPipeline.filter(p => p !== 'tail_sampling' && p !== 'filter/healthcheck');
        service.push(`    metrics:`);
        service.push(`      receivers: [${receivers.join(', ')}]`);
        service.push(`      processors: [${metricsProcessors.join(', ')}]`);
        service.push(`      exporters: [${exporters.join(', ')}]`);
    }
    
    // Logs pipeline
    if (data.signals.includes('logs')) {
        const logsProcessors = processorPipeline.filter(p => p !== 'tail_sampling');
        service.push(`    logs:`);
        service.push(`      receivers: [${receivers.join(', ')}]`);
        service.push(`      processors: [${logsProcessors.join(', ')}]`);
        service.push(`      exporters: [${exporters.join(', ')}]`);
    }
    
    // Profiles pipeline (v1.3.0+)
    if (data.signals.includes('profiles')) {
        const profilesProcessors = processorPipeline.filter(p => 
            !['tail_sampling', 'filter/healthcheck', 'attributes'].includes(p));
        service.push(`    profiles:`);
        service.push(`      receivers: [${receivers.join(', ')}]`);
        service.push(`      processors: [${profilesProcessors.join(', ')}]`);
        service.push(`      exporters: [${exporters.join(', ')}]`);
    }
    
    return service;
}

function buildDeployCommands(data) {
    const commands = [];
    
    commands.push(`# Deployment Commands`);
    commands.push(`# Generated: ${new Date().toISOString()}`);
    commands.push(``);
    
    commands.push(`# 1. Save the configuration to config.yaml`);
    commands.push(`cat > config.yaml <<'EOF'`);
    commands.push(`# (Copy the configuration from the "配置文件" tab)`);
    commands.push(`EOF`);
    commands.push(``);
    
    commands.push(`# 2. Validate the configuration`);
    commands.push(`otelcol validate --config=config.yaml`);
    commands.push(``);
    
    if (data.deploymentMode === 'agent') {
        commands.push(`# 3. Deploy as Kubernetes DaemonSet`);
        commands.push(`kubectl create configmap otel-collector-config --from-file=config.yaml -n observability`);
        commands.push(``);
        commands.push(`cat > otel-daemonset.yaml <<'EOF'`);
        commands.push(`apiVersion: apps/v1`);
        commands.push(`kind: DaemonSet`);
        commands.push(`metadata:`);
        commands.push(`  name: otel-collector`);
        commands.push(`  namespace: observability`);
        commands.push(`spec:`);
        commands.push(`  selector:`);
        commands.push(`    matchLabels:`);
        commands.push(`      app: otel-collector`);
        commands.push(`  template:`);
        commands.push(`    metadata:`);
        commands.push(`      labels:`);
        commands.push(`        app: otel-collector`);
        commands.push(`    spec:`);
        commands.push(`      containers:`);
        commands.push(`      - name: otel-collector`);
        commands.push(`        image: otel/opentelemetry-collector-contrib:0.113.0`);
        commands.push(`        args: ["--config=/etc/otel/config.yaml"]`);
        commands.push(`        resources:`);
        commands.push(`          requests:`);
        commands.push(`            memory: ${data.memoryLimit}Mi`);
        commands.push(`            cpu: 200m`);
        commands.push(`          limits:`);
        commands.push(`            memory: ${data.memoryLimit * 2}Mi`);
        commands.push(`            cpu: 1000m`);
        commands.push(`        volumeMounts:`);
        commands.push(`        - name: config`);
        commands.push(`          mountPath: /etc/otel`);
        commands.push(`        env:`);
        commands.push(`        - name: K8S_NODE_NAME`);
        commands.push(`          valueFrom:`);
        commands.push(`            fieldRef:`);
        commands.push(`              fieldPath: spec.nodeName`);
        commands.push(`        - name: K8S_POD_NAME`);
        commands.push(`          valueFrom:`);
        commands.push(`            fieldRef:`);
        commands.push(`              fieldPath: metadata.name`);
        commands.push(`        - name: K8S_NAMESPACE`);
        commands.push(`          valueFrom:`);
        commands.push(`            fieldRef:`);
        commands.push(`              fieldPath: metadata.namespace`);
        commands.push(`      volumes:`);
        commands.push(`      - name: config`);
        commands.push(`        configMap:`);
        commands.push(`          name: otel-collector-config`);
        commands.push(`EOF`);
        commands.push(``);
        commands.push(`kubectl apply -f otel-daemonset.yaml`);
    } else if (data.deploymentMode === 'gateway') {
        commands.push(`# 3. Deploy as Kubernetes Deployment`);
        commands.push(`kubectl create configmap otel-collector-config --from-file=config.yaml -n observability`);
        commands.push(``);
        commands.push(`cat > otel-deployment.yaml <<'EOF'`);
        commands.push(`apiVersion: apps/v1`);
        commands.push(`kind: Deployment`);
        commands.push(`metadata:`);
        commands.push(`  name: otel-collector-gateway`);
        commands.push(`  namespace: observability`);
        commands.push(`spec:`);
        commands.push(`  replicas: 3`);
        commands.push(`  selector:`);
        commands.push(`    matchLabels:`);
        commands.push(`      app: otel-collector-gateway`);
        commands.push(`  template:`);
        commands.push(`    metadata:`);
        commands.push(`      labels:`);
        commands.push(`        app: otel-collector-gateway`);
        commands.push(`    spec:`);
        commands.push(`      containers:`);
        commands.push(`      - name: otel-collector`);
        commands.push(`        image: otel/opentelemetry-collector-contrib:0.113.0`);
        commands.push(`        args: ["--config=/etc/otel/config.yaml"]`);
        commands.push(`        resources:`);
        commands.push(`          requests:`);
        commands.push(`            memory: ${data.memoryLimit}Mi`);
        commands.push(`            cpu: 500m`);
        commands.push(`          limits:`);
        commands.push(`            memory: ${data.memoryLimit * 2}Mi`);
        commands.push(`            cpu: 2000m`);
        commands.push(`        volumeMounts:`);
        commands.push(`        - name: config`);
        commands.push(`          mountPath: /etc/otel`);
        commands.push(`      volumes:`);
        commands.push(`      - name: config`);
        commands.push(`        configMap:`);
        commands.push(`          name: otel-collector-config`);
        commands.push(`---`);
        commands.push(`apiVersion: v1`);
        commands.push(`kind: Service`);
        commands.push(`metadata:`);
        commands.push(`  name: otel-collector-gateway`);
        commands.push(`  namespace: observability`);
        commands.push(`spec:`);
        commands.push(`  selector:`);
        commands.push(`    app: otel-collector-gateway`);
        commands.push(`  ports:`);
        commands.push(`  - name: otlp-grpc`);
        commands.push(`    port: 4317`);
        commands.push(`    targetPort: 4317`);
        commands.push(`  - name: otlp-http`);
        commands.push(`    port: 4318`);
        commands.push(`    targetPort: 4318`);
        commands.push(`  - name: metrics`);
        commands.push(`    port: 8888`);
        commands.push(`    targetPort: 8888`);
        commands.push(`EOF`);
        commands.push(``);
        commands.push(`kubectl apply -f otel-deployment.yaml`);
    } else {
        commands.push(`# 3. Docker Compose deployment`);
        commands.push(`cat > docker-compose.yml <<'EOF'`);
        commands.push(`version: '3.8'`);
        commands.push(`services:`);
        commands.push(`  otel-collector:`);
        commands.push(`    image: otel/opentelemetry-collector-contrib:0.113.0`);
        commands.push(`    command: ["--config=/etc/otel/config.yaml"]`);
        commands.push(`    volumes:`);
        commands.push(`      - ./config.yaml:/etc/otel/config.yaml`);
        commands.push(`    ports:`);
        commands.push(`      - "4317:4317"  # OTLP gRPC`);
        commands.push(`      - "4318:4318"  # OTLP HTTP`);
        commands.push(`      - "8888:8888"  # Metrics`);
        commands.push(`      - "13133:13133" # Health Check`);
        commands.push(`    deploy:`);
        commands.push(`      resources:`);
        commands.push(`        limits:`);
        commands.push(`          memory: ${data.memoryLimit * 2}M`);
        commands.push(`        reservations:`);
        commands.push(`          memory: ${data.memoryLimit}M`);
        commands.push(`EOF`);
        commands.push(``);
        commands.push(`docker-compose up -d`);
    }
    
    commands.push(``);
    commands.push(`# 4. Verify deployment`);
    commands.push(`curl http://localhost:13133`);
    commands.push(`# Expected: {"status":"Server available"}`);
    
    return commands.join('\n');
}

function buildValidateScript(data) {
    const script = [];
    
    script.push(`#!/bin/bash`);
    script.push(`# Validation Script for OpenTelemetry Collector`);
    script.push(`# Generated: ${new Date().toISOString()}`);
    script.push(``);
    script.push(`set -e`);
    script.push(``);
    script.push(`echo "🔍 Validating OpenTelemetry Collector Configuration..."`);
    script.push(``);
    
    script.push(`# 1. Check if otelcol is available`);
    script.push(`if ! command -v otelcol &> /dev/null; then`);
    script.push(`    echo "❌ otelcol not found. Install from: https://opentelemetry.io/docs/collector/installation/"`);
    script.push(`    exit 1`);
    script.push(`fi`);
    script.push(``);
    
    script.push(`# 2. Validate configuration syntax`);
    script.push(`echo "📝 Validating config.yaml syntax..."`);
    script.push(`if otelcol validate --config=config.yaml; then`);
    script.push(`    echo "✅ Configuration syntax is valid"`);
    script.push(`else`);
    script.push(`    echo "❌ Configuration syntax error"`);
    script.push(`    exit 1`);
    script.push(`fi`);
    script.push(``);
    
    script.push(`# 3. Test connectivity to backend`);
    script.push(`echo "🌐 Testing connectivity to ${data.exporterEndpoint}..."`);
    if (data.exporterEndpoint.includes(':')) {
        const [host, port] = data.exporterEndpoint.split(':');
        script.push(`if timeout 5 bash -c "cat < /dev/null > /dev/tcp/${host}/${port}"; then`);
        script.push(`    echo "✅ Backend ${data.exporterEndpoint} is reachable"`);
        script.push(`else`);
        script.push(`    echo "⚠️  Backend ${data.exporterEndpoint} is not reachable (this may be expected if backend is not running)"`);
        script.push(`fi`);
    }
    script.push(``);
    
    script.push(`# 4. Start Collector in dry-run mode`);
    script.push(`echo "🚀 Starting Collector in dry-run mode..."`);
    script.push(`timeout 10s otelcol --config=config.yaml --dry-run || true`);
    script.push(``);
    
    script.push(`# 5. Check resource requirements`);
    script.push(`echo "📊 Resource Requirements:"`);
    script.push(`echo "  Memory Limit: ${data.memoryLimit}MiB"`);
    script.push(`echo "  Batch Size: ${data.batchSize}"`);
    script.push(`echo "  Compression: ${data.compression}"`);
    script.push(`echo "  Signals: ${data.signals.join(', ')}"`);
    script.push(``);
    
    script.push(`# 6. Security checks`);
    if (!data.enableTLS && data.environment === 'production') {
        script.push(`echo "⚠️  WARNING: TLS is not enabled in production environment"`);
    }
    if (!data.enableAuth && data.environment === 'production') {
        script.push(`echo "⚠️  WARNING: Authentication is not enabled in production environment"`);
    }
    script.push(``);
    
    script.push(`echo ""`);
    script.push(`echo "✅ Validation completed successfully!"`);
    script.push(`echo ""`);
    script.push(`echo "📌 Next steps:"`);
    script.push(`echo "  1. Review the configuration file"`);
    script.push(`echo "  2. Deploy using the commands in 'Deploy Commands' tab"`);
    script.push(`echo "  3. Monitor Collector metrics at http://localhost:8888/metrics"`);
    script.push(`echo "  4. Check health at http://localhost:13133"`);
    
    return script.join('\n');
}

function updateStats(config, data) {
    const lines = config.split('\n').length;
    const components = data.receivers.length + data.processors.length + 1; // +1 for exporter
    const pipelines = data.signals.length;
    
    document.querySelector('#stats .stat-card:nth-child(1) .value').textContent = lines;
    document.querySelector('#stats .stat-card:nth-child(2) .value').textContent = components;
    document.querySelector('#stats .stat-card:nth-child(3) .value').textContent = pipelines;
}

function updateRecommendations(data) {
    const recommendations = [];
    
    if (!data.enableTLS && data.environment === 'production') {
        recommendations.push('⚠️ <strong>安全警告</strong>: 生产环境建议启用TLS加密');
    }
    
    if (!data.enableAuth && data.environment === 'production') {
        recommendations.push('⚠️ <strong>安全警告</strong>: 生产环境建议启用认证');
    }
    
    if (!data.processors.includes('memory_limiter')) {
        recommendations.push('⚠️ <strong>性能建议</strong>: 建议启用Memory Limiter防止OOM');
    }
    
    if (!data.processors.includes('tail_sampling') && data.environment === 'production') {
        recommendations.push('💡 <strong>优化建议</strong>: 生产环境建议启用尾部采样降低成本');
    }
    
    if (data.batchSize < 4096) {
        recommendations.push('💡 <strong>性能建议</strong>: 批处理大小建议设置为8192或更高以提升性能');
    }
    
    if (data.deploymentMode === 'agent' && data.memoryLimit > 1024) {
        recommendations.push('💡 <strong>资源建议</strong>: Agent模式通常512-1024MiB内存即可');
    }
    
    if (data.compression === 'none' && data.environment === 'production') {
        recommendations.push('💡 <strong>带宽建议</strong>: 生产环境建议启用gzip或zstd压缩');
    }
    
    if (recommendations.length === 0) {
        recommendations.push('✅ <strong>配置良好</strong>: 当前配置符合最佳实践');
    }
    
    document.getElementById('recommendations').innerHTML = recommendations.join('<br>');
}

function switchTab(tabName) {
    // Update tab buttons
    document.querySelectorAll('.tab').forEach(tab => {
        tab.classList.remove('active');
    });
    event.target.classList.add('active');
    
    // Update tab contents
    document.querySelectorAll('.tab-content').forEach(content => {
        content.classList.remove('active');
    });
    document.getElementById(tabName + '-content').classList.add('active');
}

function copyToClipboard(elementId) {
    const text = document.getElementById(elementId).textContent;
    navigator.clipboard.writeText(text).then(() => {
        const btn = event.target;
        const originalText = btn.textContent;
        btn.textContent = '✅ 已复制';
        btn.classList.add('copied');
        
        setTimeout(() => {
            btn.textContent = originalText;
            btn.classList.remove('copied');
        }, 2000);
    });
}

function resetForm() {
    document.getElementById('configForm').reset();
    document.getElementById('configOutput').textContent = '# 请填写左侧表单并点击"生成配置"按钮';
    document.getElementById('deployOutput').textContent = '# 部署命令将在生成配置后显示';
    document.getElementById('validateOutput').textContent = '# 验证脚本将在生成配置后显示';
    
    document.querySelector('#stats .stat-card:nth-child(1) .value').textContent = '0';
    document.querySelector('#stats .stat-card:nth-child(2) .value').textContent = '0';
    document.querySelector('#stats .stat-card:nth-child(3) .value').textContent = '0';
    
    document.getElementById('recommendations').innerHTML = 
        '💡 <strong>建议</strong>: 生产环境请启用TLS和认证,并根据实际负载调整批处理和内存参数。';
}

// Initialize with default configuration on page load
window.addEventListener('DOMContentLoaded', () => {
    generateConfig();
});

