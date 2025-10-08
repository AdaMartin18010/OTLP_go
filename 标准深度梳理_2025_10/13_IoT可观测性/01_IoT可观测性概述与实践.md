# IoT可观测性概述与实践

> **标准版本**: v1.27.0  
> **状态**: Experimental  
> **最后更新**: 2025年10月8日

---

## 目录

- [IoT可观测性概述与实践](#iot可观测性概述与实践)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. IoT可观测性特点](#2-iot可观测性特点)
    - [2.1 核心挑战](#21-核心挑战)
    - [2.2 关键需求](#22-关键需求)
  - [3. IoT设备集成](#3-iot设备集成)
    - [3.1 设备端SDK](#31-设备端sdk)
    - [3.2 网关模式](#32-网关模式)
    - [3.3 边缘计算集成](#33-边缘计算集成)
  - [4. IoT语义约定](#4-iot语义约定)
    - [4.1 设备属性](#41-设备属性)
    - [4.2 遥测属性](#42-遥测属性)
    - [4.3 事件属性](#43-事件属性)
  - [5. 轻量级协议支持](#5-轻量级协议支持)
    - [5.1 MQTT集成](#51-mqtt集成)
    - [5.2 CoAP集成](#52-coap集成)
    - [5.3 LoRaWAN集成](#53-lorawan集成)
  - [6. 设备监控](#6-设备监控)
    - [6.1 设备状态监控](#61-设备状态监控)
    - [6.2 传感器数据采集](#62-传感器数据采集)
    - [6.3 设备生命周期追踪](#63-设备生命周期追踪)
  - [7. 边缘可观测性](#7-边缘可观测性)
    - [7.1 边缘节点监控](#71-边缘节点监控)
    - [7.2 本地数据聚合](#72-本地数据聚合)
    - [7.3 间歇性连接处理](#73-间歇性连接处理)
  - [8. 资源优化](#8-资源优化)
    - [8.1 数据压缩](#81-数据压缩)
    - [8.2 采样策略](#82-采样策略)
    - [8.3 电源管理](#83-电源管理)
  - [9. 完整示例](#9-完整示例)
    - [9.1 工业传感器监控](#91-工业传感器监控)
    - [9.2 智能家居设备](#92-智能家居设备)
    - [9.3 车联网应用](#93-车联网应用)
  - [10. 参考资源](#10-参考资源)
    - [官方文档](#官方文档)
    - [社区资源](#社区资源)

---

## 1. 概述

IoT（物联网）设备的可观测性面临独特的挑战，包括极低的资源限制、间歇性连接、大规模设备管理等。OpenTelemetry通过轻量级实现和灵活的架构支持IoT场景。

**核心目标**：

```text
✅ 监控大规模IoT设备状态
✅ 采集传感器遥测数据
✅ 追踪设备生命周期事件
✅ 优化资源使用（CPU/内存/功耗）
✅ 处理间歇性网络连接
✅ 支持边缘计算场景
```

---

## 2. IoT可观测性特点

### 2.1 核心挑战

```text
❗ 极端资源限制:    微控制器级别的CPU/内存
❗ 低功耗要求:      电池供电设备需长时间运行
❗ 间歇性连接:      网络不稳定或定时唤醒
❗ 大规模部署:      数以万计的设备
❗ 异构环境:        多种协议和通信方式
❗ 安全限制:        有限的加密能力
```

### 2.2 关键需求

**设备监控需求**：

```text
- 设备在线状态
- 固件版本管理
- 电池电量监控
- 网络信号强度
- 传感器数据质量
- 设备故障诊断
```

**数据管理需求**：

```text
- 本地数据缓存
- 智能采样
- 数据压缩
- 批量上传
- 离线数据恢复
```

---

## 3. IoT设备集成

### 3.1 设备端SDK

**C/C++轻量级实现**（概念示例）：

```c
#include <opentelemetry/telemetry.h>

// 初始化轻量级TracerProvider
otel_config_t config = {
    .service_name = "iot-device",
    .service_version = "1.0.0",
    .endpoint = "http://gateway:4318",
    .compression = OTEL_COMPRESS_GZIP,
    .batch_size = 10,
    .batch_timeout_ms = 30000  // 30秒批次超时
};

otel_tracer_t* tracer = otel_init(&config);

// 记录设备事件
void report_sensor_reading(float temperature, float humidity) {
    otel_span_t* span = otel_span_start(tracer, "sensor.reading");
    
    otel_span_set_attribute_double(span, "sensor.temperature", temperature);
    otel_span_set_attribute_double(span, "sensor.humidity", humidity);
    otel_span_set_attribute_string(span, "device.id", get_device_id());
    
    otel_span_end(span);
}

// 上报设备状态
void report_device_status() {
    otel_span_t* span = otel_span_start(tracer, "device.status");
    
    otel_span_set_attribute_int(span, "device.battery_level", get_battery_level());
    otel_span_set_attribute_int(span, "device.signal_strength", get_signal_strength());
    otel_span_set_attribute_string(span, "device.firmware_version", FIRMWARE_VERSION);
    
    otel_span_end(span);
}
```

### 3.2 网关模式

**架构图**：

```text
IoT设备 (MQTT) → IoT网关 (OTel Collector) → 云端后端
```

**网关Collector配置**：

```yaml
receivers:
  # MQTT Receiver（接收设备数据）
  mqtt:
    endpoint: tcp://0.0.0.0:1883
    topics:
      - devices/+/telemetry
      - devices/+/events
    qos: 1
    client_id: otel-gateway
  
  # OTLP Receiver（边缘设备直接上报）
  otlp:
    protocols:
      http:
        endpoint: 0.0.0.0:4318

processors:
  # 批处理（减少网络请求）
  batch:
    timeout: 30s
    send_batch_size: 1000
  
  # 属性增强
  attributes:
    actions:
      # 添加网关信息
      - key: gateway.id
        value: ${GATEWAY_ID}
        action: insert
      - key: gateway.location
        value: ${GATEWAY_LOCATION}
        action: insert
  
  # Resource处理
  resource:
    attributes:
      - key: deployment.environment
        value: iot-edge
        action: insert

exporters:
  # 云端后端
  otlp/cloud:
    endpoint: cloud-backend:4317
    compression: gzip
    retry_on_failure:
      enabled: true
      max_elapsed_time: 300s
    sending_queue:
      enabled: true
      storage: file_storage

extensions:
  file_storage:
    directory: /var/lib/otelcol/iot-cache

service:
  extensions: [file_storage]
  pipelines:
    traces:
      receivers: [mqtt, otlp]
      processors: [attributes, resource, batch]
      exporters: [otlp/cloud]
```

### 3.3 边缘计算集成

**边缘节点Python示例**：

```python
import time
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.http.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.resources import Resource

# 边缘节点配置
resource = Resource(attributes={
    "service.name": "iot-edge-node",
    "service.version": "1.0.0",
    "edge.node.id": "edge-001",
    "edge.location": "factory-floor-1"
})

# OTLP Exporter（发送到本地网关）
otlp_exporter = OTLPSpanExporter(
    endpoint="http://local-gateway:4318/v1/traces",
    timeout=10
)

# TracerProvider
provider = TracerProvider(resource=resource)
processor = BatchSpanProcessor(
    otlp_exporter,
    schedule_delay_millis=30000,  # 30秒批次
    max_queue_size=2048
)
provider.add_span_processor(processor)

trace.set_tracer_provider(provider)
tracer = trace.get_tracer(__name__)

# 聚合多个设备数据
class DeviceDataAggregator:
    def __init__(self):
        self.buffer = []
    
    def collect_device_data(self, device_id, sensor_data):
        """收集单个设备数据"""
        self.buffer.append({
            "device_id": device_id,
            "timestamp": time.time(),
            "data": sensor_data
        })
        
        # 批量处理
        if len(self.buffer) >= 100:
            self.flush()
    
    def flush(self):
        """批量上报聚合数据"""
        if not self.buffer:
            return
        
        with tracer.start_as_current_span("edge.aggregate") as span:
            span.set_attribute("device.count", len(self.buffer))
            span.set_attribute("edge.node.id", "edge-001")
            
            # 计算聚合统计
            temperatures = [d["data"]["temperature"] for d in self.buffer]
            span.set_attribute("temperature.avg", sum(temperatures) / len(temperatures))
            span.set_attribute("temperature.min", min(temperatures))
            span.set_attribute("temperature.max", max(temperatures))
            
            # 上报数据
            self.send_to_gateway(self.buffer)
            self.buffer.clear()
```

---

## 4. IoT语义约定

### 4.1 设备属性

```text
device.id:              设备唯一标识
device.manufacturer:    制造商
device.model:           设备型号
device.type:            设备类型 (sensor/actuator/gateway)
device.firmware:        固件版本
device.hardware:        硬件版本
device.location:        物理位置
device.deployment_date: 部署日期
```

### 4.2 遥测属性

```text
sensor.type:            传感器类型 (temperature/humidity/pressure)
sensor.value:           传感器数值
sensor.unit:            单位 (celsius/percent/pascal)
sensor.accuracy:        精度
sensor.calibration_date: 校准日期
sensor.reading_quality: 读数质量 (good/poor/failed)
```

### 4.3 事件属性

```text
event.type:             事件类型 (startup/shutdown/error/alert)
event.severity:         严重性 (info/warning/critical)
device.battery_level:   电池电量 (0-100)
device.signal_strength: 信号强度 (dBm)
network.type:           网络类型 (wifi/cellular/lora)
```

---

## 5. 轻量级协议支持

### 5.1 MQTT集成

**设备端MQTT发布（Python）**：

```python
import paho.mqtt.client as mqtt
import json

class IoTDevice:
    def __init__(self, device_id, mqtt_broker):
        self.device_id = device_id
        self.client = mqtt.Client(device_id)
        self.client.connect(mqtt_broker, 1883)
        self.client.loop_start()
    
    def send_telemetry(self, sensor_data):
        """发送遥测数据"""
        payload = {
            "timestamp": time.time(),
            "device_id": self.device_id,
            "trace_id": generate_trace_id(),
            "data": sensor_data
        }
        
        topic = f"devices/{self.device_id}/telemetry"
        self.client.publish(topic, json.dumps(payload), qos=1)
    
    def send_event(self, event_type, data):
        """发送设备事件"""
        payload = {
            "timestamp": time.time(),
            "device_id": self.device_id,
            "event_type": event_type,
            "data": data
        }
        
        topic = f"devices/{self.device_id}/events"
        self.client.publish(topic, json.dumps(payload), qos=1)

# 使用示例
device = IoTDevice("sensor-001", "mqtt-broker.local")

# 发送温度数据
device.send_telemetry({
    "temperature": 25.5,
    "humidity": 60.0
})

# 发送电池警告
device.send_event("battery_low", {
    "battery_level": 15
})
```

### 5.2 CoAP集成

**CoAP设备端（概念示例）**：

```python
from aiocoap import *
import json

async def send_coap_telemetry(device_id, sensor_data):
    """通过CoAP发送遥测数据"""
    protocol = await Context.create_client_context()
    
    payload = json.dumps({
        "device_id": device_id,
        "timestamp": time.time(),
        "data": sensor_data
    }).encode('utf-8')
    
    request = Message(
        code=POST,
        uri=f'coap://gateway.local/telemetry',
        payload=payload
    )
    
    response = await protocol.request(request).response
    return response
```

### 5.3 LoRaWAN集成

**LoRaWAN设备数据格式**：

```text
# LoRaWAN Payload（极度压缩）
Device Payload: [DeviceID (2B) | Temperature (2B) | Humidity (1B) | Battery (1B)]

# 网关解析并转换为OTLP
Gateway解析 → OTLP Span → 云端后端
```

---

## 6. 设备监控

### 6.1 设备状态监控

**Go网关设备状态跟踪**：

```go
package main

import (
    "context"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

type DeviceMonitor struct {
    meter           metric.Meter
    onlineDevices   metric.Int64UpDownCounter
    batteryLevel    metric.Float64ObservableGauge
    signalStrength  metric.Int64ObservableGauge
}

func NewDeviceMonitor() *DeviceMonitor {
    meter := otel.Meter("iot-gateway")
    
    onlineDevices, _ := meter.Int64UpDownCounter(
        "iot.devices.online",
        metric.WithDescription("Number of online devices"),
    )
    
    return &DeviceMonitor{
        meter:         meter,
        onlineDevices: onlineDevices,
    }
}

func (m *DeviceMonitor) DeviceConnected(deviceID string) {
    ctx := context.Background()
    m.onlineDevices.Add(ctx, 1,
        metric.WithAttributes(
            attribute.String("device.id", deviceID),
        ),
    )
}

func (m *DeviceMonitor) DeviceDisconnected(deviceID string) {
    ctx := context.Background()
    m.onlineDevices.Add(ctx, -1,
        metric.WithAttributes(
            attribute.String("device.id", deviceID),
        ),
    )
}

func (m *DeviceMonitor) ReportBatteryLevel(deviceID string, level float64) {
    // 记录电池电量
    tracer := otel.Tracer("iot-gateway")
    _, span := tracer.Start(context.Background(), "device.battery_update")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("device.id", deviceID),
        attribute.Float64("battery.level", level),
    )
}
```

### 6.2 传感器数据采集

**工业传感器数据采集示例**：

```python
from dataclasses import dataclass
from typing import List
import time

@dataclass
class SensorReading:
    sensor_id: str
    sensor_type: str
    value: float
    unit: str
    timestamp: float
    quality: str  # 'good', 'poor', 'failed'

class IndustrialSensorCollector:
    def __init__(self, tracer):
        self.tracer = tracer
        self.readings_buffer = []
    
    def collect_sensor_data(self, sensors: List[str]):
        """批量采集传感器数据"""
        with self.tracer.start_as_current_span("sensors.bulk_read") as span:
            span.set_attribute("sensors.count", len(sensors))
            
            for sensor_id in sensors:
                reading = self.read_sensor(sensor_id)
                self.readings_buffer.append(reading)
            
            # 批量上报
            if len(self.readings_buffer) >= 50:
                self.flush_readings()
    
    def read_sensor(self, sensor_id: str) -> SensorReading:
        """读取单个传感器"""
        # 模拟读取传感器
        return SensorReading(
            sensor_id=sensor_id,
            sensor_type="temperature",
            value=25.5,
            unit="celsius",
            timestamp=time.time(),
            quality="good"
        )
    
    def flush_readings(self):
        """批量上报读数"""
        with self.tracer.start_as_current_span("sensors.flush") as span:
            span.set_attribute("readings.count", len(self.readings_buffer))
            
            # 计算统计
            values = [r.value for r in self.readings_buffer]
            span.set_attribute("temperature.avg", sum(values) / len(values))
            span.set_attribute("temperature.min", min(values))
            span.set_attribute("temperature.max", max(values))
            
            # 发送数据
            self.send_to_backend(self.readings_buffer)
            self.readings_buffer.clear()
```

### 6.3 设备生命周期追踪

**设备生命周期事件**：

```go
func TrackDeviceLifecycle(tracer trace.Tracer, deviceID string) {
    ctx := context.Background()
    
    // 设备注册
    RegisterDevice := func() {
        _, span := tracer.Start(ctx, "device.register")
        defer span.End()
        
        span.SetAttributes(
            attribute.String("device.id", deviceID),
            attribute.String("event.type", "register"),
        )
    }
    
    // 固件更新
    FirmwareUpdate := func(oldVersion, newVersion string) {
        _, span := tracer.Start(ctx, "device.firmware_update")
        defer span.End()
        
        span.SetAttributes(
            attribute.String("device.id", deviceID),
            attribute.String("firmware.old_version", oldVersion),
            attribute.String("firmware.new_version", newVersion),
        )
    }
    
    // 设备退役
    DecommissionDevice := func() {
        _, span := tracer.Start(ctx, "device.decommission")
        defer span.End()
        
        span.SetAttributes(
            attribute.String("device.id", deviceID),
            attribute.String("event.type", "decommission"),
        )
    }
}
```

---

## 7. 边缘可观测性

### 7.1 边缘节点监控

**边缘网关资源监控**：

```python
import psutil
from opentelemetry import metrics

class EdgeGatewayMonitor:
    def __init__(self):
        self.meter = metrics.get_meter(__name__)
        self.setup_metrics()
    
    def setup_metrics(self):
        """设置边缘网关指标"""
        # CPU使用率
        self.meter.create_observable_gauge(
            "edge.gateway.cpu.usage",
            callbacks=[self._observe_cpu],
            unit="%"
        )
        
        # 内存使用率
        self.meter.create_observable_gauge(
            "edge.gateway.memory.usage",
            callbacks=[self._observe_memory],
            unit="%"
        )
        
        # 设备连接数
        self.meter.create_observable_gauge(
            "edge.gateway.devices.connected",
            callbacks=[self._observe_devices],
            unit="{device}"
        )
    
    def _observe_cpu(self, observer):
        cpu_percent = psutil.cpu_percent()
        observer.observe(cpu_percent)
    
    def _observe_memory(self, observer):
        memory = psutil.virtual_memory()
        observer.observe(memory.percent)
    
    def _observe_devices(self, observer):
        # 从设备管理器获取连接数
        device_count = get_connected_device_count()
        observer.observe(device_count)
```

### 7.2 本地数据聚合

**边缘数据聚合引擎**：

```python
from collections import defaultdict
import statistics

class EdgeDataAggregator:
    def __init__(self, tracer):
        self.tracer = tracer
        self.aggregation_window = 60  # 60秒窗口
        self.data_buffer = defaultdict(list)
    
    def add_reading(self, device_id, sensor_type, value):
        """添加传感器读数"""
        self.data_buffer[(device_id, sensor_type)].append({
            'value': value,
            'timestamp': time.time()
        })
    
    def aggregate_and_send(self):
        """聚合并发送数据"""
        with self.tracer.start_as_current_span("edge.aggregate") as span:
            aggregated_count = 0
            
            for (device_id, sensor_type), readings in self.data_buffer.items():
                if not readings:
                    continue
                
                # 计算聚合统计
                values = [r['value'] for r in readings]
                aggregated = {
                    'device_id': device_id,
                    'sensor_type': sensor_type,
                    'count': len(values),
                    'mean': statistics.mean(values),
                    'min': min(values),
                    'max': max(values),
                    'stdev': statistics.stdev(values) if len(values) > 1 else 0
                }
                
                # 发送聚合数据
                self.send_aggregated(aggregated)
                aggregated_count += 1
            
            span.set_attribute("aggregated.device_count", aggregated_count)
            span.set_attribute("total.readings", sum(len(r) for r in self.data_buffer.values()))
            
            # 清空缓冲区
            self.data_buffer.clear()
```

### 7.3 间歇性连接处理

**离线数据缓存与恢复**：

```python
import sqlite3
import pickle

class OfflineDataCache:
    def __init__(self, db_path='/var/cache/iot-telemetry.db'):
        self.conn = sqlite3.connect(db_path)
        self.create_table()
    
    def create_table(self):
        self.conn.execute('''
            CREATE TABLE IF NOT EXISTS telemetry_cache (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                timestamp REAL,
                device_id TEXT,
                data BLOB
            )
        ''')
        self.conn.commit()
    
    def cache_telemetry(self, device_id, telemetry_data):
        """缓存离线遥测数据"""
        data_blob = pickle.dumps(telemetry_data)
        self.conn.execute(
            'INSERT INTO telemetry_cache (timestamp, device_id, data) VALUES (?, ?, ?)',
            (time.time(), device_id, data_blob)
        )
        self.conn.commit()
    
    def flush_when_online(self, sender_func):
        """网络恢复后发送缓存数据"""
        cursor = self.conn.execute('SELECT id, device_id, data FROM telemetry_cache ORDER BY id')
        
        for row in cursor:
            cache_id, device_id, data_blob = row
            telemetry_data = pickle.loads(data_blob)
            
            try:
                # 发送数据
                sender_func(device_id, telemetry_data)
                
                # 删除已发送的缓存
                self.conn.execute('DELETE FROM telemetry_cache WHERE id = ?', (cache_id,))
                self.conn.commit()
            except Exception as e:
                # 发送失败，保留缓存
                print(f"Failed to send cached data: {e}")
                break
```

---

## 8. 资源优化

### 8.1 数据压缩

**轻量级数据编码**：

```c
// 使用Protobuf或自定义二进制格式压缩数据
typedef struct {
    uint16_t device_id;
    uint32_t timestamp;
    int16_t temperature;  // 温度 * 10 (节省空间)
    uint8_t humidity;     // 湿度百分比
    uint8_t battery;      // 电池百分比
} __attribute__((packed)) sensor_data_t;

// 打包函数
void pack_sensor_data(sensor_data_t* packed, float temp, float humid, int battery) {
    packed->device_id = DEVICE_ID;
    packed->timestamp = (uint32_t)time(NULL);
    packed->temperature = (int16_t)(temp * 10);
    packed->humidity = (uint8_t)humid;
    packed->battery = (uint8_t)battery;
}

// 发送压缩数据
void send_compressed_data() {
    sensor_data_t data;
    pack_sensor_data(&data, 25.5, 60.0, 85);
    
    // 使用gzip进一步压缩
    uint8_t compressed[sizeof(sensor_data_t) * 2];
    size_t compressed_size = compress_data((uint8_t*)&data, sizeof(data), compressed);
    
    // 发送
    mqtt_publish("devices/data", compressed, compressed_size);
}
```

### 8.2 采样策略

**智能采样算法**：

```python
class AdaptiveSampler:
    def __init__(self):
        self.last_value = None
        self.threshold = 0.5  # 变化阈值
    
    def should_sample(self, new_value):
        """基于变化率决定是否采样"""
        if self.last_value is None:
            self.last_value = new_value
            return True
        
        # 计算变化率
        change_rate = abs(new_value - self.last_value) / self.last_value
        
        # 变化超过阈值时采样
        if change_rate > self.threshold:
            self.last_value = new_value
            return True
        
        return False

# 使用示例
sampler = AdaptiveSampler()

while True:
    temperature = read_temperature_sensor()
    
    if sampler.should_sample(temperature):
        send_telemetry(temperature)
    
    time.sleep(60)  # 每分钟检查一次
```

### 8.3 电源管理

**低功耗模式配置**：

```python
class PowerAwareCollector:
    def __init__(self):
        self.battery_level = 100
        self.sampling_interval = 60  # 默认60秒
    
    def adjust_for_battery(self):
        """根据电池电量调整采样频率"""
        if self.battery_level > 50:
            self.sampling_interval = 60  # 1分钟
        elif self.battery_level > 20:
            self.sampling_interval = 300  # 5分钟
        else:
            self.sampling_interval = 600  # 10分钟
    
    def collect_data(self):
        """节能数据采集"""
        self.adjust_for_battery()
        
        # 批量采集以减少无线电激活
        readings = []
        for _ in range(10):
            reading = read_sensor()
            readings.append(reading)
        
        # 批量发送
        send_batch(readings)
        
        # 进入深度睡眠
        sleep(self.sampling_interval)
```

---

## 9. 完整示例

### 9.1 工业传感器监控

```python
# 工业传感器网关
from opentelemetry import trace, metrics
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.metrics import MeterProvider
from opentelemetry.exporter.otlp.proto.http import OTLPSpanExporter, OTLPMetricExporter

class IndustrialSensorGateway:
    def __init__(self):
        # 初始化OpenTelemetry
        self.setup_telemetry()
        self.sensor_monitor = DeviceMonitor()
        self.data_aggregator = EdgeDataAggregator(self.tracer)
    
    def setup_telemetry(self):
        # Tracer配置
        provider = TracerProvider(resource=Resource(attributes={
            "service.name": "industrial-gateway",
            "deployment.environment": "factory-floor",
            "gateway.location": "building-a-floor-2"
        }))
        
        provider.add_span_processor(BatchSpanProcessor(
            OTLPSpanExporter(endpoint="http://central-collector:4318/v1/traces")
        ))
        
        trace.set_tracer_provider(provider)
        self.tracer = trace.get_tracer(__name__)
    
    def monitor_production_line(self, line_id):
        """监控生产线传感器"""
        with self.tracer.start_as_current_span(f"production_line.{line_id}") as span:
            # 采集温度传感器
            temp_sensors = [f"temp-{i}" for i in range(1, 11)]
            temperatures = [self.read_sensor(s) for s in temp_sensors]
            
            span.set_attribute("line.id", line_id)
            span.set_attribute("sensors.count", len(temp_sensors))
            span.set_attribute("temperature.avg", sum(temperatures) / len(temperatures))
            
            # 检测异常
            if max(temperatures) > 80:
                span.add_event("temperature_alert", {
                    "severity": "high",
                    "max_temperature": max(temperatures)
                })
            
            # 聚合数据
            for sensor_id, temp in zip(temp_sensors, temperatures):
                self.data_aggregator.add_reading(sensor_id, "temperature", temp)
            
            # 定期上报
            if time.time() % 60 == 0:
                self.data_aggregator.aggregate_and_send()
```

### 9.2 智能家居设备

```python
# 智能恒温器示例
class SmartThermostat:
    def __init__(self, device_id):
        self.device_id = device_id
        self.tracer = trace.get_tracer(__name__)
    
    def adjust_temperature(self, target_temp):
        """调整目标温度"""
        with self.tracer.start_as_current_span("thermostat.adjust") as span:
            span.set_attribute("device.id", self.device_id)
            span.set_attribute("temperature.target", target_temp)
            span.set_attribute("temperature.current", self.get_current_temp())
            
            # 执行温度调整
            self.set_hvac_mode(target_temp)
            
            span.add_event("temperature_adjusted")
    
    def report_status(self):
        """定期上报状态"""
        with self.tracer.start_as_current_span("thermostat.status") as span:
            span.set_attribute("device.id", self.device_id)
            span.set_attribute("temperature.current", self.get_current_temp())
            span.set_attribute("humidity.current", self.get_humidity())
            span.set_attribute("hvac.mode", self.get_hvac_mode())
            span.set_attribute("power.consumption_watts", self.get_power_consumption())
```

### 9.3 车联网应用

```go
// 车载OBD设备
type VehicleTelemetry struct {
    tracer trace.Tracer
    vehicleID string
}

func (v *VehicleTelemetry) CollectVehicleData() {
    ctx := context.Background()
    _, span := v.tracer.Start(ctx, "vehicle.telemetry")
    defer span.End()
    
    // 收集车辆数据
    speed := v.getSpeed()
    rpm := v.getRPM()
    fuelLevel := v.getFuelLevel()
    engineTemp := v.getEngineTemperature()
    location := v.getGPSLocation()
    
    span.SetAttributes(
        attribute.String("vehicle.id", v.vehicleID),
        attribute.Float64("vehicle.speed", speed),
        attribute.Int64("vehicle.rpm", rpm),
        attribute.Float64("vehicle.fuel_level", fuelLevel),
        attribute.Float64("vehicle.engine_temp", engineTemp),
        attribute.String("vehicle.location", location.String()),
    )
    
    // 检测异常
    if engineTemp > 100 {
        span.AddEvent("engine_overheat", trace.WithAttributes(
            attribute.String("severity", "critical"),
            attribute.Float64("temperature", engineTemp),
        ))
    }
}
```

---

## 10. 参考资源

### 官方文档

- **OpenTelemetry IoT**: <https://opentelemetry.io/docs/specs/semconv/iot/>
- **Collector Configuration**: <https://opentelemetry.io/docs/collector/configuration/>

### 社区资源

- **IoT Use Cases**: <https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/use-cases/iot.md>
- **Edge Computing Patterns**: <https://opentelemetry.io/docs/collector/deployment/>

---

**文档维护**: OTLP深度梳理项目组  
**最后更新**: 2025年10月8日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐
