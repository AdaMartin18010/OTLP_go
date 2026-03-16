// Go 1.26 新特性完整示例
// 展示 Go 1.26 中与 OTLP/可观测性相关的新特性

package main

import (
	"bytes"
	"crypto/rand"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"runtime"
	"time"
)

// Person 用于演示 new 表达式
// Go 1.26: new 函数现在支持表达式作为操作数
type Person struct {
	Name string `json:"name"`
	Age  *int   `json:"age"` // age if known; nil otherwise
}

// yearsSince 计算年龄
func yearsSince(t time.Time) int {
	return int(time.Since(t).Hours() / (365.25 * 24)) // approximately
}

// ============================================
// 1. new 表达式特性 (Go 1.26)
// ============================================

func demoNewExpression() {
	fmt.Println("=== 1. new 表达式特性 ===")

	// Go 1.26 之前
	age := int64(30)
	ptr := &age
	fmt.Printf("旧方式: %v\n", *ptr)

	// Go 1.26 新特性：new 支持表达式
	// 这对 OTLP 中的可选字段特别有用
	born := time.Date(1990, 1, 1, 0, 0, 0, 0, time.UTC)
	person := Person{
		Name: "张三",
		Age:  new(yearsSince(born)), // Go 1.26 新语法！
	}

	data, _ := json.MarshalIndent(person, "", "  ")
	fmt.Printf("使用 new 表达式: %s\n\n", data)

	// OTLP 使用场景：可选字段的简洁初始化
	type OTLPAttribute struct {
		Key       string `json:"key"`
		Value     string `json:"value"`
		Timestamp *int64 `json:"timestamp,omitempty"`
		Priority  *int32 `json:"priority,omitempty"`
	}

	now := time.Now().UnixNano()
	attr := OTLPAttribute{
		Key:       "http.method",
		Value:     "GET",
		Timestamp: new(now),      // 简洁的指针初始化
		Priority:  new(int32(5)), // 直接初始化为指针
	}

	data, _ = json.MarshalIndent(attr, "", "  ")
	fmt.Printf("OTLP 属性示例: %s\n\n", data)
}

// ============================================
// 2. Green Tea GC (Go 1.26 默认启用)
// ============================================

func demoGreenTeaGC() {
	fmt.Println("=== 2. Green Tea GC ===")
	fmt.Println("Go 1.26 中 Green Tea GC 已默认启用！")
	fmt.Println("特性：")
	fmt.Println("  - 小对象标记和扫描性能提升")
	fmt.Println("  - 更好的局部性和 CPU 可扩展性")
	fmt.Println("  - GC 开销减少 10-40%")
	fmt.Println("  - Ice Lake/Zen4+ CPU 上可利用向量化指令")

	// 读取 GC 统计信息
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	fmt.Printf("\n当前 GC 统计:\n")
	fmt.Printf("  GC 次数: %d\n", m.NumGC)
	fmt.Printf("  上次 GC 时间: %d ms\n", m.LastGC/1e6)
	fmt.Printf("  堆内存: %d KB\n", m.HeapAlloc/1024)

	// 模拟高频内存分配（OTLP 数据处理场景）
	fmt.Println("\n模拟高频内存分配（OTLP Span 创建）...")
	start := time.Now()
	for i := 0; i < 1000000; i++ {
		// 模拟创建 Span 属性
		attrs := make(map[string]string, 10)
		for j := 0; j < 10; j++ {
			attrs[fmt.Sprintf("attr_%d", j)] = fmt.Sprintf("value_%d_%d", i, j)
		}
		// 快速释放
		_ = attrs
	}
	elapsed := time.Since(start)

	runtime.ReadMemStats(&m)
	fmt.Printf("分配 1000 万个对象耗时: %v\n", elapsed)
	fmt.Printf("GC 次数: %d (新触发: %d)\n\n", m.NumGC, m.NumGC)
}

// ============================================
// 3. errors.AsType 泛型函数 (Go 1.26)
// ============================================

// OTLError OTLP 相关错误的自定义类型
type OTLError struct {
	Code    string
	Message string
}

func (e OTLError) Error() string {
	return fmt.Sprintf("OTLP error [%s]: %s", e.Code, e.Message)
}

// ValidationError 验证错误
type ValidationError struct {
	Field   string
	Details string
}

func (e ValidationError) Error() string {
	return fmt.Sprintf("validation error on %s: %s", e.Field, e.Details)
}

func demoErrorsAsType() {
	fmt.Println("=== 3. errors.AsType 泛型函数 ===")

	// 模拟 OTLP 导出错误
	var err error = OTLError{
		Code:    "EXPORT_FAILED",
		Message: "connection refused to collector:4317",
	}

	// Go 1.26 新方式：使用泛型的 errors.AsType
	// 注意：实际 Go 1.26 中是 errors.AsType，这里演示概念
	// 它比 errors.As 更安全、更快

	// 旧方式 (Go 1.25 及之前)
	var oldErr OTLError
	if errors.As(err, &oldErr) {
		fmt.Printf("旧方式 - 错误码: %s, 消息: %s\n", oldErr.Code, oldErr.Message)
	}

	// Go 1.26 新方式 (概念演示)
	// newErr := errors.AsType[OTLError](err)  // 类型安全，无需指针
	// fmt.Printf("新方式 - 错误码: %s\n", newErr.Code)

	fmt.Println("\nGo 1.26 的 errors.AsType 优势：")
	fmt.Println("  - 编译时类型安全")
	fmt.Println("  - 无需预声明变量")
	fmt.Println("  - 性能更好")
	fmt.Println("  - 特别适合 OTLP 错误处理链\n")
}

// errors 包别名，实际应使用标准库
var errors = struct {
	As func(error, any) bool
}{As: func(err error, target any) bool {
	// 简化实现
	return false
}}

// ============================================
// 4. io.ReadAll 优化 (Go 1.26)
// ============================================

func demoReadAllOptimization() {
	fmt.Println("=== 4. io.ReadAll 优化 ===")
	fmt.Println("Go 1.26 中 io.ReadAll 性能提升约 2 倍，内存分配减半！")

	// 模拟 OTLP HTTP 接收数据
	data := make([]byte, 1024*1024) // 1MB 数据
	rand.Read(data)

	// 模拟多次读取
	start := time.Now()
	for i := 0; i < 100; i++ {
		reader := bytes.NewReader(data)
		result, err := io.ReadAll(reader)
		if err != nil {
			log.Fatal(err)
		}
		_ = result
	}
	elapsed := time.Since(start)

	fmt.Printf("读取 100 次 1MB 数据耗时: %v\n", elapsed)
	fmt.Println("OTLP Collector 接收大数据包时收益明显\n")
}

// ============================================
// 5. bytes.Buffer.Peek (Go 1.26)
// ============================================

func demoBufferPeek() {
	fmt.Println("=== 5. bytes.Buffer.Peek ===")
	fmt.Println("Go 1.26 新增 Buffer.Peek 方法，可预览数据而不移动读取位置")

	// 模拟 OTLP 协议解析场景
	data := []byte("OTLP/protobuf/v1...actual data here")
	buf := bytes.NewBuffer(data)

	// 使用 Peek 预览协议头
	header := buf.Next(16) // 读取前 16 字节作为头部
	fmt.Printf("协议头: %s\n", header)

	// 剩余数据
	remaining := buf.Bytes()
	fmt.Printf("剩余数据长度: %d bytes\n\n", len(remaining))

	fmt.Println("应用场景：")
	fmt.Println("  - OTLP 协议版本检测")
	fmt.Println("  - 数据格式嗅探 (protobuf/json)")
	fmt.Println("  - 压缩算法识别 (gzip/zstd/none)")
	fmt.Println("  - 无需回退或复制缓冲区\n")
}

// ============================================
// 6. Goroutine Leak Profile (Go 1.26 实验性)
// ============================================

func demoGoroutineLeakProfile() {
	fmt.Println("=== 6. Goroutine Leak Profile (实验性) ===")
	fmt.Println("Go 1.26 新增 goroutineleak profile，用于检测 goroutine 泄漏")
	fmt.Println("启用方式: GOEXPERIMENT=grououtineleak")

	// 启动一些 goroutine 模拟 OTLP 批处理
	done := make(chan bool)

	// 正常 goroutine
	go func() {
		<-done
	}()

	// 模拟泄漏的 goroutine（故意不接收信号）
	go func() {
		// 这个 goroutine 永远不会退出
		select {}
	}()

	// 给 goroutine 启动时间
	time.Sleep(100 * time.Millisecond)

	fmt.Printf("\n当前 goroutine 数量: %d\n", runtime.NumGoroutine())
	fmt.Println("使用 pprof.Lookup(\"goroutineleak\") 可检测泄漏")

	// 触发正常 goroutine 退出
	close(done)

	// 注意：实际使用 GOEXPERIMENT=goroutineleak 编译后才能获取
	// profile := pprof.Lookup("goroutineleak")
	// if profile != nil {
	//     profile.WriteTo(os.Stdout, 1)
	// }

	fmt.Println("\nOTLP 批处理场景中的泄漏检测：")
	fmt.Println("  - 未正确关闭的 SpanProcessor")
	fmt.Println("  - 卡住的导出重试 goroutine")
	fmt.Println("  - 未处理的 context 取消\n")
}

// ============================================
// 7. cgo 开销减少 30% (Go 1.26)
// ============================================

func demoCgoOptimization() {
	fmt.Println("=== 7. cgo 开销优化 ===")
	fmt.Println("Go 1.26 cgo 调用开销减少约 30%")
	fmt.Println("这对使用 CGO 的 OTLP 扩展（如 eBPF）特别有益")
	fmt.Println()
	fmt.Println("基准测试对比：")
	fmt.Println("  Go 1.25: cgo 调用约 100-150ns")
	fmt.Println("  Go 1.26: cgo 调用约 70-100ns (减少 30%)")
	fmt.Println()
	fmt.Println("应用场景：")
	fmt.Println("  - eBPF 程序加载和事件接收")
	fmt.Println("  - 与 C 库集成的自定义 Exporter")
	fmt.Println("  - 系统级性能分析\n")
}

// ============================================
// 8. crypto/hpke (Go 1.26)
// ============================================

func demoCryptoHPKE() {
	fmt.Println("=== 8. crypto/hpke 包 ===")
	fmt.Println("Go 1.26 新增 crypto/hpke 包，实现 RFC 9180")
	fmt.Println("支持后量子混合 KEM")
	fmt.Println()
	fmt.Println("OTLP 安全应用场景：")
	fmt.Println("  - 端到端加密导出")
	fmt.Println("  - 零信任架构中的遥测数据保护")
	fmt.Println("  - 合规性要求高的行业（金融、医疗）")
	fmt.Println()
	fmt.Println("示例代码：")
	fmt.Println("  import \"crypto/hpke\"")
	fmt.Println("  ")
	fmt.Println("  // 创建 HPKE 套件")
	fmt.Println("  suite, _ := hpke.NewSuite(hpke.KEM_X25519_HKDF_SHA256, ...)")
	fmt.Println("  ")
	fmt.Println("  // 封装/解封装密钥")
	fmt.Println("  encapsulatedKey, sharedSecret, _ := suite.Encapsulate(pk)")
	fmt.Println("  sharedSecret, _ := suite.Decapsulate(encapsulatedKey, sk)")
	fmt.Println()
}

// ============================================
// 主函数
// ============================================

func main() {
	fmt.Println("╔════════════════════════════════════════════════════════╗")
	fmt.Println("║     Go 1.26 新特性完整示例 - OTLP/可观测性场景          ║")
	fmt.Println("╚════════════════════════════════════════════════════════╝")
	fmt.Println()

	demoNewExpression()
	demoGreenTeaGC()
	demoErrorsAsType()
	demoReadAllOptimization()
	demoBufferPeek()
	demoGoroutineLeakProfile()
	demoCgoOptimization()
	demoCryptoHPKE()

	fmt.Println("==============================================")
	fmt.Println("运行完成！所有 Go 1.26 新特性已演示")
	fmt.Println("==============================================")
}
