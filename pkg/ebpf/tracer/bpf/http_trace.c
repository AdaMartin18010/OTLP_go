//go:build ignore

// http_trace.c - eBPF program for HTTP request tracing
// This program attaches uprobes to net/http.(*Server).ServeHTTP
// to capture HTTP requests without modifying application code

#include "vmlinux.h"
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>
#include <bpf/bpf_core_read.h>

// Maximum path length
#define MAX_PATH_LEN 128
#define MAX_METHOD_LEN 8
#define MAX_REMOTE_ADDR_LEN 64

// HTTP event structure - must match Go struct exactly
struct http_event {
    u64 timestamp_ns;       // Event timestamp
    u32 pid;                // Process ID
    u32 tid;                // Thread ID
    u64 duration_ns;        // Request duration
    u16 status_code;        // HTTP status code
    u16 method_len;         // Method string length
    u16 path_len;           // Path string length
    char method[MAX_METHOD_LEN];
    char path[MAX_PATH_LEN];
    char remote_addr[MAX_REMOTE_ADDR_LEN];
};

// Ring buffer for sending events to userspace
struct {
    __uint(type, BPF_MAP_TYPE_RINGBUF);
    __uint(max_entries, 256 * 1024); // 256KB buffer
} events SEC(".maps");

// Active requests map: key=pid_tid, value=start_timestamp
struct {
    __uint(type, BPF_MAP_TYPE_HASH);
    __uint(max_entries, 10240);
    __type(key, u64);       // pid << 32 | tid
    __type(value, u64);     // start timestamp (nanoseconds)
} active_requests SEC(".maps");

// Request context map for storing request details
struct request_ctx {
    u64 start_ns;
    char method[MAX_METHOD_LEN];
    char path[MAX_PATH_LEN];
};

struct {
    __uint(type, BPF_MAP_TYPE_HASH);
    __uint(max_entries, 10240);
    __type(key, u64);               // pid << 32 | tid
    __type(value, struct request_ctx);
} request_contexts SEC(".maps");

// Helper to get current PID and TID
static __always_inline u64 get_pid_tgid() {
    return bpf_get_current_pid_tgid();
}

// uprobe: ServeHTTP entry
// Signature: func (s *Server) ServeHTTP(w ResponseWriter, r *Request)
SEC("uprobe/net_http_Server_ServeHTTP")
int BPF_KPROBE(trace_serve_http_entry, void *w, void *r) {
    u64 pid_tgid = get_pid_tgid();
    u64 timestamp = bpf_ktime_get_ns();
    
    // Store start timestamp
    bpf_map_update_elem(&active_requests, &pid_tgid, &timestamp, BPF_ANY);
    
    // Store request context
    struct request_ctx ctx = {};
    ctx.start_ns = timestamp;
    
    // Try to read method from *Request
    // Request.Method is at offset 0 in Request struct (string header)
    if (r != NULL) {
        // Read method string
        // Go string: {ptr, len}
        u64 method_ptr = 0;
        u64 method_len = 0;
        
        // For Go 1.20+, Method is first field
        bpf_probe_read(&method_ptr, sizeof(method_ptr), r);
        bpf_probe_read(&method_len, sizeof(method_len), r + sizeof(void*));
        
        if (method_len > 0 && method_len < MAX_METHOD_LEN) {
            bpf_probe_read_user_str(ctx.method, sizeof(ctx.method), (void*)method_ptr);
        } else {
            __builtin_memcpy(ctx.method, "GET", 4);
        }
        
        // Read RequestURI (path)
        // RequestURI is at offset ~48 (depends on Go version)
        // This is simplified - actual offset needs verification
        void *uri_ptr = NULL;
        u64 uri_len = 0;
        
        // Read RequestURI field (offset may vary)
        bpf_probe_read(&uri_ptr, sizeof(uri_ptr), r + 48);
        bpf_probe_read(&uri_len, sizeof(uri_len), r + 48 + sizeof(void*));
        
        if (uri_len > 0 && uri_len < MAX_PATH_LEN) {
            bpf_probe_read_user_str(ctx.path, sizeof(ctx.path), uri_ptr);
        } else {
            __builtin_memcpy(ctx.path, "/", 2);
        }
    }
    
    bpf_map_update_elem(&request_contexts, &pid_tgid, &ctx, BPF_ANY);
    
    return 0;
}

// uretprobe: ServeHTTP exit
SEC("uretprobe/net_http_Server_ServeHTTP")
int BPF_KPROBE(trace_serve_http_exit) {
    u64 pid_tgid = get_pid_tgid();
    u32 pid = pid_tgid >> 32;
    u32 tid = (u32)pid_tgid;
    
    // Get start timestamp
    u64 *start_ts = bpf_map_lookup_elem(&active_requests, &pid_tgid);
    if (!start_ts) {
        return 0;
    }
    
    // Get request context
    struct request_ctx *ctx = bpf_map_lookup_elem(&request_contexts, &pid_tgid);
    if (!ctx) {
        bpf_map_delete_elem(&active_requests, &pid_tgid);
        return 0;
    }
    
    // Reserve space in ring buffer
    struct http_event *e = bpf_ringbuf_reserve(&events, sizeof(*e), 0);
    if (!e) {
        bpf_map_delete_elem(&active_requests, &pid_tgid);
        bpf_map_delete_elem(&request_contexts, &pid_tgid);
        return 0;
    }
    
    // Fill event data
    e->timestamp_ns = *start_ts;
    e->pid = pid;
    e->tid = tid;
    e->duration_ns = bpf_ktime_get_ns() - *start_ts;
    e->status_code = 200; // Would need to extract from ResponseWriter
    
    // Copy method and path
    __builtin_memcpy(e->method, ctx->method, MAX_METHOD_LEN);
    __builtin_memcpy(e->path, ctx->path, MAX_PATH_LEN);
    
    // Remote address placeholder
    __builtin_memcpy(e->remote_addr, "127.0.0.1:0", 12);
    
    e->method_len = 0;
    for (int i = 0; i < MAX_METHOD_LEN && e->method[i]; i++) {
        e->method_len++;
    }
    
    e->path_len = 0;
    for (int i = 0; i < MAX_PATH_LEN && e->path[i]; i++) {
        e->path_len++;
    }
    
    // Submit event
    bpf_ringbuf_submit(e, 0);
    
    // Cleanup
    bpf_map_delete_elem(&active_requests, &pid_tgid);
    bpf_map_delete_elem(&request_contexts, &pid_tgid);
    
    return 0;
}

// License
char LICENSE[] SEC("license") = "Dual MIT/GPL";

// Version information
__u32 VERSION SEC("version") = 1;
