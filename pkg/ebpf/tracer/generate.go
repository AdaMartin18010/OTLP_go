//go:build ignore

package main

import (
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"
)

// This file generates eBPF bytecode using bpf2go
// Run: go generate ./pkg/ebpf/tracer/...

func main() {
	// Find bpf2go
	bpf2go, err := exec.LookPath("bpf2go")
	if err != nil {
		log.Println("bpf2go not found, installing...")
		cmd := exec.Command("go", "install", "github.com/cilium/ebpf/cmd/bpf2go@latest")
		cmd.Stdout = os.Stdout
		cmd.Stderr = os.Stderr
		if err := cmd.Run(); err != nil {
			log.Fatalf("Failed to install bpf2go: %v", err)
		}
		bpf2go = "bpf2go"
	}

	// Get current directory
	wd, err := os.Getwd()
	if err != nil {
		log.Fatalf("Failed to get working directory: %v", err)
	}

	bpfDir := filepath.Join(wd, "bpf")

	// Generate eBPF code
	// Target: linux amd64
	args := []string{
		"-target", "amd64",
		"-type", "http_event",
		"-output-dir", ".",
		"tracer",
		filepath.Join(bpfDir, "http_trace.c"),
	}

	cmd := exec.Command(bpf2go, args...)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	cmd.Env = os.Environ()

	fmt.Println("Running bpf2go...")
	fmt.Printf("Command: %s %v\n", bpf2go, args)

	if err := cmd.Run(); err != nil {
		log.Fatalf("bpf2go failed: %v", err)
	}

	fmt.Println("eBPF code generated successfully!")
}
