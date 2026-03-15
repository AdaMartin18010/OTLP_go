// Package resource provides host resource detection capabilities.
package resource

import (
	"bufio"
	"context"
	"fmt"
	"os"
	"os/exec"
	"runtime"
	"strings"

	"OTLP_go/pkg/types"
)

// HostDetector detects host-related resource attributes.
type HostDetector struct {
	// IncludeHostID includes the host ID in the detected attributes.
	IncludeHostID bool
	// IncludeHostType includes the host type in the detected attributes.
	IncludeHostType bool
}

// DetectorType returns the type of detector.
func (d *HostDetector) DetectorType() string {
	return "host"
}

// Detect detects host-related resource attributes.
func (d *HostDetector) Detect(ctx context.Context) (*types.Resource, error) {
	builder := types.NewResourceBuilder()

	// Host name
	if hostname, err := os.Hostname(); err == nil && hostname != "" {
		builder.WithString("host.name", hostname)
	}

	// OS type
	osType := runtime.GOOS
	if osType != "" {
		builder.WithString("os.type", osType)
	}

	// OS description (version)
	if osDesc := getOSDescription(); osDesc != "" {
		builder.WithString("os.description", osDesc)
	}

	// Architecture
	arch := runtime.GOARCH
	if arch != "" {
		builder.WithString("host.arch", arch)
	}

	// Host ID (optional)
	if d.IncludeHostID {
		if hostID := getHostID(); hostID != "" {
			builder.WithString("host.id", hostID)
		}
	}

	// Host type (optional)
	if d.IncludeHostType {
		if hostType := getHostType(); hostType != "" {
			builder.WithString("host.type", hostType)
		}
	}

	return builder.Build(), nil
}

// getOSDescription gets the OS description/version.
func getOSDescription() string {
	switch runtime.GOOS {
	case "linux":
		return getLinuxVersion()
	case "darwin":
		return getDarwinVersion()
	case "windows":
		return getWindowsVersion()
	default:
		return runtime.Version()
	}
}

// getLinuxVersion gets the Linux distribution and version.
func getLinuxVersion() string {
	// Try /etc/os-release first
	if data, err := os.ReadFile("/etc/os-release"); err == nil {
		return parseOSRelease(string(data))
	}

	// Try /etc/lsb-release
	if data, err := os.ReadFile("/etc/lsb-release"); err == nil {
		return parseLSBRelease(string(data))
	}

	return ""
}

// parseOSRelease parses /etc/os-release content.
func parseOSRelease(content string) string {
	var name, version string
	scanner := bufio.NewScanner(strings.NewReader(content))
	for scanner.Scan() {
		line := scanner.Text()
		if strings.HasPrefix(line, "NAME=") {
			name = strings.Trim(strings.TrimPrefix(line, "NAME="), "\"")
		} else if strings.HasPrefix(line, "VERSION_ID=") {
			version = strings.Trim(strings.TrimPrefix(line, "VERSION_ID="), "\"")
		}
	}
	if name != "" {
		if version != "" {
			return fmt.Sprintf("%s %s", name, version)
		}
		return name
	}
	return ""
}

// parseLSBRelease parses /etc/lsb-release content.
func parseLSBRelease(content string) string {
	var dist, desc string
	scanner := bufio.NewScanner(strings.NewReader(content))
	for scanner.Scan() {
		line := scanner.Text()
		if strings.HasPrefix(line, "DISTRIB_ID=") {
			dist = strings.Trim(strings.TrimPrefix(line, "DISTRIB_ID="), "\"")
		} else if strings.HasPrefix(line, "DISTRIB_DESCRIPTION=") {
			desc = strings.Trim(strings.TrimPrefix(line, "DISTRIB_DESCRIPTION="), "\"")
		}
	}
	if desc != "" {
		return desc
	}
	return dist
}

// getDarwinVersion gets macOS version.
func getDarwinVersion() string {
	cmd := exec.Command("sw_vers", "-productVersion")
	out, err := cmd.Output()
	if err == nil {
		return strings.TrimSpace(string(out))
	}
	return ""
}

// getWindowsVersion gets Windows version.
func getWindowsVersion() string {
	// Try to get Windows version from registry or commands
	cmd := exec.Command("cmd", "/c", "ver")
	out, err := cmd.Output()
	if err == nil {
		return strings.TrimSpace(string(out))
	}
	return ""
}

// getHostID gets a unique host identifier.
func getHostID() string {
	switch runtime.GOOS {
	case "linux":
		// Try machine-id
		if data, err := os.ReadFile("/etc/machine-id"); err == nil {
			return strings.TrimSpace(string(data))
		}
		if data, err := os.ReadFile("/var/lib/dbus/machine-id"); err == nil {
			return strings.TrimSpace(string(data))
		}
	case "darwin":
		// Get hardware UUID on macOS
		cmd := exec.Command("system_profiler", "SPHardwareDataType")
		out, err := cmd.Output()
		if err == nil {
			return extractUUID(string(out))
		}
	case "windows":
		// Get machine GUID from registry
		cmd := exec.Command("reg", "query", "HKEY_LOCAL_MACHINE\\SOFTWARE\\Microsoft\\Cryptography", "/v", "MachineGuid")
		out, err := cmd.Output()
		if err == nil {
			return extractWindowsGUID(string(out))
		}
	}
	return ""
}

// extractUUID extracts UUID from system_profiler output.
func extractUUID(output string) string {
	for _, line := range strings.Split(output, "\n") {
		if strings.Contains(line, "Hardware UUID") {
			parts := strings.Split(line, ":")
			if len(parts) > 1 {
				return strings.TrimSpace(parts[1])
			}
		}
	}
	return ""
}

// extractWindowsGUID extracts GUID from reg query output.
func extractWindowsGUID(output string) string {
	lines := strings.Split(output, "\n")
	for _, line := range lines {
		if strings.Contains(line, "MachineGuid") {
			parts := strings.Fields(line)
			if len(parts) >= 3 {
				return parts[2]
			}
		}
	}
	return ""
}

// getHostType gets the host machine type.
func getHostType() string {
	switch runtime.GOOS {
	case "linux":
		cmd := exec.Command("uname", "-m")
		out, err := cmd.Output()
		if err == nil {
			return strings.TrimSpace(string(out))
		}
	case "darwin":
		cmd := exec.Command("uname", "-m")
		out, err := cmd.Output()
		if err == nil {
			return strings.TrimSpace(string(out))
		}
	}
	return runtime.GOARCH
}

// importRuntimeInfo imports runtime information into the builder.
func importRuntimeInfo(builder *types.ResourceBuilder) {
	// Process runtime info
	builder.WithString("process.runtime.name", "go")
	builder.WithString("process.runtime.version", runtime.Version())
	builder.WithString("process.runtime.description", runtime.GOOS+"/"+runtime.GOARCH)
}

// importOSInfo imports OS information into the builder.
func importOSInfo(builder *types.ResourceBuilder) {
	builder.WithString("os.type", runtime.GOOS)
	if version := getOSDescription(); version != "" {
		builder.WithString("os.version", version)
	}
}

// detectContainer detects container information.
func detectContainer(ctx context.Context) (*types.Resource, error) {
	builder := types.NewResourceBuilder()

	// Check if running in a container
	if isInContainer() {
		// Try to get container ID from cgroup
		if containerID := getContainerID(); containerID != "" {
			builder.WithString("container.id", containerID)
		}

		// Try to detect container runtime
		if runtime := detectContainerRuntime(); runtime != "" {
			builder.WithString("container.runtime", runtime)
		}
	}

	return builder.Build(), nil
}

// isInContainer checks if the process is running inside a container.
func isInContainer() bool {
	// Check for Docker
	if _, err := os.Stat("/.dockerenv"); err == nil {
		return true
	}

	// Check for containerd or other runtimes via cgroup
	if data, err := os.ReadFile("/proc/self/cgroup"); err == nil {
		content := string(data)
		if strings.Contains(content, "docker") ||
			strings.Contains(content, "containerd") ||
			strings.Contains(content, "kubepods") {
			return true
		}
	}

	return false
}

// getContainerID extracts container ID from cgroup.
func getContainerID() string {
	data, err := os.ReadFile("/proc/self/cgroup")
	if err != nil {
		return ""
	}

	lines := strings.Split(string(data), "\n")
	for _, line := range lines {
		// Look for patterns like:
		// docker: /docker/<container_id>
		// containerd: /system.slice/containerd.service/...
		// k8s: /kubepods/.../<pod_uid>/...

		if strings.Contains(line, "docker") {
			parts := strings.Split(line, "/")
			for _, part := range parts {
				part = strings.TrimSpace(part)
				// Container ID is typically 64 hex characters
				if len(part) == 64 {
					return part
				}
			}
		}

		if strings.Contains(line, "containerd") {
			parts := strings.Split(line, "/")
			for _, part := range parts {
				part = strings.TrimSpace(part)
				// containerd ID may have cri-containerd- prefix
				if strings.Contains(part, "cri-containerd-") {
					return strings.TrimPrefix(part, "cri-containerd-")
				}
			}
		}
	}

	return ""
}

// detectContainerRuntime detects which container runtime is being used.
func detectContainerRuntime() string {
	data, err := os.ReadFile("/proc/self/cgroup")
	if err != nil {
		return ""
	}

	content := string(data)
	if strings.Contains(content, "docker") {
		return "docker"
	}
	if strings.Contains(content, "containerd") {
		return "containerd"
	}
	if strings.Contains(content, "kubepods") {
		return "kubernetes"
	}

	return ""
}

// GetHostInfo returns detailed host information.
type HostInfo struct {
	Hostname    string
	OS          string
	OSVersion   string
	Arch        string
	HostID      string
	NumCPU      int
	Container   bool
	ContainerID string
}

// GetHostInfo returns detailed information about the host.
func GetHostInfo() *HostInfo {
	info := &HostInfo{
		NumCPU: runtime.NumCPU(),
	}

	if hostname, err := os.Hostname(); err == nil {
		info.Hostname = hostname
	}

	info.OS = runtime.GOOS
	info.OSVersion = getOSDescription()
	info.Arch = runtime.GOARCH
	info.HostID = getHostID()
	info.Container = isInContainer()
	if info.Container {
		info.ContainerID = getContainerID()
	}

	return info
}

// ToResource converts HostInfo to a Resource.
func (h *HostInfo) ToResource() *types.Resource {
	builder := types.NewResourceBuilder()

	if h.Hostname != "" {
		builder.WithString("host.name", h.Hostname)
	}
	if h.OS != "" {
		builder.WithString("os.type", h.OS)
	}
	if h.OSVersion != "" {
		builder.WithString("os.version", h.OSVersion)
	}
	if h.Arch != "" {
		builder.WithString("host.arch", h.Arch)
	}
	if h.HostID != "" {
		builder.WithString("host.id", h.HostID)
	}
	if h.Container {
		if h.ContainerID != "" {
			builder.WithString("container.id", h.ContainerID)
		}
	}

	return builder.Build()
}
