package resource

import (
	"context"
	"os"
	"runtime"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestHostDetector(t *testing.T) {
	ctx := context.Background()
	detector := &HostDetector{}

	t.Run("detects host attributes", func(t *testing.T) {
		res, err := detector.Detect(ctx)
		require.NoError(t, err)
		require.NotNil(t, res)

		// Should have host name
		hostname, _ := os.Hostname()
		assert.Equal(t, hostname, res.GetString("host.name"))

		// Should have OS type
		assert.Equal(t, runtime.GOOS, res.GetString("os.type"))

		// Should have architecture
		assert.Equal(t, runtime.GOARCH, res.GetString("host.arch"))
	})

	t.Run("returns correct detector type", func(t *testing.T) {
		assert.Equal(t, "host", detector.DetectorType())
	})

	t.Run("with host ID enabled", func(t *testing.T) {
		detectorWithID := &HostDetector{IncludeHostID: true}
		res, err := detectorWithID.Detect(ctx)
		require.NoError(t, err)

		// May or may not have host.id depending on OS
		// Just check it doesn't error
		_ = res.GetString("host.id")
	})

	t.Run("with host type enabled", func(t *testing.T) {
		detectorWithType := &HostDetector{IncludeHostType: true}
		res, err := detectorWithType.Detect(ctx)
		require.NoError(t, err)

		// May or may not have host.type depending on OS
		// Just check it doesn't error
		_ = res.GetString("host.type")
	})
}

func TestGetOSDescription(t *testing.T) {
	desc := getOSDescription()
	// Should return something, but content depends on OS
	// Just ensure it doesn't panic
	_ = desc
}

func TestGetHostID(t *testing.T) {
	hostID := getHostID()
	// Result depends on OS and system configuration
	// Just ensure it doesn't panic
	_ = hostID
}

func TestGetHostType(t *testing.T) {
	hostType := getHostType()
	// Should return architecture at minimum
	assert.NotEmpty(t, hostType)
}

func TestParseOSRelease(t *testing.T) {
	content := `NAME="Ubuntu"
VERSION="20.04.3 LTS (Focal Fossa)"
ID=ubuntu
ID_LIKE=debian
PRETTY_NAME="Ubuntu 20.04.3 LTS"
VERSION_ID="20.04"
HOME_URL="https://www.ubuntu.com/"
SUPPORT_URL="https://help.ubuntu.com/"
BUG_REPORT_URL="https://bugs.launchpad.net/ubuntu/"
PRIVACY_POLICY_URL="https://www.ubuntu.com/legal/terms-and-policies/privacy-policy"
VERSION_CODENAME=focal
UBUNTU_CODENAME=focal`

	result := parseOSRelease(content)
	assert.Equal(t, "Ubuntu 20.04", result)
}

func TestParseOSReleaseMinimal(t *testing.T) {
	content := `NAME="Alpine Linux"
ID=alpine
VERSION_ID=3.14.0`

	result := parseOSRelease(content)
	assert.Equal(t, "Alpine Linux 3.14.0", result)
}

func TestParseOSReleaseNoVersion(t *testing.T) {
	content := `NAME="Custom Linux"`

	result := parseOSRelease(content)
	assert.Equal(t, "Custom Linux", result)
}

func TestParseLSBRelease(t *testing.T) {
	content := `DISTRIB_ID=Ubuntu
DISTRIB_RELEASE=20.04
DISTRIB_CODENAME=focal
DISTRIB_DESCRIPTION="Ubuntu 20.04.3 LTS"`

	result := parseLSBRelease(content)
	assert.Equal(t, "Ubuntu 20.04.3 LTS", result)
}

func TestParseLSBReleaseMinimal(t *testing.T) {
	content := `DISTRIB_ID=Debian
DISTRIB_RELEASE=11`

	result := parseLSBRelease(content)
	assert.Equal(t, "Debian", result)
}

func TestIsInContainer(t *testing.T) {
	// This test's result depends on the test environment
	// Just ensure it doesn't panic
	_ = isInContainer()
}

func TestGetContainerID(t *testing.T) {
	// This test's result depends on the test environment
	// Just ensure it doesn't panic
	_ = getContainerID()
}

func TestDetectContainerRuntime(t *testing.T) {
	// This test's result depends on the test environment
	// Just ensure it doesn't panic
	_ = detectContainerRuntime()
}

func TestGetHostInfo(t *testing.T) {
	info := GetHostInfo()
	require.NotNil(t, info)

	// Check basic info is populated
	hostname, _ := os.Hostname()
	assert.Equal(t, hostname, info.Hostname)
	assert.Equal(t, runtime.GOOS, info.OS)
	assert.Equal(t, runtime.GOARCH, info.Arch)
	assert.Equal(t, runtime.NumCPU(), info.NumCPU)
}

func TestHostInfoToResource(t *testing.T) {
	info := &HostInfo{
		Hostname:    "test-host",
		OS:          "linux",
		OSVersion:   "20.04",
		Arch:        "amd64",
		HostID:      "host-123",
		Container:   true,
		ContainerID: "container-456",
	}

	res := info.ToResource()
	require.NotNil(t, res)

	assert.Equal(t, "test-host", res.GetString("host.name"))
	assert.Equal(t, "linux", res.GetString("os.type"))
	assert.Equal(t, "amd64", res.GetString("host.arch"))
	assert.Equal(t, "host-123", res.GetString("host.id"))
	assert.Equal(t, "container-456", res.GetString("container.id"))
}

func TestHostInfoToResourceNoContainer(t *testing.T) {
	info := &HostInfo{
		Hostname:  "test-host",
		OS:        "linux",
		Arch:      "amd64",
		Container: false,
	}

	res := info.ToResource()
	require.NotNil(t, res)

	// Should not have container.id when not in container
	_, ok := res.Get("container.id")
	assert.False(t, ok)
}

func TestExtractUUID(t *testing.T) {
	output := `Hardware:

    Hardware Overview:

      Model Name: MacBook Pro
      Model Identifier: MacBookPro18,1
      Model Number: MK1A3xx/A
      Chip: Apple M1 Pro
      Total Number of Cores: 10 (8 performance and 2 efficiency)
      Memory: 16 GB
      System Firmware Version: 7429.61.2
      OS Loader Version: 7429.61.2
      Hardware UUID: 12345678-1234-1234-1234-123456789ABC
      Provisioning UDID: 00001234-1234123412341234123412341234
      Activation Lock Status: Disabled`

	uuid := extractUUID(output)
	assert.Equal(t, "12345678-1234-1234-1234-123456789ABC", uuid)
}

func TestExtractUUIDNotFound(t *testing.T) {
	output := `Hardware Overview:
      Model Name: MacBook Pro`

	uuid := extractUUID(output)
	assert.Empty(t, uuid)
}

func TestExtractWindowsGUID(t *testing.T) {
	output := `
HKEY_LOCAL_MACHINE\SOFTWARE\Microsoft\Cryptography
    MachineGuid    REG_SZ    12345678-1234-1234-1234-123456789ABC`

	guid := extractWindowsGUID(output)
	assert.Equal(t, "12345678-1234-1234-1234-123456789ABC", guid)
}

func TestExtractWindowsGUIDNotFound(t *testing.T) {
	output := `Some other registry output`

	guid := extractWindowsGUID(output)
	assert.Empty(t, guid)
}
