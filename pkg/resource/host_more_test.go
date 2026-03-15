package resource

import (
	"context"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestDetectContainer(t *testing.T) {
	ctx := context.Background()
	res, err := detectContainer(ctx)
	require.NoError(t, err)
	require.NotNil(t, res)
	// Should not error even if not in container
}

func TestDetectContainerRuntimeMore(t *testing.T) {
	// This may or may not return a value depending on environment
	runtime := detectContainerRuntime()
	// Just ensure it doesn't panic
	_ = runtime
}

func TestGetContainerIDMore(t *testing.T) {
	// This may or may not return a value depending on environment
	id := getContainerID()
	// Just ensure it doesn't panic
	_ = id
}

func TestGetLinuxVersion(t *testing.T) {
	// This may or may not return a value depending on environment
	version := getLinuxVersion()
	// Just ensure it doesn't panic
	_ = version
}

func TestGetDarwinVersion(t *testing.T) {
	// This may or may not return a value depending on environment
	version := getDarwinVersion()
	// Just ensure it doesn't panic
	_ = version
}

func TestGetWindowsVersion(t *testing.T) {
	// This may or may not return a value depending on environment
	version := getWindowsVersion()
	// Just ensure it doesn't panic
	_ = version
}

func TestGetHostIDWithMock(t *testing.T) {
	// Test that getHostID doesn't panic
	id := getHostID()
	// Just ensure it doesn't panic - result depends on OS
	_ = id
}

func TestHostDetectorWithOptions(t *testing.T) {
	ctx := context.Background()

	t.Run("with all options enabled", func(t *testing.T) {
		detector := &HostDetector{
			IncludeHostID:   true,
			IncludeHostType: true,
		}
		res, err := detector.Detect(ctx)
		require.NoError(t, err)
		require.NotNil(t, res)

		// Should have host info
		assert.NotEmpty(t, res.GetString("host.name"))
		assert.NotEmpty(t, res.GetString("os.type"))
		assert.NotEmpty(t, res.GetString("host.arch"))
	})

	t.Run("with no options enabled", func(t *testing.T) {
		detector := &HostDetector{
			IncludeHostID:   false,
			IncludeHostType: false,
		}
		res, err := detector.Detect(ctx)
		require.NoError(t, err)
		require.NotNil(t, res)

		// Should still have basic host info
		assert.NotEmpty(t, res.GetString("host.name"))
		assert.NotEmpty(t, res.GetString("os.type"))
	})
}

func TestIsInContainerDetection(t *testing.T) {
	// Just ensure function doesn't panic
	_ = isInContainer()
}
