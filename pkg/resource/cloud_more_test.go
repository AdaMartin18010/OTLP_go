package resource

import (
	"context"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestGetAWSMetadata(t *testing.T) {
	ctx := context.Background()

	// This test will fail when not on AWS, which is expected
	_, err := getAWSMetadata(ctx, "instance-id")
	// Should return error when not on AWS
	assert.Error(t, err)
}

func TestGetAWSAccountID(t *testing.T) {
	ctx := context.Background()

	// This test will fail when not on AWS, which is expected
	_, err := getAWSAccountID(ctx)
	// Should return error when not on AWS
	assert.Error(t, err)
}

func TestGetGCPMetadata(t *testing.T) {
	ctx := context.Background()

	// This test will fail when not on GCP, which is expected
	_, err := getGCPMetadata(ctx, "instance/id")
	// Should return error when not on GCP
	assert.Error(t, err)
}

func TestDetectAWSIntegration(t *testing.T) {
	ctx := context.Background()

	// This should return error when not running on AWS
	_, err := detectAWS(ctx)
	assert.Error(t, err)
}

func TestDetectGCPIntegration(t *testing.T) {
	ctx := context.Background()

	// This should return error when not running on GCP
	_, err := detectGCP(ctx)
	assert.Error(t, err)
}

func TestDetectAzureIntegration(t *testing.T) {
	ctx := context.Background()

	// This should return error when not running on Azure
	_, err := detectAzure(ctx)
	assert.Error(t, err)
}

func TestCloudProviderDetectorSuccess(t *testing.T) {
	// Test that detector type is correct
	detector := NewCloudProviderDetector("aws")
	require.NotNil(t, detector)
	assert.Equal(t, "cloud", detector.DetectorType())
}
