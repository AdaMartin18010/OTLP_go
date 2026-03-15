// Package resource provides cloud provider resource detection.
package resource

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"strings"
	"time"

	"OTLP_go/pkg/types"
)

const (
	// AWS metadata service endpoint
	awsMetadataEndpoint = "http://169.254.169.254/latest/meta-data"
	awsTokenEndpoint    = "http://169.254.169.254/latest/api/token"

	// GCP metadata service endpoint
	gcpMetadataEndpoint = "http://metadata.google.internal/computeMetadata/v1"

	// Azure metadata service endpoint
	azureMetadataEndpoint = "http://169.254.169.254/metadata/instance?api-version=2021-02-01"
)

// httpClient with timeout for metadata requests
var metadataClient = &http.Client{
	Timeout: 2 * time.Second,
}

// detectAWS detects AWS EC2 resource attributes.
func detectAWS(ctx context.Context) (*types.Resource, error) {
	// Check if we're on AWS
	if !isAWS() {
		return nil, fmt.Errorf("not running on AWS")
	}

	builder := types.NewResourceBuilder()
	builder.WithString("cloud.provider", "aws")

	// Get region
	if region, err := getAWSMetadata(ctx, "placement/region"); err == nil && region != "" {
		builder.WithString("cloud.region", region)
	}

	// Get availability zone
	if zone, err := getAWSMetadata(ctx, "placement/availability-zone"); err == nil && zone != "" {
		builder.WithString("cloud.availability_zone", zone)
	}

	// Get instance ID
	if instanceID, err := getAWSMetadata(ctx, "instance-id"); err == nil && instanceID != "" {
		builder.WithString("host.id", instanceID)
	}

	// Get instance type
	if instanceType, err := getAWSMetadata(ctx, "instance-type"); err == nil && instanceType != "" {
		builder.WithString("host.type", instanceType)
	}

	// Get account ID
	if accountID, err := getAWSAccountID(ctx); err == nil && accountID != "" {
		builder.WithString("cloud.account.id", accountID)
	}

	return builder.Build(), nil
}

// isAWS checks if running on AWS.
func isAWS() bool {
	// Check environment variable
	if os.Getenv("AWS_REGION") != "" || os.Getenv("AWS_DEFAULT_REGION") != "" {
		return true
	}

	// Try to reach metadata service
	req, err := http.NewRequest("PUT", awsTokenEndpoint, nil)
	if err != nil {
		return false
	}
	req.Header.Set("X-aws-ec2-metadata-token-ttl-seconds", "60")

	resp, err := metadataClient.Do(req)
	if err != nil {
		return false
	}
	resp.Body.Close()

	return resp.StatusCode == http.StatusOK
}

// getAWSMetadata gets metadata from AWS IMDS.
func getAWSMetadata(ctx context.Context, path string) (string, error) {
	// Get token
	tokenReq, err := http.NewRequestWithContext(ctx, "PUT", awsTokenEndpoint, nil)
	if err != nil {
		return "", err
	}
	tokenReq.Header.Set("X-aws-ec2-metadata-token-ttl-seconds", "60")

	tokenResp, err := metadataClient.Do(tokenReq)
	if err != nil {
		return "", err
	}
	defer tokenResp.Body.Close()

	if tokenResp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("failed to get IMDS token: %d", tokenResp.StatusCode)
	}

	token, err := io.ReadAll(tokenResp.Body)
	if err != nil {
		return "", err
	}

	// Get metadata
	metadataURL := fmt.Sprintf("%s/%s", awsMetadataEndpoint, path)
	req, err := http.NewRequestWithContext(ctx, "GET", metadataURL, nil)
	if err != nil {
		return "", err
	}
	req.Header.Set("X-aws-ec2-metadata-token", string(token))

	resp, err := metadataClient.Do(req)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("metadata request failed: %d", resp.StatusCode)
	}

	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}

	return string(data), nil
}

// getAWSAccountID gets the AWS account ID.
func getAWSAccountID(ctx context.Context) (string, error) {
	// Try to get from STS or IAM metadata
	identity, err := getAWSMetadata(ctx, "iam/info")
	if err != nil {
		return "", err
	}

	// Parse the JSON response to extract AccountId
	var info struct {
		AccountID string `json:"AccountId"`
	}
	if err := json.Unmarshal([]byte(identity), &info); err == nil && info.AccountID != "" {
		return info.AccountID, nil
	}

	// Try to extract from ARN in the response
	if strings.Contains(identity, "AccountId") {
		// Simple extraction
		start := strings.Index(identity, "AccountId\":\"")
		if start != -1 {
			start += len("AccountId\":\"")
			end := strings.Index(identity[start:], "\"")
			if end != -1 {
				return identity[start : start+end], nil
			}
		}
	}

	return "", fmt.Errorf("account ID not found")
}

// detectGCP detects Google Cloud Platform resource attributes.
func detectGCP(ctx context.Context) (*types.Resource, error) {
	// Check if we're on GCP
	if !isGCP() {
		return nil, fmt.Errorf("not running on GCP")
	}

	builder := types.NewResourceBuilder()
	builder.WithString("cloud.provider", "gcp")

	// Get project ID
	if projectID, err := getGCPMetadata(ctx, "project/project-id"); err == nil && projectID != "" {
		builder.WithString("cloud.account.id", projectID)
	}

	// Get zone
	if zone, err := getGCPMetadata(ctx, "instance/zone"); err == nil && zone != "" {
		// Zone format: projects/<project>/zones/<zone>
		parts := strings.Split(zone, "/")
		if len(parts) > 0 {
			builder.WithString("cloud.availability_zone", parts[len(parts)-1])
		}
	}

	// Get region
	if region, err := getGCPMetadata(ctx, "instance/region"); err == nil && region != "" {
		parts := strings.Split(region, "/")
		if len(parts) > 0 {
			builder.WithString("cloud.region", parts[len(parts)-1])
		}
	}

	// Get instance ID
	if instanceID, err := getGCPMetadata(ctx, "instance/id"); err == nil && instanceID != "" {
		builder.WithString("host.id", instanceID)
	}

	// Get instance type
	if machineType, err := getGCPMetadata(ctx, "instance/machine-type"); err == nil && machineType != "" {
		parts := strings.Split(machineType, "/")
		if len(parts) > 0 {
			builder.WithString("host.type", parts[len(parts)-1])
		}
	}

	// Get hostname
	if hostname, err := getGCPMetadata(ctx, "instance/hostname"); err == nil && hostname != "" {
		builder.WithString("host.name", hostname)
	}

	return builder.Build(), nil
}

// isGCP checks if running on GCP.
func isGCP() bool {
	// Check environment variable
	if os.Getenv("GOOGLE_CLOUD_PROJECT") != "" || os.Getenv("GCP_PROJECT") != "" {
		return true
	}

	// Try to reach metadata service
	req, err := http.NewRequest("GET", gcpMetadataEndpoint+"/", nil)
	if err != nil {
		return false
	}
	req.Header.Set("Metadata-Flavor", "Google")

	resp, err := metadataClient.Do(req)
	if err != nil {
		return false
	}
	resp.Body.Close()

	return resp.StatusCode == http.StatusOK
}

// getGCPMetadata gets metadata from GCP metadata service.
func getGCPMetadata(ctx context.Context, path string) (string, error) {
	url := fmt.Sprintf("%s/%s", gcpMetadataEndpoint, path)
	req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return "", err
	}
	req.Header.Set("Metadata-Flavor", "Google")

	resp, err := metadataClient.Do(req)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("metadata request failed: %d", resp.StatusCode)
	}

	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}

	return string(data), nil
}

// detectAzure detects Microsoft Azure resource attributes.
func detectAzure(ctx context.Context) (*types.Resource, error) {
	// Check if we're on Azure
	if !isAzure() {
		return nil, fmt.Errorf("not running on Azure")
	}

	builder := types.NewResourceBuilder()
	builder.WithString("cloud.provider", "azure")

	// Get instance metadata
	metadata, err := getAzureMetadata(ctx)
	if err != nil {
		return builder.Build(), nil
	}

	// Extract information from metadata
	if compute, ok := metadata["compute"].(map[string]interface{}); ok {
		if vmID, ok := compute["vmId"].(string); ok && vmID != "" {
			builder.WithString("host.id", vmID)
		}
		if name, ok := compute["name"].(string); ok && name != "" {
			builder.WithString("host.name", name)
		}
		if vmSize, ok := compute["vmSize"].(string); ok && vmSize != "" {
			builder.WithString("host.type", vmSize)
		}
		if subscriptionID, ok := compute["subscriptionId"].(string); ok && subscriptionID != "" {
			builder.WithString("cloud.account.id", subscriptionID)
		}
		if location, ok := compute["location"].(string); ok && location != "" {
			builder.WithString("cloud.region", location)
		}
		if resourceGroup, ok := compute["resourceGroupName"].(string); ok && resourceGroup != "" {
			builder.WithString("azure.resource_group.name", resourceGroup)
		}
		if osType, ok := compute["osType"].(string); ok && osType != "" {
			builder.WithString("os.type", strings.ToLower(osType))
		}
	}

	return builder.Build(), nil
}

// isAzure checks if running on Azure.
func isAzure() bool {
	// Check environment variables
	if os.Getenv("AZURE_SUBSCRIPTION_ID") != "" || os.Getenv("WEBSITE_RESOURCE_GROUP") != "" {
		return true
	}

	// Try to reach metadata service
	req, err := http.NewRequest("GET", azureMetadataEndpoint, nil)
	if err != nil {
		return false
	}
	req.Header.Set("Metadata", "true")

	resp, err := metadataClient.Do(req)
	if err != nil {
		return false
	}
	resp.Body.Close()

	return resp.StatusCode == http.StatusOK
}

// getAzureMetadata gets metadata from Azure metadata service.
func getAzureMetadata(ctx context.Context) (map[string]interface{}, error) {
	req, err := http.NewRequestWithContext(ctx, "GET", azureMetadataEndpoint, nil)
	if err != nil {
		return nil, err
	}
	req.Header.Set("Metadata", "true")

	resp, err := metadataClient.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("metadata request failed: %d", resp.StatusCode)
	}

	var metadata map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&metadata); err != nil {
		return nil, err
	}

	return metadata, nil
}

// CloudProvider represents a cloud provider type.
type CloudProvider int

const (
	// CloudProviderUnknown indicates an unknown cloud provider.
	CloudProviderUnknown CloudProvider = iota
	// CloudProviderAWS indicates Amazon Web Services.
	CloudProviderAWS
	// CloudProviderGCP indicates Google Cloud Platform.
	CloudProviderGCP
	// CloudProviderAzure indicates Microsoft Azure.
	CloudProviderAzure
)

// String returns the string representation of the cloud provider.
func (c CloudProvider) String() string {
	switch c {
	case CloudProviderAWS:
		return "aws"
	case CloudProviderGCP:
		return "gcp"
	case CloudProviderAzure:
		return "azure"
	default:
		return "unknown"
	}
}

// DetectCloudProvider detects which cloud provider we're running on.
func DetectCloudProvider() CloudProvider {
	if isAWS() {
		return CloudProviderAWS
	}
	if isGCP() {
		return CloudProviderGCP
	}
	if isAzure() {
		return CloudProviderAzure
	}
	return CloudProviderUnknown
}

// WithCloudProvider creates an option that includes cloud provider detection.
func WithCloudProvider(provider string) Option {
	return func(c *Config) {
		switch provider {
		case "aws", "gcp", "azure":
			c.Detectors = append(c.Detectors, NewCloudProviderDetector(provider))
		default:
			// Auto-detect
			provider := DetectCloudProvider()
			if provider != CloudProviderUnknown {
				c.Detectors = append(c.Detectors, NewCloudProviderDetector(provider.String()))
			}
		}
	}
}
