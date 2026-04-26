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

var (
	// AWS metadata service endpoint
	awsMetadataEndpoint = "http://169.254.169.254/latest/meta-data"
	awsTokenEndpoint    = "http://169.254.169.254/latest/api/token"

	// GCP metadata service endpoint
	gcpMetadataEndpoint = "http://metadata.google.internal/computeMetadata/v1"

	// Azure metadata service endpoint
	azureMetadataEndpoint = "http://169.254.169.254/metadata/instance?api-version=2021-02-01"
)

const (
	// AWS ECS metadata environment variables
	awsECSMetadataEnvV4 = "ECS_CONTAINER_METADATA_URI_V4"
	awsECSMetadataEnv   = "ECS_CONTAINER_METADATA_URI"

	// AWS EKS environment variable
	awsEKSEnv = "AWS_EXECUTION_ENV"

	// Kubernetes environment variable
	k8sServiceHost = "KUBERNETES_SERVICE_HOST"
)

// httpClient with timeout for metadata requests
var metadataClient = &http.Client{
	Timeout: 2 * time.Second,
}

// detectAWS detects AWS resource attributes including EC2, ECS, and EKS.
func detectAWS(ctx context.Context) (*types.Resource, error) {
	if !isAWS() {
		return nil, fmt.Errorf("not running on AWS")
	}

	builder := types.NewResourceBuilder()
	builder.WithString("cloud.provider", "aws")

	// Get region (common to all AWS platforms)
	if region, err := getAWSMetadata(ctx, "placement/region"); err == nil && region != "" {
		builder.WithString("cloud.region", region)
	}

	// Get availability zone (common to all AWS platforms)
	if zone, err := getAWSMetadata(ctx, "placement/availability-zone"); err == nil && zone != "" {
		builder.WithString("cloud.availability_zone", zone)
	}

	// Get account ID (common to all AWS platforms)
	if accountID, err := getAWSAccountID(ctx); err == nil && accountID != "" {
		builder.WithString("cloud.account.id", accountID)
	}

	// Detect specific AWS platform
	switch {
	case isECS():
		builder.WithString("cloud.platform", "aws_ecs")
		addECSAttributes(ctx, builder)
	case isEKS():
		builder.WithString("cloud.platform", "aws_eks")
		addEKSAttributes(ctx, builder)
	default:
		builder.WithString("cloud.platform", "aws_ec2")
		addEC2Attributes(ctx, builder)
	}

	return builder.Build(), nil
}

// isAWS checks if running on AWS.
func isAWS() bool {
	if os.Getenv("AWS_REGION") != "" || os.Getenv("AWS_DEFAULT_REGION") != "" {
		return true
	}

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
	identity, err := getAWSMetadata(ctx, "iam/info")
	if err != nil {
		return "", err
	}

	var info struct {
		AccountID string `json:"AccountId"`
	}
	if err := json.Unmarshal([]byte(identity), &info); err == nil && info.AccountID != "" {
		return info.AccountID, nil
	}

	if strings.Contains(identity, "AccountId") {
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

// addEC2Attributes adds EC2-specific attributes.
func addEC2Attributes(ctx context.Context, builder *types.ResourceBuilder) {
	if instanceID, err := getAWSMetadata(ctx, "instance-id"); err == nil && instanceID != "" {
		builder.WithString("host.id", instanceID)
	}
	if instanceType, err := getAWSMetadata(ctx, "instance-type"); err == nil && instanceType != "" {
		builder.WithString("host.type", instanceType)
	}
}

// isECS checks if running on AWS ECS.
func isECS() bool {
	return os.Getenv(awsECSMetadataEnvV4) != "" || os.Getenv(awsECSMetadataEnv) != ""
}

// addECSAttributes adds ECS-specific attributes.
func addECSAttributes(ctx context.Context, builder *types.ResourceBuilder) {
	metadataURI := os.Getenv(awsECSMetadataEnvV4)
	if metadataURI == "" {
		metadataURI = os.Getenv(awsECSMetadataEnv)
	}
	if metadataURI == "" {
		return
	}

	metadata, err := getECSMetadata(ctx, metadataURI)
	if err != nil {
		return
	}

	if taskARN, ok := metadata["TaskARN"].(string); ok && taskARN != "" {
		builder.WithString("aws.ecs.task.arn", taskARN)
	}
	if clusterARN, ok := metadata["Cluster"].(string); ok && clusterARN != "" {
		builder.WithString("aws.ecs.cluster.arn", clusterARN)
	}
	if family, ok := metadata["Family"].(string); ok && family != "" {
		builder.WithString("aws.ecs.task.family", family)
	}
	if revision, ok := metadata["Revision"].(string); ok && revision != "" {
		builder.WithString("aws.ecs.task.revision", revision)
	}
	if launchType, ok := metadata["LaunchType"].(string); ok && launchType != "" {
		builder.WithString("aws.ecs.launchtype", strings.ToLower(launchType))
	}

	// Container-specific metadata
	if containers, ok := metadata["Containers"].([]interface{}); ok && len(containers) > 0 {
		if first, ok := containers[0].(map[string]interface{}); ok {
			if containerARN, ok := first["ContainerARN"].(string); ok && containerARN != "" {
				builder.WithString("aws.ecs.container.arn", containerARN)
			}
			if name, ok := first["Name"].(string); ok && name != "" {
				builder.WithString("container.name", name)
			}
			if image, ok := first["Image"].(string); ok && image != "" {
				builder.WithString("container.image.name", image)
			}
		}
	}
}

// getECSMetadata fetches ECS container metadata.
func getECSMetadata(ctx context.Context, metadataURI string) (map[string]interface{}, error) {
	req, err := http.NewRequestWithContext(ctx, "GET", metadataURI, nil)
	if err != nil {
		return nil, err
	}

	resp, err := metadataClient.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("ecs metadata request failed: %d", resp.StatusCode)
	}

	var metadata map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&metadata); err != nil {
		return nil, err
	}

	return metadata, nil
}

// isEKS checks if running on AWS EKS.
func isEKS() bool {
	if strings.Contains(os.Getenv(awsEKSEnv), "EKS") {
		return true
	}
	if os.Getenv(k8sServiceHost) != "" && isAWS() {
		return true
	}
	return false
}

// addEKSAttributes adds EKS-specific attributes.
func addEKSAttributes(ctx context.Context, builder *types.ResourceBuilder) {
	// Try to get cluster name from EKS metadata or Kubernetes env
	if clusterName, err := getAWSMetadata(ctx, "placement/cluster-name"); err == nil && clusterName != "" {
		builder.WithString("k8s.cluster.name", clusterName)
	}

	// Add Kubernetes pod info if available
	if podName := os.Getenv("HOSTNAME"); podName != "" {
		builder.WithString("k8s.pod.name", podName)
	}
	if namespace := os.Getenv("KUBERNETES_NAMESPACE"); namespace != "" {
		builder.WithString("k8s.namespace.name", namespace)
	}

	// Host info from EC2 metadata
	if instanceID, err := getAWSMetadata(ctx, "instance-id"); err == nil && instanceID != "" {
		builder.WithString("host.id", instanceID)
	}
	if instanceType, err := getAWSMetadata(ctx, "instance-type"); err == nil && instanceType != "" {
		builder.WithString("host.type", instanceType)
	}
}

// detectGCP detects Google Cloud Platform resource attributes including GCE and GKE.
func detectGCP(ctx context.Context) (*types.Resource, error) {
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

	// Detect specific GCP platform
	if isGKE(ctx) {
		builder.WithString("cloud.platform", "gcp_gke")
		addGKEAttributes(ctx, builder)
	} else {
		builder.WithString("cloud.platform", "gcp_gce")
		addGCEAttributes(ctx, builder)
	}

	return builder.Build(), nil
}

// isGCP checks if running on GCP.
func isGCP() bool {
	if os.Getenv("GOOGLE_CLOUD_PROJECT") != "" || os.Getenv("GCP_PROJECT") != "" {
		return true
	}

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

// addGCEAttributes adds GCE-specific attributes.
func addGCEAttributes(ctx context.Context, builder *types.ResourceBuilder) {
	if instanceID, err := getGCPMetadata(ctx, "instance/id"); err == nil && instanceID != "" {
		builder.WithString("host.id", instanceID)
	}
	if machineType, err := getGCPMetadata(ctx, "instance/machine-type"); err == nil && machineType != "" {
		parts := strings.Split(machineType, "/")
		if len(parts) > 0 {
			builder.WithString("host.type", parts[len(parts)-1])
		}
	}
	if hostname, err := getGCPMetadata(ctx, "instance/hostname"); err == nil && hostname != "" {
		builder.WithString("host.name", hostname)
	}
	if name, err := getGCPMetadata(ctx, "instance/name"); err == nil && name != "" {
		builder.WithString("host.name", name)
	}
}

// isGKE checks if running on GKE.
func isGKE(ctx context.Context) bool {
	if os.Getenv(k8sServiceHost) != "" && isGCP() {
		return true
	}
	clusterName, err := getGCPMetadata(ctx, "instance/attributes/cluster-name")
	return err == nil && clusterName != ""
}

// addGKEAttributes adds GKE-specific attributes.
func addGKEAttributes(ctx context.Context, builder *types.ResourceBuilder) {
	if clusterName, err := getGCPMetadata(ctx, "instance/attributes/cluster-name"); err == nil && clusterName != "" {
		builder.WithString("k8s.cluster.name", clusterName)
	}
	if clusterLocation, err := getGCPMetadata(ctx, "instance/attributes/cluster-location"); err == nil && clusterLocation != "" {
		builder.WithString("gcp.gke.cluster.location", clusterLocation)
	}
	if instanceID, err := getGCPMetadata(ctx, "instance/id"); err == nil && instanceID != "" {
		builder.WithString("host.id", instanceID)
	}
	if podName := os.Getenv("HOSTNAME"); podName != "" {
		builder.WithString("k8s.pod.name", podName)
	}
	if namespace := os.Getenv("KUBERNETES_NAMESPACE"); namespace != "" {
		builder.WithString("k8s.namespace.name", namespace)
	}
}

// detectAzure detects Microsoft Azure resource attributes including VM and AKS.
func detectAzure(ctx context.Context) (*types.Resource, error) {
	if !isAzure() {
		return nil, fmt.Errorf("not running on Azure")
	}

	builder := types.NewResourceBuilder()
	builder.WithString("cloud.provider", "azure")

	metadata, _ := getAzureMetadata(ctx)

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

	if network, ok := metadata["network"].(map[string]interface{}); ok {
		if interfaces, ok := network["interface"].([]interface{}); ok && len(interfaces) > 0 {
			if first, ok := interfaces[0].(map[string]interface{}); ok {
				if ipv4, ok := first["ipv4"].(map[string]interface{}); ok {
					if ipaddr, ok := ipv4["ipAddress"].([]interface{}); ok && len(ipaddr) > 0 {
						if ip, ok := ipaddr[0].(map[string]interface{}); ok {
							if privateIP, ok := ip["privateIpAddress"].(string); ok && privateIP != "" {
								builder.WithString("host.ip", privateIP)
							}
						}
					}
				}
			}
		}
	}

	if isAKS() {
		builder.WithString("cloud.platform", "azure_aks")
		addAKSAttributes(ctx, builder)
	} else {
		builder.WithString("cloud.platform", "azure_vm")
	}

	return builder.Build(), nil
}

// isAzure checks if running on Azure.
func isAzure() bool {
	if os.Getenv("AZURE_SUBSCRIPTION_ID") != "" || os.Getenv("WEBSITE_RESOURCE_GROUP") != "" {
		return true
	}

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

// isAKS checks if running on Azure AKS.
func isAKS() bool {
	return os.Getenv(k8sServiceHost) != "" && isAzure()
}

// addAKSAttributes adds AKS-specific attributes.
func addAKSAttributes(ctx context.Context, builder *types.ResourceBuilder) {
	if clusterName := os.Getenv("AKS_CLUSTER_NAME"); clusterName != "" {
		builder.WithString("k8s.cluster.name", clusterName)
	}
	if podName := os.Getenv("HOSTNAME"); podName != "" {
		builder.WithString("k8s.pod.name", podName)
	}
	if namespace := os.Getenv("KUBERNETES_NAMESPACE"); namespace != "" {
		builder.WithString("k8s.namespace.name", namespace)
	}
	if nodeName := os.Getenv("AKS_NODE_NAME"); nodeName != "" {
		builder.WithString("k8s.node.name", nodeName)
	}
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
			provider := DetectCloudProvider()
			if provider != CloudProviderUnknown {
				c.Detectors = append(c.Detectors, NewCloudProviderDetector(provider.String()))
			}
		}
	}
}
