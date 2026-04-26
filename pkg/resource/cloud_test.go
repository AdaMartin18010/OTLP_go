package resource

import (
	"context"
	"encoding/json"
	"errors"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"

	"OTLP_go/pkg/types"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestDetectCloudProvider(t *testing.T) {
	provider := DetectCloudProvider()
	assert.True(t, provider >= CloudProviderUnknown && provider <= CloudProviderAzure)
}

func TestCloudProviderString(t *testing.T) {
	tests := []struct {
		provider CloudProvider
		expected string
	}{
		{CloudProviderUnknown, "unknown"},
		{CloudProviderAWS, "aws"},
		{CloudProviderGCP, "gcp"},
		{CloudProviderAzure, "azure"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			assert.Equal(t, tt.expected, tt.provider.String())
		})
	}
}

func TestIsAWS(t *testing.T) {
	t.Run("detects from environment variable", func(t *testing.T) {
		os.Setenv("AWS_REGION", "us-east-1")
		defer os.Unsetenv("AWS_REGION")

		assert.True(t, isAWS())
	})

	t.Run("detects from AWS_DEFAULT_REGION", func(t *testing.T) {
		os.Setenv("AWS_DEFAULT_REGION", "us-west-2")
		defer os.Unsetenv("AWS_DEFAULT_REGION")

		assert.True(t, isAWS())
	})

	t.Run("no AWS without env vars", func(t *testing.T) {
		os.Unsetenv("AWS_REGION")
		os.Unsetenv("AWS_DEFAULT_REGION")

		_ = isAWS()
	})
}

func TestIsGCP(t *testing.T) {
	t.Run("detects from GOOGLE_CLOUD_PROJECT", func(t *testing.T) {
		os.Setenv("GOOGLE_CLOUD_PROJECT", "my-project")
		defer os.Unsetenv("GOOGLE_CLOUD_PROJECT")

		assert.True(t, isGCP())
	})

	t.Run("detects from GCP_PROJECT", func(t *testing.T) {
		os.Setenv("GCP_PROJECT", "my-project")
		defer os.Unsetenv("GCP_PROJECT")

		assert.True(t, isGCP())
	})

	t.Run("no GCP without env vars", func(t *testing.T) {
		os.Unsetenv("GOOGLE_CLOUD_PROJECT")
		os.Unsetenv("GCP_PROJECT")

		_ = isGCP()
	})
}

func TestIsAzure(t *testing.T) {
	t.Run("detects from AZURE_SUBSCRIPTION_ID", func(t *testing.T) {
		os.Setenv("AZURE_SUBSCRIPTION_ID", "sub-123")
		defer os.Unsetenv("AZURE_SUBSCRIPTION_ID")

		assert.True(t, isAzure())
	})

	t.Run("detects from WEBSITE_RESOURCE_GROUP", func(t *testing.T) {
		os.Setenv("WEBSITE_RESOURCE_GROUP", "my-group")
		defer os.Unsetenv("WEBSITE_RESOURCE_GROUP")

		assert.True(t, isAzure())
	})

	t.Run("no Azure without env vars", func(t *testing.T) {
		os.Unsetenv("AZURE_SUBSCRIPTION_ID")
		os.Unsetenv("WEBSITE_RESOURCE_GROUP")

		_ = isAzure()
	})
}

func TestDetectAWS(t *testing.T) {
	ctx := context.Background()

	t.Run("returns error when not on AWS", func(t *testing.T) {
		os.Unsetenv("AWS_REGION")
		os.Unsetenv("AWS_DEFAULT_REGION")

		_, err := detectAWS(ctx)
		assert.Error(t, err)
	})
}

func TestDetectGCP(t *testing.T) {
	ctx := context.Background()

	t.Run("returns error when not on GCP", func(t *testing.T) {
		os.Unsetenv("GOOGLE_CLOUD_PROJECT")
		os.Unsetenv("GCP_PROJECT")

		_, err := detectGCP(ctx)
		assert.Error(t, err)
	})
}

func TestDetectAzure(t *testing.T) {
	ctx := context.Background()

	t.Run("returns error when not on Azure", func(t *testing.T) {
		os.Unsetenv("AZURE_SUBSCRIPTION_ID")
		os.Unsetenv("WEBSITE_RESOURCE_GROUP")

		_, err := detectAzure(ctx)
		assert.Error(t, err)
	})
}

func TestCloudProviderDetector(t *testing.T) {
	ctx := context.Background()

	t.Run("returns error for unknown provider", func(t *testing.T) {
		detector := NewCloudProviderDetector("unknown")
		_, err := detector.Detect(ctx)
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "unknown cloud provider")
	})

	t.Run("returns error when not on cloud", func(t *testing.T) {
		os.Unsetenv("AWS_REGION")
		os.Unsetenv("AWS_DEFAULT_REGION")
		os.Unsetenv("GOOGLE_CLOUD_PROJECT")
		os.Unsetenv("GCP_PROJECT")
		os.Unsetenv("AZURE_SUBSCRIPTION_ID")
		os.Unsetenv("WEBSITE_RESOURCE_GROUP")

		detector := NewCloudProviderDetector("aws")
		_, err := detector.Detect(ctx)
		assert.Error(t, err)
	})
}

func TestWithCloudProvider(t *testing.T) {
	t.Run("adds AWS detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithCloudProvider("aws")
		opt(cfg)

		hasCloud := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "cloud" {
				hasCloud = true
				break
			}
		}
		assert.True(t, hasCloud)
	})

	t.Run("adds GCP detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithCloudProvider("gcp")
		opt(cfg)

		hasCloud := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "cloud" {
				hasCloud = true
				break
			}
		}
		assert.True(t, hasCloud)
	})

	t.Run("adds Azure detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithCloudProvider("azure")
		opt(cfg)

		hasCloud := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "cloud" {
				hasCloud = true
				break
			}
		}
		assert.True(t, hasCloud)
	})

	t.Run("auto-detects cloud provider", func(t *testing.T) {
		os.Setenv("GOOGLE_CLOUD_PROJECT", "my-project")
		defer os.Unsetenv("GOOGLE_CLOUD_PROJECT")

		cfg := &Config{Detectors: []Detector{}}
		opt := WithCloudProvider("auto")
		opt(cfg)

		hasCloud := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "cloud" {
				hasCloud = true
				break
			}
		}
		assert.True(t, hasCloud)
	})
}

func TestGetAzureMetadata(t *testing.T) {
	ctx := context.Background()

	if !isAzure() {
		t.Skip("Not running on Azure")
	}

	metadata, err := getAzureMetadata(ctx)
	require.NoError(t, err)
	require.NotNil(t, metadata)

	_, ok := metadata["compute"]
	assert.True(t, ok)
}

// ECS Detection Tests

func TestIsECS(t *testing.T) {
	t.Run("detects from ECS_CONTAINER_METADATA_URI_V4", func(t *testing.T) {
		os.Setenv(awsECSMetadataEnvV4, "http://169.254.170.2/v4/abc123")
		defer os.Unsetenv(awsECSMetadataEnvV4)

		assert.True(t, isECS())
	})

	t.Run("detects from ECS_CONTAINER_METADATA_URI", func(t *testing.T) {
		os.Setenv(awsECSMetadataEnv, "http://169.254.170.2/v2/abc123")
		defer os.Unsetenv(awsECSMetadataEnv)

		assert.True(t, isECS())
	})

	t.Run("no ECS without env vars", func(t *testing.T) {
		os.Unsetenv(awsECSMetadataEnvV4)
		os.Unsetenv(awsECSMetadataEnv)

		assert.False(t, isECS())
	})
}

func TestAddECSAttributes(t *testing.T) {
	ctx := context.Background()

	t.Run("no metadata URI", func(t *testing.T) {
		os.Unsetenv(awsECSMetadataEnvV4)
		os.Unsetenv(awsECSMetadataEnv)

		builder := types.NewResourceBuilder()
		addECSAttributes(ctx, builder)
		res := builder.Build()
		assert.Empty(t, res.GetString("aws.ecs.task.arn"))
	})

	t.Run("with metadata", func(t *testing.T) {
		server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			resp := map[string]interface{}{
				"TaskARN":    "arn:aws:ecs:us-east-1:123456789:task/my-cluster/abc123",
				"Cluster":    "arn:aws:ecs:us-east-1:123456789:cluster/my-cluster",
				"Family":     "my-task-family",
				"Revision":   "3",
				"LaunchType": "FARGATE",
				"Containers": []interface{}{
					map[string]interface{}{
						"ContainerARN": "arn:aws:ecs:us-east-1:123456789:container/abc",
						"Name":         "my-container",
						"Image":        "nginx:latest",
					},
				},
			}
			_ = json.NewEncoder(w).Encode(resp)
		}))
		defer server.Close()

		os.Setenv(awsECSMetadataEnvV4, server.URL)
		defer os.Unsetenv(awsECSMetadataEnvV4)

		builder := types.NewResourceBuilder()
		addECSAttributes(ctx, builder)
		res := builder.Build()

		assert.Equal(t, "arn:aws:ecs:us-east-1:123456789:task/my-cluster/abc123", res.GetString("aws.ecs.task.arn"))
		assert.Equal(t, "arn:aws:ecs:us-east-1:123456789:cluster/my-cluster", res.GetString("aws.ecs.cluster.arn"))
		assert.Equal(t, "my-task-family", res.GetString("aws.ecs.task.family"))
		assert.Equal(t, "3", res.GetString("aws.ecs.task.revision"))
		assert.Equal(t, "fargate", res.GetString("aws.ecs.launchtype"))
		assert.Equal(t, "arn:aws:ecs:us-east-1:123456789:container/abc", res.GetString("aws.ecs.container.arn"))
		assert.Equal(t, "my-container", res.GetString("container.name"))
		assert.Equal(t, "nginx:latest", res.GetString("container.image.name"))
	})
}

// EKS Detection Tests

func TestIsEKS(t *testing.T) {
	t.Run("detects from AWS_EXECUTION_ENV", func(t *testing.T) {
		os.Setenv(awsEKSEnv, "AWS_EKS_FARGATE")
		defer os.Unsetenv(awsEKSEnv)

		assert.True(t, isEKS())
	})

	t.Run("detects from Kubernetes on AWS", func(t *testing.T) {
		os.Unsetenv(awsEKSEnv)
		os.Setenv(k8sServiceHost, "10.0.0.1")
		os.Setenv("AWS_REGION", "us-east-1")
		defer os.Unsetenv(k8sServiceHost)
		defer os.Unsetenv("AWS_REGION")

		assert.True(t, isEKS())
	})

	t.Run("no EKS without indicators", func(t *testing.T) {
		os.Unsetenv(awsEKSEnv)
		os.Unsetenv(k8sServiceHost)
		os.Unsetenv("AWS_REGION")
		os.Unsetenv("AWS_DEFAULT_REGION")

		assert.False(t, isEKS())
	})
}

func TestAddEKSAttributes(t *testing.T) {
	ctx := context.Background()

	t.Run("adds Kubernetes env attributes", func(t *testing.T) {
		os.Setenv("HOSTNAME", "my-pod")
		os.Setenv("KUBERNETES_NAMESPACE", "default")
		defer os.Unsetenv("HOSTNAME")
		defer os.Unsetenv("KUBERNETES_NAMESPACE")

		builder := types.NewResourceBuilder()
		addEKSAttributes(ctx, builder)
		res := builder.Build()

		assert.Equal(t, "my-pod", res.GetString("k8s.pod.name"))
		assert.Equal(t, "default", res.GetString("k8s.namespace.name"))
	})
}

// GKE Detection Tests

func TestIsGKE(t *testing.T) {
	t.Run("detects from Kubernetes on GCP", func(t *testing.T) {
		os.Setenv(k8sServiceHost, "10.0.0.1")
		os.Setenv("GOOGLE_CLOUD_PROJECT", "my-project")
		defer os.Unsetenv(k8sServiceHost)
		defer os.Unsetenv("GOOGLE_CLOUD_PROJECT")

		assert.True(t, isGKE(context.Background()))
	})

	t.Run("no GKE without indicators", func(t *testing.T) {
		os.Unsetenv(k8sServiceHost)
		os.Unsetenv("GOOGLE_CLOUD_PROJECT")
		os.Unsetenv("GCP_PROJECT")

		assert.False(t, isGKE(context.Background()))
	})
}

func TestAddGKEAttributes(t *testing.T) {
	ctx := context.Background()

	t.Run("adds Kubernetes env attributes", func(t *testing.T) {
		os.Setenv("HOSTNAME", "gke-pod")
		os.Setenv("KUBERNETES_NAMESPACE", "kube-system")
		defer os.Unsetenv("HOSTNAME")
		defer os.Unsetenv("KUBERNETES_NAMESPACE")

		builder := types.NewResourceBuilder()
		addGKEAttributes(ctx, builder)
		res := builder.Build()

		assert.Equal(t, "gke-pod", res.GetString("k8s.pod.name"))
		assert.Equal(t, "kube-system", res.GetString("k8s.namespace.name"))
	})
}

// AKS Detection Tests

func TestIsAKS(t *testing.T) {
	t.Run("detects from Kubernetes on Azure", func(t *testing.T) {
		os.Setenv(k8sServiceHost, "10.0.0.1")
		os.Setenv("AZURE_SUBSCRIPTION_ID", "sub-123")
		defer os.Unsetenv(k8sServiceHost)
		defer os.Unsetenv("AZURE_SUBSCRIPTION_ID")

		assert.True(t, isAKS())
	})

	t.Run("no AKS without indicators", func(t *testing.T) {
		os.Unsetenv(k8sServiceHost)
		os.Unsetenv("AZURE_SUBSCRIPTION_ID")
		os.Unsetenv("WEBSITE_RESOURCE_GROUP")

		assert.False(t, isAKS())
	})
}

func TestAddAKSAttributes(t *testing.T) {
	ctx := context.Background()

	t.Run("adds AKS env attributes", func(t *testing.T) {
		os.Setenv("AKS_CLUSTER_NAME", "my-aks")
		os.Setenv("HOSTNAME", "aks-pod")
		os.Setenv("KUBERNETES_NAMESPACE", "default")
		os.Setenv("AKS_NODE_NAME", "aks-node-1")
		defer os.Unsetenv("AKS_CLUSTER_NAME")
		defer os.Unsetenv("HOSTNAME")
		defer os.Unsetenv("KUBERNETES_NAMESPACE")
		defer os.Unsetenv("AKS_NODE_NAME")

		builder := types.NewResourceBuilder()
		addAKSAttributes(ctx, builder)
		res := builder.Build()

		assert.Equal(t, "my-aks", res.GetString("k8s.cluster.name"))
		assert.Equal(t, "aks-pod", res.GetString("k8s.pod.name"))
		assert.Equal(t, "default", res.GetString("k8s.namespace.name"))
		assert.Equal(t, "aks-node-1", res.GetString("k8s.node.name"))
	})
}

// Platform-specific attribute builder tests

func TestAddEC2Attributes(t *testing.T) {
	ctx := context.Background()

	t.Run("does not panic when not on EC2", func(t *testing.T) {
		os.Unsetenv("AWS_REGION")
		os.Unsetenv("AWS_DEFAULT_REGION")

		builder := types.NewResourceBuilder()
		addEC2Attributes(ctx, builder)
		res := builder.Build()
		assert.Empty(t, res.GetString("host.id"))
	})

	t.Run("with mock metadata server", func(t *testing.T) {
		server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			path := strings.TrimPrefix(r.URL.Path, "/latest/meta-data/")
			switch path {
			case "instance-id":
				_, _ = w.Write([]byte("i-1234567890abcdef0"))
			case "instance-type":
				_, _ = w.Write([]byte("t2.micro"))
			default:
				w.WriteHeader(http.StatusNotFound)
			}
		}))
		defer server.Close()

		origEndpoint := awsMetadataEndpoint
		awsMetadataEndpoint = server.URL + "/latest/meta-data"
		defer func() { awsMetadataEndpoint = origEndpoint }()

		// Mock token endpoint
		tokenServer := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			_, _ = w.Write([]byte("mock-token"))
		}))
		defer tokenServer.Close()

		origToken := awsTokenEndpoint
		awsTokenEndpoint = tokenServer.URL
		defer func() { awsTokenEndpoint = origToken }()

		builder := types.NewResourceBuilder()
		addEC2Attributes(ctx, builder)
		res := builder.Build()

		assert.Equal(t, "i-1234567890abcdef0", res.GetString("host.id"))
		assert.Equal(t, "t2.micro", res.GetString("host.type"))
	})
}

func TestAddGCEAttributes(t *testing.T) {
	ctx := context.Background()

	t.Run("does not panic when not on GCE", func(t *testing.T) {
		os.Unsetenv("GOOGLE_CLOUD_PROJECT")
		os.Unsetenv("GCP_PROJECT")

		builder := types.NewResourceBuilder()
		addGCEAttributes(ctx, builder)
		res := builder.Build()
		assert.Empty(t, res.GetString("host.id"))
	})

	t.Run("with mock metadata server", func(t *testing.T) {
		server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			path := strings.TrimPrefix(r.URL.Path, "/computeMetadata/v1/")
			switch path {
			case "instance/id":
				_, _ = w.Write([]byte("12345"))
			case "instance/machine-type":
				_, _ = w.Write([]byte("projects/123/machineTypes/n1-standard-1"))
			case "instance/hostname":
				_, _ = w.Write([]byte("gce-instance"))
			case "instance/name":
				_, _ = w.Write([]byte("my-instance"))
			default:
				w.WriteHeader(http.StatusNotFound)
			}
		}))
		defer server.Close()

		origEndpoint := gcpMetadataEndpoint
		gcpMetadataEndpoint = server.URL + "/computeMetadata/v1"
		defer func() { gcpMetadataEndpoint = origEndpoint }()

		builder := types.NewResourceBuilder()
		addGCEAttributes(ctx, builder)
		res := builder.Build()

		assert.Equal(t, "12345", res.GetString("host.id"))
		assert.Equal(t, "n1-standard-1", res.GetString("host.type"))
		assert.Equal(t, "my-instance", res.GetString("host.name"))
	})
}

func TestGetECSMetadataError(t *testing.T) {
	ctx := context.Background()

	_, err := getECSMetadata(ctx, "http://invalid.local/")
	assert.Error(t, err)
}

// Mock metadata server tests for full detection paths

func TestDetectAWSWithMockServer(t *testing.T) {
	ctx := context.Background()

	t.Run("EC2 detection", func(t *testing.T) {
		os.Setenv("AWS_REGION", "us-east-1")
		defer os.Unsetenv("AWS_REGION")

		server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			if r.URL.Path == "/latest/api/token" {
				_, _ = w.Write([]byte("mock-token"))
				return
			}
			path := strings.TrimPrefix(r.URL.Path, "/latest/meta-data/")
			switch path {
			case "placement/region":
				_, _ = w.Write([]byte("us-east-1"))
			case "placement/availability-zone":
				_, _ = w.Write([]byte("us-east-1a"))
			case "instance-id":
				_, _ = w.Write([]byte("i-123"))
			case "instance-type":
				_, _ = w.Write([]byte("t2.micro"))
			case "iam/info":
				_, _ = w.Write([]byte(`{"AccountId":"123456789"}`))
			default:
				w.WriteHeader(http.StatusNotFound)
			}
		}))
		defer server.Close()

		origMeta := awsMetadataEndpoint
		origToken := awsTokenEndpoint
		awsMetadataEndpoint = server.URL + "/latest/meta-data"
		awsTokenEndpoint = server.URL + "/latest/api/token"
		defer func() {
			awsMetadataEndpoint = origMeta
			awsTokenEndpoint = origToken
		}()

		res, err := detectAWS(ctx)
		require.NoError(t, err)
		assert.Equal(t, "aws", res.GetString("cloud.provider"))
		assert.Equal(t, "us-east-1", res.GetString("cloud.region"))
		assert.Equal(t, "us-east-1a", res.GetString("cloud.availability_zone"))
		assert.Equal(t, "123456789", res.GetString("cloud.account.id"))
		assert.Equal(t, "aws_ec2", res.GetString("cloud.platform"))
		assert.Equal(t, "i-123", res.GetString("host.id"))
		assert.Equal(t, "t2.micro", res.GetString("host.type"))
	})

	t.Run("ECS detection", func(t *testing.T) {
		os.Setenv("AWS_REGION", "us-west-2")
		os.Setenv(awsECSMetadataEnvV4, "http://localhost:9999/v4/task")
		defer os.Unsetenv("AWS_REGION")
		defer os.Unsetenv(awsECSMetadataEnvV4)

		server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			if r.URL.Path == "/latest/api/token" {
				_, _ = w.Write([]byte("mock-token"))
				return
			}
			path := strings.TrimPrefix(r.URL.Path, "/latest/meta-data/")
			switch path {
			case "placement/region":
				_, _ = w.Write([]byte("us-west-2"))
			case "placement/availability-zone":
				_, _ = w.Write([]byte("us-west-2a"))
			case "iam/info":
				_, _ = w.Write([]byte(`{"AccountId":"987654321"}`))
			default:
				w.WriteHeader(http.StatusNotFound)
			}
		}))
		defer server.Close()

		origMeta := awsMetadataEndpoint
		origToken := awsTokenEndpoint
		awsMetadataEndpoint = server.URL + "/latest/meta-data"
		awsTokenEndpoint = server.URL + "/latest/api/token"
		defer func() {
			awsMetadataEndpoint = origMeta
			awsTokenEndpoint = origToken
		}()

		res, err := detectAWS(ctx)
		require.NoError(t, err)
		assert.Equal(t, "aws", res.GetString("cloud.provider"))
		assert.Equal(t, "aws_ecs", res.GetString("cloud.platform"))
		assert.Equal(t, "us-west-2", res.GetString("cloud.region"))
	})
}

func TestDetectGCPWithMockServer(t *testing.T) {
	ctx := context.Background()

	os.Setenv("GOOGLE_CLOUD_PROJECT", "test-project")
	defer os.Unsetenv("GOOGLE_CLOUD_PROJECT")

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		path := strings.TrimPrefix(r.URL.Path, "/computeMetadata/v1/")
		switch path {
		case "project/project-id":
			_, _ = w.Write([]byte("test-project"))
		case "instance/zone":
			_, _ = w.Write([]byte("projects/123/zones/us-central1-a"))
		case "instance/region":
			_, _ = w.Write([]byte("projects/123/regions/us-central1"))
		case "instance/id":
			_, _ = w.Write([]byte("67890"))
		case "instance/machine-type":
			_, _ = w.Write([]byte("projects/123/machineTypes/n1-standard-2"))
		case "instance/hostname":
			_, _ = w.Write([]byte("gcp-host"))
		case "instance/name":
			_, _ = w.Write([]byte("gcp-name"))
		default:
			w.WriteHeader(http.StatusNotFound)
		}
	}))
	defer server.Close()

	origEndpoint := gcpMetadataEndpoint
	gcpMetadataEndpoint = server.URL + "/computeMetadata/v1"
	defer func() { gcpMetadataEndpoint = origEndpoint }()

	res, err := detectGCP(ctx)
	require.NoError(t, err)
	assert.Equal(t, "gcp", res.GetString("cloud.provider"))
	assert.Equal(t, "test-project", res.GetString("cloud.account.id"))
	assert.Equal(t, "us-central1-a", res.GetString("cloud.availability_zone"))
	assert.Equal(t, "us-central1", res.GetString("cloud.region"))
	assert.Equal(t, "gcp_gce", res.GetString("cloud.platform"))
	assert.Equal(t, "67890", res.GetString("host.id"))
	assert.Equal(t, "n1-standard-2", res.GetString("host.type"))
	assert.Equal(t, "gcp-name", res.GetString("host.name"))
}

func TestDetectAzureWithMockServer(t *testing.T) {
	ctx := context.Background()

	os.Setenv("AZURE_SUBSCRIPTION_ID", "sub-123")
	defer os.Unsetenv("AZURE_SUBSCRIPTION_ID")

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		resp := map[string]interface{}{
			"compute": map[string]interface{}{
				"vmId":              "vm-123",
				"name":              "azure-vm",
				"vmSize":            "Standard_D2s_v3",
				"subscriptionId":    "sub-123",
				"location":          "eastus",
				"resourceGroupName": "my-rg",
				"osType":            "Linux",
			},
			"network": map[string]interface{}{
				"interface": []interface{}{
					map[string]interface{}{
						"ipv4": map[string]interface{}{
							"ipAddress": []interface{}{
								map[string]interface{}{
									"privateIpAddress": "10.0.0.4",
								},
							},
						},
					},
				},
			},
		}
		_ = json.NewEncoder(w).Encode(resp)
	}))
	defer server.Close()

	origEndpoint := azureMetadataEndpoint
	azureMetadataEndpoint = server.URL
	defer func() { azureMetadataEndpoint = origEndpoint }()

	res, err := detectAzure(ctx)
	require.NoError(t, err)
	assert.Equal(t, "azure", res.GetString("cloud.provider"))
	assert.Equal(t, "vm-123", res.GetString("host.id"))
	assert.Equal(t, "azure-vm", res.GetString("host.name"))
	assert.Equal(t, "Standard_D2s_v3", res.GetString("host.type"))
	assert.Equal(t, "sub-123", res.GetString("cloud.account.id"))
	assert.Equal(t, "eastus", res.GetString("cloud.region"))
	assert.Equal(t, "my-rg", res.GetString("azure.resource_group.name"))
	assert.Equal(t, "linux", res.GetString("os.type"))
	assert.Equal(t, "10.0.0.4", res.GetString("host.ip"))
	assert.Equal(t, "azure_vm", res.GetString("cloud.platform"))
}

func TestGetAWSAccountIDWithMock(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/latest/api/token" {
			_, _ = w.Write([]byte("mock-token"))
			return
		}
		path := strings.TrimPrefix(r.URL.Path, "/latest/meta-data/")
		if path == "iam/info" {
			_, _ = w.Write([]byte(`{"AccountId":"mock-account-123"}`))
			return
		}
		w.WriteHeader(http.StatusNotFound)
	}))
	defer server.Close()

	origMeta := awsMetadataEndpoint
	origToken := awsTokenEndpoint
	awsMetadataEndpoint = server.URL + "/latest/meta-data"
	awsTokenEndpoint = server.URL + "/latest/api/token"
	defer func() {
		awsMetadataEndpoint = origMeta
		awsTokenEndpoint = origToken
	}()

	accountID, err := getAWSAccountID(ctx)
	require.NoError(t, err)
	assert.Equal(t, "mock-account-123", accountID)
}

func TestGetAWSAccountIDFallbackParsing(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/latest/api/token" {
			_, _ = w.Write([]byte("mock-token"))
			return
		}
		path := strings.TrimPrefix(r.URL.Path, "/latest/meta-data/")
		if path == "iam/info" {
			_, _ = w.Write([]byte(`not-json AccountId":"fallback-account" more`))
			return
		}
		w.WriteHeader(http.StatusNotFound)
	}))
	defer server.Close()

	origMeta := awsMetadataEndpoint
	origToken := awsTokenEndpoint
	awsMetadataEndpoint = server.URL + "/latest/meta-data"
	awsTokenEndpoint = server.URL + "/latest/api/token"
	defer func() {
		awsMetadataEndpoint = origMeta
		awsTokenEndpoint = origToken
	}()

	accountID, err := getAWSAccountID(ctx)
	require.NoError(t, err)
	assert.Equal(t, "fallback-account", accountID)
}

func TestGetAWSMetadataTokenFailure(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/latest/api/token" {
			w.WriteHeader(http.StatusForbidden)
			return
		}
	}))
	defer server.Close()

	origToken := awsTokenEndpoint
	awsTokenEndpoint = server.URL + "/latest/api/token"
	defer func() { awsTokenEndpoint = origToken }()

	_, err := getAWSMetadata(ctx, "instance-id")
	assert.Error(t, err)
}

func TestGetGCPMetadataWithMock(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		path := strings.TrimPrefix(r.URL.Path, "/computeMetadata/v1/")
		if path == "project/project-id" {
			_, _ = w.Write([]byte("mock-project"))
			return
		}
		w.WriteHeader(http.StatusNotFound)
	}))
	defer server.Close()

	origEndpoint := gcpMetadataEndpoint
	gcpMetadataEndpoint = server.URL + "/computeMetadata/v1"
	defer func() { gcpMetadataEndpoint = origEndpoint }()

	val, err := getGCPMetadata(ctx, "project/project-id")
	require.NoError(t, err)
	assert.Equal(t, "mock-project", val)
}

func TestGetAzureMetadataWithMock(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		resp := map[string]interface{}{
			"compute": map[string]interface{}{
				"vmId": "vm-mock",
			},
		}
		_ = json.NewEncoder(w).Encode(resp)
	}))
	defer server.Close()

	origEndpoint := azureMetadataEndpoint
	azureMetadataEndpoint = server.URL
	defer func() { azureMetadataEndpoint = origEndpoint }()

	metadata, err := getAzureMetadata(ctx)
	require.NoError(t, err)
	assert.Equal(t, "vm-mock", metadata["compute"].(map[string]interface{})["vmId"])
}

func TestGetAzureMetadataFailure(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusInternalServerError)
	}))
	defer server.Close()

	origEndpoint := azureMetadataEndpoint
	azureMetadataEndpoint = server.URL
	defer func() { azureMetadataEndpoint = origEndpoint }()

	_, err := getAzureMetadata(ctx)
	assert.Error(t, err)
}

func TestGetECSMetadataWithMock(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		resp := map[string]interface{}{
			"TaskARN": "arn:aws:ecs:us-east-1:123:task/cluster/task1",
		}
		_ = json.NewEncoder(w).Encode(resp)
	}))
	defer server.Close()

	metadata, err := getECSMetadata(ctx, server.URL)
	require.NoError(t, err)
	assert.Equal(t, "arn:aws:ecs:us-east-1:123:task/cluster/task1", metadata["TaskARN"])
}

func TestGetECSMetadataHTTPFailure(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusInternalServerError)
	}))
	defer server.Close()

	_, err := getECSMetadata(ctx, server.URL)
	assert.Error(t, err)
}

func TestAddECSAttributesPartialData(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		resp := map[string]interface{}{
			"TaskARN":  "arn:aws:ecs:us-east-1:123:task/cluster/task1",
			"Cluster":  "my-cluster",
			"Family":   "family1",
			"Revision": "1",
			"Containers": []interface{}{
				map[string]interface{}{
					"Name": "container1",
				},
			},
		}
		_ = json.NewEncoder(w).Encode(resp)
	}))
	defer server.Close()

	os.Setenv(awsECSMetadataEnvV4, server.URL)
	defer os.Unsetenv(awsECSMetadataEnvV4)

	builder := types.NewResourceBuilder()
	addECSAttributes(ctx, builder)
	res := builder.Build()

	assert.Equal(t, "arn:aws:ecs:us-east-1:123:task/cluster/task1", res.GetString("aws.ecs.task.arn"))
	assert.Equal(t, "my-cluster", res.GetString("aws.ecs.cluster.arn"))
	assert.Equal(t, "family1", res.GetString("aws.ecs.task.family"))
	assert.Equal(t, "1", res.GetString("aws.ecs.task.revision"))
	assert.Empty(t, res.GetString("aws.ecs.launchtype"))
	assert.Empty(t, res.GetString("aws.ecs.container.arn"))
	assert.Equal(t, "container1", res.GetString("container.name"))
}

func TestAddECSAttributesInvalidContainers(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		resp := map[string]interface{}{
			"Containers": []interface{}{"not-a-map"},
		}
		_ = json.NewEncoder(w).Encode(resp)
	}))
	defer server.Close()

	os.Setenv(awsECSMetadataEnvV4, server.URL)
	defer os.Unsetenv(awsECSMetadataEnvV4)

	builder := types.NewResourceBuilder()
	addECSAttributes(ctx, builder)
	res := builder.Build()
	assert.Empty(t, res.GetString("container.name"))
}

func TestAddGKEAttributesWithMock(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		path := strings.TrimPrefix(r.URL.Path, "/computeMetadata/v1/")
		switch path {
		case "instance/attributes/cluster-name":
			_, _ = w.Write([]byte("my-gke-cluster"))
		case "instance/attributes/cluster-location":
			_, _ = w.Write([]byte("us-central1"))
		case "instance/id":
			_, _ = w.Write([]byte("12345"))
		default:
			w.WriteHeader(http.StatusNotFound)
		}
	}))
	defer server.Close()

	origEndpoint := gcpMetadataEndpoint
	gcpMetadataEndpoint = server.URL + "/computeMetadata/v1"
	defer func() { gcpMetadataEndpoint = origEndpoint }()

	os.Setenv("HOSTNAME", "gke-pod")
	os.Setenv("KUBERNETES_NAMESPACE", "default")
	defer os.Unsetenv("HOSTNAME")
	defer os.Unsetenv("KUBERNETES_NAMESPACE")

	builder := types.NewResourceBuilder()
	addGKEAttributes(ctx, builder)
	res := builder.Build()

	assert.Equal(t, "my-gke-cluster", res.GetString("k8s.cluster.name"))
	assert.Equal(t, "us-central1", res.GetString("gcp.gke.cluster.location"))
	assert.Equal(t, "12345", res.GetString("host.id"))
}

func TestDetectAzureWithAKSMock(t *testing.T) {
	ctx := context.Background()

	os.Setenv("AZURE_SUBSCRIPTION_ID", "sub-123")
	os.Setenv(k8sServiceHost, "10.0.0.1")
	defer os.Unsetenv("AZURE_SUBSCRIPTION_ID")
	defer os.Unsetenv(k8sServiceHost)

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		resp := map[string]interface{}{
			"compute": map[string]interface{}{
				"vmId":              "vm-123",
				"name":              "aks-vm",
				"vmSize":            "Standard_D2s_v3",
				"subscriptionId":    "sub-123",
				"location":          "eastus",
				"resourceGroupName": "aks-rg",
				"osType":            "Linux",
			},
		}
		_ = json.NewEncoder(w).Encode(resp)
	}))
	defer server.Close()

	origEndpoint := azureMetadataEndpoint
	azureMetadataEndpoint = server.URL
	defer func() { azureMetadataEndpoint = origEndpoint }()

	os.Setenv("AKS_CLUSTER_NAME", "my-aks")
	os.Setenv("HOSTNAME", "aks-pod")
	os.Setenv("KUBERNETES_NAMESPACE", "default")
	os.Setenv("AKS_NODE_NAME", "aks-node-1")
	defer func() {
		os.Unsetenv("AKS_CLUSTER_NAME")
		os.Unsetenv("HOSTNAME")
		os.Unsetenv("KUBERNETES_NAMESPACE")
		os.Unsetenv("AKS_NODE_NAME")
	}()

	res, err := detectAzure(ctx)
	require.NoError(t, err)
	assert.Equal(t, "azure", res.GetString("cloud.provider"))
	assert.Equal(t, "azure_aks", res.GetString("cloud.platform"))
	assert.Equal(t, "my-aks", res.GetString("k8s.cluster.name"))
	assert.Equal(t, "aks-pod", res.GetString("k8s.pod.name"))
}

func TestDetectCloudProviderWithMocks(t *testing.T) {
	t.Run("detects AWS", func(t *testing.T) {
		os.Setenv("AWS_REGION", "us-east-1")
		defer os.Unsetenv("AWS_REGION")

		provider := DetectCloudProvider()
		assert.Equal(t, CloudProviderAWS, provider)
	})

	t.Run("detects GCP", func(t *testing.T) {
		os.Unsetenv("AWS_REGION")
		os.Unsetenv("AWS_DEFAULT_REGION")
		os.Setenv("GOOGLE_CLOUD_PROJECT", "test")
		defer os.Unsetenv("GOOGLE_CLOUD_PROJECT")

		provider := DetectCloudProvider()
		assert.Equal(t, CloudProviderGCP, provider)
	})

	t.Run("detects Azure", func(t *testing.T) {
		os.Unsetenv("AWS_REGION")
		os.Unsetenv("AWS_DEFAULT_REGION")
		os.Unsetenv("GOOGLE_CLOUD_PROJECT")
		os.Unsetenv("GCP_PROJECT")
		os.Setenv("AZURE_SUBSCRIPTION_ID", "sub")
		defer os.Unsetenv("AZURE_SUBSCRIPTION_ID")

		provider := DetectCloudProvider()
		assert.Equal(t, CloudProviderAzure, provider)
	})
}

func TestIsAWSWithMockIMDS(t *testing.T) {
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method == "PUT" {
			w.WriteHeader(http.StatusOK)
			_, _ = w.Write([]byte("token"))
		}
	}))
	defer server.Close()

	os.Unsetenv("AWS_REGION")
	os.Unsetenv("AWS_DEFAULT_REGION")

	origToken := awsTokenEndpoint
	awsTokenEndpoint = server.URL
	defer func() { awsTokenEndpoint = origToken }()

	assert.True(t, isAWS())
}

func TestIsGCPWithMockMetadata(t *testing.T) {
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Header.Get("Metadata-Flavor") == "Google" {
			w.WriteHeader(http.StatusOK)
		}
	}))
	defer server.Close()

	os.Unsetenv("GOOGLE_CLOUD_PROJECT")
	os.Unsetenv("GCP_PROJECT")

	origEndpoint := gcpMetadataEndpoint
	gcpMetadataEndpoint = server.URL
	defer func() { gcpMetadataEndpoint = origEndpoint }()

	assert.True(t, isGCP())
}

func TestIsAzureWithMockMetadata(t *testing.T) {
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Header.Get("Metadata") == "true" {
			w.WriteHeader(http.StatusOK)
		}
	}))
	defer server.Close()

	os.Unsetenv("AZURE_SUBSCRIPTION_ID")
	os.Unsetenv("WEBSITE_RESOURCE_GROUP")

	origEndpoint := azureMetadataEndpoint
	azureMetadataEndpoint = server.URL
	defer func() { azureMetadataEndpoint = origEndpoint }()

	assert.True(t, isAzure())
}

func TestAddEKSAttributesWithMock(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/latest/api/token" {
			_, _ = w.Write([]byte("mock-token"))
			return
		}
		path := strings.TrimPrefix(r.URL.Path, "/latest/meta-data/")
		if path == "placement/cluster-name" {
			_, _ = w.Write([]byte("my-eks-cluster"))
			return
		}
		if path == "instance-id" {
			_, _ = w.Write([]byte("i-eks-123"))
			return
		}
		if path == "instance-type" {
			_, _ = w.Write([]byte("m5.large"))
			return
		}
		w.WriteHeader(http.StatusNotFound)
	}))
	defer server.Close()

	origMeta := awsMetadataEndpoint
	origToken := awsTokenEndpoint
	awsMetadataEndpoint = server.URL + "/latest/meta-data"
	awsTokenEndpoint = server.URL + "/latest/api/token"
	defer func() {
		awsMetadataEndpoint = origMeta
		awsTokenEndpoint = origToken
	}()

	os.Setenv("HOSTNAME", "eks-pod")
	os.Setenv("KUBERNETES_NAMESPACE", "kube-system")
	defer os.Unsetenv("HOSTNAME")
	defer os.Unsetenv("KUBERNETES_NAMESPACE")

	builder := types.NewResourceBuilder()
	addEKSAttributes(ctx, builder)
	res := builder.Build()

	assert.Equal(t, "my-eks-cluster", res.GetString("k8s.cluster.name"))
	assert.Equal(t, "eks-pod", res.GetString("k8s.pod.name"))
	assert.Equal(t, "kube-system", res.GetString("k8s.namespace.name"))
	assert.Equal(t, "i-eks-123", res.GetString("host.id"))
	assert.Equal(t, "m5.large", res.GetString("host.type"))
}

func TestGetAWSAccountIDNoAccountId(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/latest/api/token" {
			_, _ = w.Write([]byte("mock-token"))
			return
		}
		path := strings.TrimPrefix(r.URL.Path, "/latest/meta-data/")
		if path == "iam/info" {
			_, _ = w.Write([]byte(`{}`))
			return
		}
		w.WriteHeader(http.StatusNotFound)
	}))
	defer server.Close()

	origMeta := awsMetadataEndpoint
	origToken := awsTokenEndpoint
	awsMetadataEndpoint = server.URL + "/latest/meta-data"
	awsTokenEndpoint = server.URL + "/latest/api/token"
	defer func() {
		awsMetadataEndpoint = origMeta
		awsTokenEndpoint = origToken
	}()

	_, err := getAWSAccountID(ctx)
	assert.Error(t, err)
}

// Additional CloudProviderDetector tests for GCP and Azure success paths

func TestCloudProviderDetectorGCP(t *testing.T) {
	ctx := context.Background()

	os.Setenv("GOOGLE_CLOUD_PROJECT", "test")
	defer os.Unsetenv("GOOGLE_CLOUD_PROJECT")

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		path := strings.TrimPrefix(r.URL.Path, "/computeMetadata/v1/")
		if path == "project/project-id" {
			_, _ = w.Write([]byte("test"))
			return
		}
		w.WriteHeader(http.StatusNotFound)
	}))
	defer server.Close()

	origEndpoint := gcpMetadataEndpoint
	gcpMetadataEndpoint = server.URL + "/computeMetadata/v1"
	defer func() { gcpMetadataEndpoint = origEndpoint }()

	detector := NewCloudProviderDetector("gcp")
	res, err := detector.Detect(ctx)
	require.NoError(t, err)
	assert.Equal(t, "gcp", res.GetString("cloud.provider"))
}

func TestCloudProviderDetectorAzure(t *testing.T) {
	ctx := context.Background()

	os.Setenv("AZURE_SUBSCRIPTION_ID", "sub")
	defer os.Unsetenv("AZURE_SUBSCRIPTION_ID")

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		resp := map[string]interface{}{
			"compute": map[string]interface{}{
				"vmId":           "vm-1",
				"subscriptionId": "sub",
				"location":       "eastus",
			},
		}
		_ = json.NewEncoder(w).Encode(resp)
	}))
	defer server.Close()

	origEndpoint := azureMetadataEndpoint
	azureMetadataEndpoint = server.URL
	defer func() { azureMetadataEndpoint = origEndpoint }()

	detector := NewCloudProviderDetector("azure")
	res, err := detector.Detect(ctx)
	require.NoError(t, err)
	assert.Equal(t, "azure", res.GetString("cloud.provider"))
}

// Test getAWSMetadata metadata request failure path

func TestGetAWSMetadataRequestFailure(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/latest/api/token" {
			_, _ = w.Write([]byte("mock-token"))
			return
		}
		w.WriteHeader(http.StatusNotFound)
	}))
	defer server.Close()

	origMeta := awsMetadataEndpoint
	origToken := awsTokenEndpoint
	awsMetadataEndpoint = server.URL + "/latest/meta-data"
	awsTokenEndpoint = server.URL + "/latest/api/token"
	defer func() {
		awsMetadataEndpoint = origMeta
		awsTokenEndpoint = origToken
	}()

	_, err := getAWSMetadata(ctx, "instance-id")
	assert.Error(t, err)
}

// Test getGCPMetadata status failure path

func TestGetGCPMetadataStatusFailure(t *testing.T) {
	ctx := context.Background()

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusNotFound)
	}))
	defer server.Close()

	origEndpoint := gcpMetadataEndpoint
	gcpMetadataEndpoint = server.URL + "/computeMetadata/v1"
	defer func() { gcpMetadataEndpoint = origEndpoint }()

	_, err := getGCPMetadata(ctx, "project/project-id")
	assert.Error(t, err)
}

// Test body read errors using custom RoundTripper

type errReadCloser struct{}

func (e errReadCloser) Read(p []byte) (n int, err error) { return 0, errors.New("read error") }
func (e errReadCloser) Close() error                     { return nil }

func TestGetAWSMetadataBodyReadError(t *testing.T) {
	ctx := context.Background()

	origClient := metadataClient
	metadataClient = &http.Client{
		Transport: roundTripperFunc(func(r *http.Request) (*http.Response, error) {
			if r.Method == "PUT" {
				return &http.Response{
					StatusCode: http.StatusOK,
					Body:       errReadCloser{},
				}, nil
			}
			return &http.Response{
				StatusCode: http.StatusOK,
				Body:       errReadCloser{},
			}, nil
		}),
	}
	defer func() { metadataClient = origClient }()

	_, err := getAWSMetadata(ctx, "instance-id")
	assert.Error(t, err)
}

func TestGetGCPMetadataBodyReadError(t *testing.T) {
	ctx := context.Background()

	origClient := metadataClient
	metadataClient = &http.Client{
		Transport: roundTripperFunc(func(r *http.Request) (*http.Response, error) {
			return &http.Response{
				StatusCode: http.StatusOK,
				Body:       errReadCloser{},
			}, nil
		}),
	}
	defer func() { metadataClient = origClient }()

	_, err := getGCPMetadata(ctx, "project/project-id")
	assert.Error(t, err)
}

func TestGetAzureMetadataBodyReadError(t *testing.T) {
	ctx := context.Background()

	origClient := metadataClient
	metadataClient = &http.Client{
		Transport: roundTripperFunc(func(r *http.Request) (*http.Response, error) {
			return &http.Response{
				StatusCode: http.StatusOK,
				Body:       errReadCloser{},
			}, nil
		}),
	}
	defer func() { metadataClient = origClient }()

	_, err := getAzureMetadata(ctx)
	assert.Error(t, err)
}

type roundTripperFunc func(*http.Request) (*http.Response, error)

func (f roundTripperFunc) RoundTrip(r *http.Request) (*http.Response, error) { return f(r) }
