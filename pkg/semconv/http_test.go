package semconv

import (
	"net/http"
	"testing"

	"github.com/stretchr/testify/assert"
	"go.opentelemetry.io/otel/attribute"
)

func TestHTTPMethod(t *testing.T) {
	kv := HTTPMethod("GET")
	assert.Equal(t, string(AttributeKeyHTTPMethod), string(kv.Key))
	assert.Equal(t, "GET", kv.Value.AsString())
}

func TestHTTPStatusCode(t *testing.T) {
	kv := HTTPStatusCode(200)
	assert.Equal(t, string(AttributeKeyHTTPStatusCode), string(kv.Key))
	assert.Equal(t, int64(200), kv.Value.AsInt64())
}

func TestHTTPRoute(t *testing.T) {
	kv := HTTPRoute("/users/{id}")
	assert.Equal(t, string(AttributeKeyHTTPRoute), string(kv.Key))
	assert.Equal(t, "/users/{id}", kv.Value.AsString())
}

func TestServerAddress(t *testing.T) {
	kv := ServerAddress("example.com")
	assert.Equal(t, string(AttributeKeyServerAddress), string(kv.Key))
	assert.Equal(t, "example.com", kv.Value.AsString())
}

func TestServerPort(t *testing.T) {
	kv := ServerPort(8080)
	assert.Equal(t, string(AttributeKeyServerPort), string(kv.Key))
	assert.Equal(t, int64(8080), kv.Value.AsInt64())
}

func TestURLScheme(t *testing.T) {
	kv := URLScheme("https")
	assert.Equal(t, string(AttributeKeyURLScheme), string(kv.Key))
	assert.Equal(t, "https", kv.Value.AsString())
}

func TestHTTPRequestBodySize(t *testing.T) {
	kv := HTTPRequestBodySize(1024)
	assert.Equal(t, string(AttributeKeyHTTPRequestBodySize), string(kv.Key))
	assert.Equal(t, int64(1024), kv.Value.AsInt64())
}

func TestHTTPResponseBodySize(t *testing.T) {
	kv := HTTPResponseBodySize(2048)
	assert.Equal(t, string(AttributeKeyHTTPResponseBodySize), string(kv.Key))
	assert.Equal(t, int64(2048), kv.Value.AsInt64())
}

func TestHTTPClientAttributes(t *testing.T) {
	t.Run("nil request", func(t *testing.T) {
		attrs := HTTPClientAttributes(nil)
		assert.Nil(t, attrs)
	})

	t.Run("full request", func(t *testing.T) {
		req, _ := http.NewRequest("POST", "https://example.com:8443/api", nil)
		attrs := HTTPClientAttributes(req)
		assert.Len(t, attrs, 4)

		m := make(map[string]interface{})
		for _, attr := range attrs {
			m[string(attr.Key)] = attr.Value.AsInterface()
		}

		assert.Equal(t, "POST", m["http.request.method"])
		assert.Equal(t, "example.com", m["server.address"])
		assert.Equal(t, int64(8443), m["server.port"])
		assert.Equal(t, "https", m["url.scheme"])
	})

	t.Run("request without port", func(t *testing.T) {
		req, _ := http.NewRequest("GET", "http://example.com/api", nil)
		attrs := HTTPClientAttributes(req)
		assert.Len(t, attrs, 3)
	})
}

func TestHTTPServerAttributes(t *testing.T) {
	req, _ := http.NewRequest("GET", "http://example.com/api", nil)

	t.Run("with route", func(t *testing.T) {
		attrs := HTTPServerAttributes(req, "/api")
		assert.Len(t, attrs, 4)

		m := make(map[string]interface{})
		for _, attr := range attrs {
			m[string(attr.Key)] = attr.Value.AsInterface()
		}
		assert.Equal(t, "/api", m["http.route"])
	})

	t.Run("without route", func(t *testing.T) {
		attrs := HTTPServerAttributes(req, "")
		assert.Len(t, attrs, 3)
	})
}

func TestHTTPConstants(t *testing.T) {
	assert.Equal(t, attribute.Key("http.request.method"), AttributeKeyHTTPMethod)
	assert.Equal(t, attribute.Key("http.response.status_code"), AttributeKeyHTTPStatusCode)
	assert.Equal(t, attribute.Key("http.route"), AttributeKeyHTTPRoute)
	assert.Equal(t, attribute.Key("server.address"), AttributeKeyServerAddress)
	assert.Equal(t, attribute.Key("server.port"), AttributeKeyServerPort)
	assert.Equal(t, attribute.Key("url.scheme"), AttributeKeyURLScheme)
	assert.Equal(t, attribute.Key("http.request.body.size"), AttributeKeyHTTPRequestBodySize)
	assert.Equal(t, attribute.Key("http.response.body.size"), AttributeKeyHTTPResponseBodySize)
}
