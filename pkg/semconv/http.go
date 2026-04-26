// Package semconv provides OpenTelemetry semantic convention attributes.
package semconv

import (
	"net/http"
	"strconv"

	"go.opentelemetry.io/otel/attribute"
)

// HTTP semantic convention attribute keys.
const (
	AttributeKeyHTTPMethod           = attribute.Key("http.request.method")
	AttributeKeyHTTPStatusCode       = attribute.Key("http.response.status_code")
	AttributeKeyHTTPRoute            = attribute.Key("http.route")
	AttributeKeyServerAddress        = attribute.Key("server.address")
	AttributeKeyServerPort           = attribute.Key("server.port")
	AttributeKeyURLScheme            = attribute.Key("url.scheme")
	AttributeKeyHTTPRequestBodySize  = attribute.Key("http.request.body.size")
	AttributeKeyHTTPResponseBodySize = attribute.Key("http.response.body.size")
)

// HTTPMethod returns an attribute KeyValue conforming to the
// "http.request.method" semantic convention.
func HTTPMethod(val string) attribute.KeyValue {
	return AttributeKeyHTTPMethod.String(val)
}

// HTTPStatusCode returns an attribute KeyValue conforming to the
// "http.response.status_code" semantic convention.
func HTTPStatusCode(val int) attribute.KeyValue {
	return AttributeKeyHTTPStatusCode.Int(val)
}

// HTTPRoute returns an attribute KeyValue conforming to the
// "http.route" semantic convention.
func HTTPRoute(val string) attribute.KeyValue {
	return AttributeKeyHTTPRoute.String(val)
}

// ServerAddress returns an attribute KeyValue conforming to the
// "server.address" semantic convention.
func ServerAddress(val string) attribute.KeyValue {
	return AttributeKeyServerAddress.String(val)
}

// ServerPort returns an attribute KeyValue conforming to the
// "server.port" semantic convention.
func ServerPort(val int) attribute.KeyValue {
	return AttributeKeyServerPort.Int(val)
}

// URLScheme returns an attribute KeyValue conforming to the
// "url.scheme" semantic convention.
func URLScheme(val string) attribute.KeyValue {
	return AttributeKeyURLScheme.String(val)
}

// HTTPRequestBodySize returns an attribute KeyValue conforming to the
// "http.request.body.size" semantic convention.
func HTTPRequestBodySize(val int64) attribute.KeyValue {
	return AttributeKeyHTTPRequestBodySize.Int64(val)
}

// HTTPResponseBodySize returns an attribute KeyValue conforming to the
// "http.response.body.size" semantic convention.
func HTTPResponseBodySize(val int64) attribute.KeyValue {
	return AttributeKeyHTTPResponseBodySize.Int64(val)
}

// HTTPClientAttributes returns HTTP client attributes from an http.Request.
func HTTPClientAttributes(req *http.Request) []attribute.KeyValue {
	if req == nil {
		return nil
	}

	attrs := []attribute.KeyValue{
		HTTPMethod(req.Method),
		ServerAddress(req.URL.Hostname()),
	}

	if port := req.URL.Port(); port != "" {
		if p, err := strconv.Atoi(port); err == nil {
			attrs = append(attrs, ServerPort(p))
		}
	}

	if req.URL.Scheme != "" {
		attrs = append(attrs, URLScheme(req.URL.Scheme))
	}

	return attrs
}

// HTTPServerAttributes returns HTTP server attributes from an http.Request and route.
func HTTPServerAttributes(req *http.Request, route string) []attribute.KeyValue {
	attrs := HTTPClientAttributes(req)
	if route != "" {
		attrs = append(attrs, HTTPRoute(route))
	}
	return attrs
}
