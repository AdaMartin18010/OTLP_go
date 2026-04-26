// Package logrus provides a bridge between logrus and OpenTelemetry logs.
//
// The actual hook implementation is in hook.go which requires
// github.com/sirupsen/logrus. Ensure the dependency is available
// before using the Hook type.
package logrus
