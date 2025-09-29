package main

import (
	"context"
	"log/slog"
	"os"
	"time"
)

// newSlog returns a standard slog logger that writes to stdout.
// This avoids relying on experimental OTel log exporters that may not be available.
func newSlog(ctx context.Context) *slog.Logger {
	_ = ctx
	return slog.New(slog.NewTextHandler(os.Stdout, nil))
}

func emitBootLog(l *slog.Logger) {
	l.Info("service boot", "pid", os.Getpid(), "ts", time.Now().Format(time.RFC3339Nano))
}
