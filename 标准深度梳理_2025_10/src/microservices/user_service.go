package microservices

import (
	"context"
	"fmt"
	"log"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"

	"otlp-go-monitoring/src/pkg/types"
)

// UserService handles user-related operations
type UserService struct {
	tracer trace.Tracer
	users  map[string]*types.User
}

// NewUserService creates a new UserService instance
func NewUserService() *UserService {
	return &UserService{
		tracer: otel.Tracer("user-service"),
		users:  make(map[string]*types.User),
	}
}

// GetUser retrieves a user by ID
func (us *UserService) GetUser(ctx context.Context, userID string) (*types.User, error) {
	ctx, span := us.tracer.Start(ctx, "get-user")
	defer span.End()

	span.SetAttributes(
		attribute.String("user.id", userID),
	)

	// Simulate user retrieval
	time.Sleep(50 * time.Millisecond)

	user, exists := us.users[userID]
	if !exists {
		span.SetStatus(codes.Error, "User not found")
		return nil, fmt.Errorf("user not found: %s", userID)
	}

	span.SetAttributes(
		attribute.String("user.name", user.Name),
		attribute.String("user.email", user.Email),
		attribute.String("user.level", user.Level),
	)

	span.SetStatus(codes.Ok, "User retrieved successfully")
	log.Printf("User retrieved: %s", userID)

	return user, nil
}

// GetUserStats retrieves user statistics
func (us *UserService) GetUserStats(ctx context.Context, userID string) (map[string]interface{}, error) {
	ctx, span := us.tracer.Start(ctx, "get-user-stats")
	defer span.End()

	span.SetAttributes(
		attribute.String("user.id", userID),
	)

	// Simulate user stats retrieval
	time.Sleep(30 * time.Millisecond)

	stats := map[string]interface{}{
		"total_orders":     10,
		"total_spent":      1500.0,
		"last_order_date":  time.Now().AddDate(0, 0, -5),
		"membership_level": "premium",
	}

	span.SetAttributes(
		attribute.Int("stats.total_orders", 10),
		attribute.Float64("stats.total_spent", 1500.0),
	)

	span.SetStatus(codes.Ok, "User stats retrieved successfully")
	log.Printf("User stats retrieved: %s", userID)

	return stats, nil
}
