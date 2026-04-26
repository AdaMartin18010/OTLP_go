package semconv

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"go.opentelemetry.io/otel/attribute"
)

func TestDBSystem(t *testing.T) {
	kv := DBSystem("postgresql")
	assert.Equal(t, string(AttributeKeyDBSystem), string(kv.Key))
	assert.Equal(t, "postgresql", kv.Value.AsString())
}

func TestDBOperation(t *testing.T) {
	kv := DBOperation("SELECT")
	assert.Equal(t, string(AttributeKeyDBOperation), string(kv.Key))
	assert.Equal(t, "SELECT", kv.Value.AsString())
}

func TestDBSQLTable(t *testing.T) {
	kv := DBSQLTable("users")
	assert.Equal(t, string(AttributeKeyDBSQLTable), string(kv.Key))
	assert.Equal(t, "users", kv.Value.AsString())
}

func TestDBQueryText(t *testing.T) {
	kv := DBQueryText("SELECT * FROM users")
	assert.Equal(t, string(AttributeKeyDBQueryText), string(kv.Key))
	assert.Equal(t, "SELECT * FROM users", kv.Value.AsString())
}

func TestDBName(t *testing.T) {
	kv := DBName("mydb")
	assert.Equal(t, string(AttributeKeyDBName), string(kv.Key))
	assert.Equal(t, "mydb", kv.Value.AsString())
}

func TestDBStatement(t *testing.T) {
	kv := DBStatement("INSERT INTO logs VALUES (1)")
	assert.Equal(t, string(AttributeKeyDBStatement), string(kv.Key))
	assert.Equal(t, "INSERT INTO logs VALUES (1)", kv.Value.AsString())
}

func TestDBAttributes(t *testing.T) {
	t.Run("with statement", func(t *testing.T) {
		attrs := DBAttributes("mysql", "SELECT 1")
		assert.Len(t, attrs, 2)
		assert.Equal(t, "mysql", attrs[0].Value.AsString())
		assert.Equal(t, "SELECT 1", attrs[1].Value.AsString())
	})

	t.Run("without statement", func(t *testing.T) {
		attrs := DBAttributes("redis", "")
		assert.Len(t, attrs, 1)
		assert.Equal(t, "redis", attrs[0].Value.AsString())
	})
}

func TestDBConstants(t *testing.T) {
	assert.Equal(t, attribute.Key("db.system"), AttributeKeyDBSystem)
	assert.Equal(t, attribute.Key("db.operation"), AttributeKeyDBOperation)
	assert.Equal(t, attribute.Key("db.sql.table"), AttributeKeyDBSQLTable)
	assert.Equal(t, attribute.Key("db.query.text"), AttributeKeyDBQueryText)
	assert.Equal(t, attribute.Key("db.name"), AttributeKeyDBName)
	assert.Equal(t, attribute.Key("db.statement"), AttributeKeyDBStatement)
}
