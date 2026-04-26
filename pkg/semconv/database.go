package semconv

import "go.opentelemetry.io/otel/attribute"

// Database semantic convention attribute keys.
const (
	AttributeKeyDBSystem    = attribute.Key("db.system")
	AttributeKeyDBOperation = attribute.Key("db.operation")
	AttributeKeyDBSQLTable  = attribute.Key("db.sql.table")
	AttributeKeyDBQueryText = attribute.Key("db.query.text")
	AttributeKeyDBName      = attribute.Key("db.name")
	AttributeKeyDBStatement = attribute.Key("db.statement")
)

// DBSystem returns an attribute KeyValue conforming to the
// "db.system" semantic convention.
func DBSystem(val string) attribute.KeyValue {
	return AttributeKeyDBSystem.String(val)
}

// DBOperation returns an attribute KeyValue conforming to the
// "db.operation" semantic convention.
func DBOperation(val string) attribute.KeyValue {
	return AttributeKeyDBOperation.String(val)
}

// DBSQLTable returns an attribute KeyValue conforming to the
// "db.sql.table" semantic convention.
func DBSQLTable(val string) attribute.KeyValue {
	return AttributeKeyDBSQLTable.String(val)
}

// DBQueryText returns an attribute KeyValue conforming to the
// "db.query.text" semantic convention.
func DBQueryText(val string) attribute.KeyValue {
	return AttributeKeyDBQueryText.String(val)
}

// DBName returns an attribute KeyValue conforming to the
// "db.name" semantic convention.
func DBName(val string) attribute.KeyValue {
	return AttributeKeyDBName.String(val)
}

// DBStatement returns an attribute KeyValue conforming to the
// "db.statement" semantic convention.
func DBStatement(val string) attribute.KeyValue {
	return AttributeKeyDBStatement.String(val)
}

// DBAttributes returns database attributes for the given system and statement.
func DBAttributes(system, statement string) []attribute.KeyValue {
	attrs := []attribute.KeyValue{
		DBSystem(system),
	}
	if statement != "" {
		attrs = append(attrs, DBQueryText(statement))
	}
	return attrs
}
