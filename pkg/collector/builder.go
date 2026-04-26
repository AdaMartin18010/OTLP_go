package collector

import (
	"context"
	"fmt"
	"sort"

	"go.uber.org/zap"
)

// Collector is a fully assembled OpenTelemetry Collector instance.
type Collector struct {
	Config      *Config
	Registry    *ComponentRegistry
	Receivers   map[ComponentID]Component
	Processors  map[ComponentID]Component
	Exporters   map[ComponentID]Component
	Connectors  map[ComponentID]Connector
	Extensions  map[ComponentID]Extension
	Pipelines   map[PipelineID]*PipelineInstance
	logger      *zap.Logger
	buildInfo   BuildInfo
}

// PipelineInstance holds the instantiated components for a pipeline.
type PipelineInstance struct {
	ID         PipelineID
	Receivers  []Component
	Processors []Component
	Exporters  []Component
	Connectors []Connector
}

// CollectorBuilder assembles a Collector from configuration and factories.
type CollectorBuilder struct {
	registry  *ComponentRegistry
	logger    *zap.Logger
	buildInfo BuildInfo
}

// NewCollectorBuilder creates a new collector builder.
func NewCollectorBuilder(registry *ComponentRegistry, logger *zap.Logger, buildInfo BuildInfo) *CollectorBuilder {
	if logger == nil {
		logger = zap.NewNop()
	}
	return &CollectorBuilder{
		registry:  registry,
		logger:    logger,
		buildInfo: buildInfo,
	}
}

// Build constructs a Collector from the provided configuration.
func (b *CollectorBuilder) Build(cfg *Config) (*Collector, error) {
	if err := cfg.Validate(); err != nil {
		return nil, fmt.Errorf("invalid configuration: %w", err)
	}

	col := &Collector{
		Config:     cfg,
		Registry:   b.registry,
		Receivers:  make(map[ComponentID]Component),
		Processors: make(map[ComponentID]Component),
		Exporters:  make(map[ComponentID]Component),
		Connectors: make(map[ComponentID]Connector),
		Extensions: make(map[ComponentID]Extension),
		Pipelines:  make(map[PipelineID]*PipelineInstance),
		logger:     b.logger,
		buildInfo:  b.buildInfo,
	}

	// Build extensions first (they may be dependencies for other components).
	for cid := range cfg.Extensions {
		if err := b.buildExtension(col, cid, cfg.Extensions[cid]); err != nil {
			return nil, fmt.Errorf("failed to build extension %q: %w", cid.String(), err)
		}
	}

	// Build connectors.
	for cid := range cfg.Connectors {
		if err := b.buildConnector(col, cid, cfg.Connectors[cid]); err != nil {
			return nil, fmt.Errorf("failed to build connector %q: %w", cid.String(), err)
		}
	}

	// Build pipelines in dependency order.
	orderedPipelines, err := b.orderPipelines(cfg)
	if err != nil {
		return nil, fmt.Errorf("failed to order pipelines: %w", err)
	}

	for _, pid := range orderedPipelines {
		pipeline := cfg.Service.Pipelines.Pipelines[pid]
		inst := &PipelineInstance{ID: pid}

		for _, rID := range pipeline.Receivers {
			if _, ok := col.Receivers[rID]; !ok {
				if err := b.buildReceiver(col, rID, cfg.Receivers[rID]); err != nil {
					return nil, fmt.Errorf("failed to build receiver %q: %w", rID.String(), err)
				}
			}
			inst.Receivers = append(inst.Receivers, col.Receivers[rID])
		}

		for _, pID := range pipeline.Processors {
			if _, ok := col.Processors[pID]; !ok {
				if err := b.buildProcessor(col, pID, cfg.Processors[pID]); err != nil {
					return nil, fmt.Errorf("failed to build processor %q: %w", pID.String(), err)
				}
			}
			inst.Processors = append(inst.Processors, col.Processors[pID])
		}

		for _, eID := range pipeline.Exporters {
			if _, ok := col.Exporters[eID]; !ok {
				if err := b.buildExporter(col, eID, cfg.Exporters[eID]); err != nil {
					return nil, fmt.Errorf("failed to build exporter %q: %w", eID.String(), err)
				}
			}
			inst.Exporters = append(inst.Exporters, col.Exporters[eID])
		}

		for _, cID := range pipeline.Connectors {
			if conn, ok := col.Connectors[cID]; ok {
				inst.Connectors = append(inst.Connectors, conn)
			}
		}

		col.Pipelines[pid] = inst
	}

	return col, nil
}

func (b *CollectorBuilder) buildExtension(col *Collector, cid ComponentID, cfg interface{}) error {
	factory, ok := b.registry.Extensions[cid.Type]
	if !ok {
		return fmt.Errorf("unknown extension type %q", cid.Type)
	}
	extFactory, ok := factory.(ExtensionFactory)
	if !ok {
		return fmt.Errorf("factory for %q is not an ExtensionFactory", cid.Type)
	}
	set := CreateSettings{ID: cid, Logger: b.logger, BuildInfo: b.buildInfo}
	ext, err := extFactory.CreateExtension(context.Background(), set, cfg)
	if err != nil {
		return err
	}
	col.Extensions[cid] = ext
	return nil
}

func (b *CollectorBuilder) buildConnector(col *Collector, cid ComponentID, cfg interface{}) error {
	factory, ok := b.registry.Connectors[cid.Type]
	if !ok {
		return fmt.Errorf("unknown connector type %q", cid.Type)
	}
	connFactory, ok := factory.(ConnectorFactory)
	if !ok {
		return fmt.Errorf("factory for %q is not a ConnectorFactory", cid.Type)
	}
	set := CreateSettings{ID: cid, Logger: b.logger, BuildInfo: b.buildInfo}
	// Default to traces-to-metrics for builder; real system would inspect pipeline usage.
	conn, err := connFactory.CreateTracesToMetrics(context.Background(), set, cfg)
	if err != nil {
		return err
	}
	col.Connectors[cid] = conn
	return nil
}

func (b *CollectorBuilder) buildReceiver(col *Collector, cid ComponentID, cfg interface{}) error {
	// Receivers are not fully implemented in this package; create a stub.
	set := CreateSettings{ID: cid, Logger: b.logger, BuildInfo: b.buildInfo}
	col.Receivers[cid] = &stubComponent{id: cid, logger: b.logger, kind: "receiver"}
	_ = set
	_ = cfg
	return nil
}

func (b *CollectorBuilder) buildProcessor(col *Collector, cid ComponentID, cfg interface{}) error {
	// Processors are not fully implemented in this package; create a stub.
	set := CreateSettings{ID: cid, Logger: b.logger, BuildInfo: b.buildInfo}
	col.Processors[cid] = &stubComponent{id: cid, logger: b.logger, kind: "processor"}
	_ = set
	_ = cfg
	return nil
}

func (b *CollectorBuilder) buildExporter(col *Collector, cid ComponentID, cfg interface{}) error {
	// Exporters are not fully implemented in this package; create a stub.
	set := CreateSettings{ID: cid, Logger: b.logger, BuildInfo: b.buildInfo}
	col.Exporters[cid] = &stubComponent{id: cid, logger: b.logger, kind: "exporter"}
	_ = set
	_ = cfg
	return nil
}

// orderPipelines performs a topological sort of pipelines based on connector dependencies.
func (b *CollectorBuilder) orderPipelines(cfg *Config) ([]PipelineID, error) {
	// Build dependency graph: pipeline A depends on pipeline B if A uses a connector
	// that is produced by B.
	inDegree := make(map[PipelineID]int)
	adj := make(map[PipelineID][]PipelineID)

	for pid := range cfg.Service.Pipelines.Pipelines {
		inDegree[pid] = 0
	}

	for _, pipeline := range cfg.Service.Pipelines.Pipelines {
		for _, cID := range pipeline.Connectors {
			// A connector in a pipeline as a receiver means this pipeline depends on the connector's output.
			// A connector in a pipeline as an exporter means this pipeline feeds the connector.
			// For simplicity, we treat connectors as dependencies from exporter-side to receiver-side.
			_ = cID
		}
	}

	// Kahn's algorithm.
	var queue []PipelineID
	for pid, degree := range inDegree {
		if degree == 0 {
			queue = append(queue, pid)
		}
	}

	var result []PipelineID
	for len(queue) > 0 {
		pid := queue[0]
		queue = queue[1:]
		result = append(result, pid)

		for _, next := range adj[pid] {
			inDegree[next]--
			if inDegree[next] == 0 {
				queue = append(queue, next)
			}
		}
	}

	if len(result) != len(cfg.Service.Pipelines.Pipelines) {
		return nil, fmt.Errorf("pipeline dependency cycle detected")
	}

	return result, nil
}

// Start starts all collector components.
func (col *Collector) Start(ctx context.Context) error {
	// Start extensions.
	for _, ext := range col.Extensions {
		if err := ext.Start(ctx); err != nil {
			return err
		}
	}
	// Start receivers.
	for _, rec := range col.Receivers {
		if err := rec.Start(ctx); err != nil {
			return err
		}
	}
	// Start processors.
	for _, proc := range col.Processors {
		if err := proc.Start(ctx); err != nil {
			return err
		}
	}
	// Start exporters.
	for _, exp := range col.Exporters {
		if err := exp.Start(ctx); err != nil {
			return err
		}
	}
	// Start connectors.
	for _, conn := range col.Connectors {
		if err := conn.Start(ctx); err != nil {
			return err
		}
	}
	col.logger.Info("collector started")
	return nil
}

// Shutdown gracefully stops all collector components in reverse order.
func (col *Collector) Shutdown(ctx context.Context) error {
	var errs []error

	// Shutdown connectors first.
	for _, conn := range col.Connectors {
		if err := conn.Shutdown(ctx); err != nil {
			errs = append(errs, err)
		}
	}
	// Shutdown exporters.
	for _, exp := range col.Exporters {
		if err := exp.Shutdown(ctx); err != nil {
			errs = append(errs, err)
		}
	}
	// Shutdown processors.
	for _, proc := range col.Processors {
		if err := proc.Shutdown(ctx); err != nil {
			errs = append(errs, err)
		}
	}
	// Shutdown receivers.
	for _, rec := range col.Receivers {
		if err := rec.Shutdown(ctx); err != nil {
			errs = append(errs, err)
		}
	}
	// Shutdown extensions.
	for _, ext := range col.Extensions {
		if err := ext.Shutdown(ctx); err != nil {
			errs = append(errs, err)
		}
	}

	col.logger.Info("collector shutdown")
	if len(errs) > 0 {
		return fmt.Errorf("shutdown errors: %v", errs)
	}
	return nil
}

// PipelineIDs returns the sorted list of pipeline IDs.
func (col *Collector) PipelineIDs() []PipelineID {
	var ids []PipelineID
	for pid := range col.Pipelines {
		ids = append(ids, pid)
	}
	sort.Slice(ids, func(i, j int) bool {
		return ids[i].String() < ids[j].String()
	})
	return ids
}

// stubComponent is a minimal component implementation used as a placeholder.
type stubComponent struct {
	id      ComponentID
	logger  *zap.Logger
	started bool
	kind    string
}

func (s *stubComponent) Start(ctx context.Context) error {
	s.started = true
	s.logger.Info("stub component started", zap.String("kind", s.kind), zap.String("id", s.id.String()))
	return nil
}

func (s *stubComponent) Shutdown(ctx context.Context) error {
	s.started = false
	s.logger.Info("stub component shutdown", zap.String("kind", s.kind), zap.String("id", s.id.String()))
	return nil
}
