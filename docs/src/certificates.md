# Exact-data model certificates

[`export_dve_certificate`](@ref) captures a complete influence diagram in the
versioned `ecorecipes.dve-certificate` profile. It is a data bridge to independent
finite-model checks, not an assertion that the Julia optimizer, exporter or
compiler has been proved correct.

```julia
using InfluenceDiagrams

model = umbrella_model()
certificate = export_dve_certificate(model)
certificate["numeric"]
certificate["topological_order"]
```

The result is a JSON-compatible dictionary. An application or test environment
that includes JSON3 can serialize it with `JSON3.write(certificate)`. Capture
finishes before a dictionary is returned; profile, resource or companion
failures do not return a partial certificate.

## Preserved data

Original variable, state, mechanism, decision, utility and slot part IDs are
positive decimal strings. Entity arrays follow numeric source-ID order, while
state and slot arrays follow the actual `*_position` attributes. A separate
combined topological order defines the proof indices; causal ancestors of
external evidence precede the first decision.

References keep their four tags and payloads in a deduplicated reference pool.
Both the raw `(parents..., child)` CPT and the actual compiled unique-variable
factor are included. Repeated input slots retain all raw entries; the factor
must select their diagonal exactly. Every table cell has explicit zero-based
coordinates in lexicographic order, with the rightmost coordinate varying fastest.

The [JSON Schema](dve-certificate-v1.schema.json) describes the exact field/tag
shapes. Cross-field conditions also matter: ID projection, reference usage,
ordered slots, factor diagonals, no-forgetting and the evidence-prefix condition
must be checked by a consumer. The source-manifest hash identifies the frozen
version-1 comparison contract, not the installed package's Git commit.

## Two distinct numeric interpretations

The default `numeric_mode=:binary64_exact` retains every finite Float64 cell as
its 16-digit IEEE bit word. Its exact mathematical value is the dyadic rational
represented by those bits. Other raw kernel scalar types are rejected rather
than silently cast.

Runtime acceptance within `atol` does not imply that these dyadic rows sum to
exactly one. For example, three Float64 approximations to one third can pass
runtime validation but fail exact row normalization. That is an inapplicable
exact-model certificate, not permission for a consumer to renormalize it.

`numeric_mode=:rational_exact` requires an explicit `exact_tables` companion:

```text
(:cpt, mechanism_part_id, Tuple(zero_based_coordinates)) => exact rational
(:utility, utility_part_id, Tuple(zero_based_coordinates)) => exact rational
```

It must cover every raw CPT and utility cell exactly, with no extra coordinates.
The exporter checks nearest-even rounding against the captured Float64 value
using exact rational midpoints, including subnormal and overflow boundaries.
Rationals are never guessed from decimal printing or approximate rationalization.
Factor companions come only from diagonal selection of the raw CPT companions.

`capture_runtime_bits=false` is available with rational companions when only the
exact rational values should be serialized; agreement with the actual captured
runtime cells is still checked. The current producer does not implement an
intrinsic-rational storage profile.

## Deliberate boundaries and failures

Version 1 contains model data, not solver-step traces; `trace=true` is an explicit
unsupported-profile error. It includes hard model evidence and no external soft
likelihood. Current policies on the model are not exported as optimization
constraints.

`max_entries` caps the complete raw-CPT, factor and utility payload before utility
callbacks are evaluated. Each utility table is materialized once. The caller must
not mutate the model or external callback state during capture.

[`DVEExportError`](@ref) carries a code, owner and coordinates where applicable.
Ordinary structural, missing-binding and kernel-validation failures retain their
existing typed exceptions. No clipping, normalization, incomplete-table defaults
or success-shaped fallback is performed.

A reference consumer may distinguish structurally valid positive-mass exact data,
valid zero-mass rejection data, and data outside exact semantics. Such outcomes
are computed outputs, never trusted `valid` or `optimal` input flags. Automatic
theorem application still needs a proved decoder-to-model correspondence;
schema conformance alone does not supply it.

## Actual execution and compilation observations

[`trace_decision_elimination`](@ref) is a separate solver-trace API. Its default
version-1 trace captures the actual exact-rational DVE run. The opt-in version 2
also records the compilation boundary:

```julia
solution, trace = trace_decision_elimination(umbrella_model();
                                            include_compilation=true)
trace["version"]                 # 2
trace["compilation"]["inputs"]   # bound sources and actual effective factors
```

The observer records the bound Float64 kernel storage, its sanctioned `cpt`
conversion, tabular utility sources, and the actual factors consumed before
rational conversion. These are not factors generated afterward by a substitute
compiler. Repeated parent occurrences remain in the source CPT; their compiled
factor has distinct variable axes and selects the source diagonal.

Captured arrays are first-axis-fastest. Kernel axes are outputs before inputs;
CPT axes are `(parents..., child)`. State labels and occurrence positions are
recorded explicitly. Source and effective-table copies share the `max_entries`
budget with the ordinary trace. Unsupported source scalar types and callable
utilities raise `DVEExportError` in this initial compilation profile.

This begins at the **bound model**. The workspace's separate
`ecorecipes.id-execution-refinement` wrapper retains original JSON bytes and
native JSON3 read-back so a consumer can compare the request, binding,
compilation and execution as distinct stages. Its source arrays use
last-axis-fastest order; the consumer explicitly checks the coordinate
conversion rather than comparing flattened vectors without their axes.

Neither a captured trace nor successful host comparisons prove JSON3, Julia's
JIT, LLVM or physical hardware correct. Exact normalization and positive-mass
conditions still need checking; capturing a tolerance-accepted model does not
make it an exactly normalized model. The stable solver's final conversion now
constructs binary64 words with integer rounding rather than floating-point
scaling, but implementation and hardware refinement remain separate claims.
