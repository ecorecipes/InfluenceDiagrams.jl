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
unsupported-profile error. Version 2 adds the solver's result, not its steps. It includes hard model evidence and no external soft
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
are computed outputs, never trusted `valid` or `optimal` input flags. Schema
conformance alone does not supply a decoder-to-model correspondence; the Lean
project supplies one from a parsed JSON tree. `Finite/DVE/CertificateJson.lean`
decodes a version-1 certificate faithfully (`decodeCertificate_eq_ok`), and
`certificateMatches` in `Finite/DVE/CertificateCheck.lean` decides whether it
agrees with the decoded diagram. When it does and the cells are nonnegative, the
exact DVE run on the certificate's data picks the least-position maximizer of its
own score (`certificate_tables`); when every conditional-probability row also sums
to exactly one, that solution is optimal (`certificate_solve_spec`,
`certificate_tables_optimal`). Binary64 rows seldom sum to exactly one; for them
`certificate_approx_optimal` (`Finite/DVE/CertificateApprox.lean`) proves that, for
a matching certificate with nonnegative cells and `ε = certificateEpsilon c < 1`
(the largest `|row sum - 1|`), the exact DVE run on the certificate's numbers is
within `2 n (((1 + ε) / (1 - ε))^n - 1) Umax` of the optimum of the row-normalised
model, with `n` the number of mechanisms and `Umax` the sum of the utility tables'
largest absolute cells. The row-normalised model is a reference, chosen because the
decimal model Julia rounded is not recorded; `lake exe check_certificate` prints
`ε`, `n`, `Umax` and the gap (`8.9e-14` for the binary64 umbrella). A version-1
certificate does not carry Julia's solution, so nothing in it ties Julia's solver
output to these theorems; JSON parsing and this exporter are trusted. A version-2
certificate records that output (next section), and the Lean decoder reads both
versions.

## Recording Julia's solution (version 2)

A version-1 certificate holds only the model, so nothing in it ties Julia's
solver output to the Lean theorems. `solution` opts in to recording that output:

```julia
model = two_stage_model()
v2 = export_dve_certificate(model; solution=true)          # the default binary64 run
v2["version"]                                               # 2
exact = export_dve_certificate(model; solution=DecisionVariableElimination(stable=true))
exact["solution"].value                                     # (q = (num = "21", den = "1"), f64 = ...)
```

With `solution=false`, the default, the result is the version-1 certificate,
byte for byte. Otherwise the certificate has `"version": 2`, the exporter
suffix `-v2`, every version-1 field unchanged, and one more field,
`"solution"`. `solution=true` means `DecisionVariableElimination()`, the
backend `optimize` uses by default; any `DecisionVariableElimination` backend
can be passed instead.

### What the run reads

The run is the production driver of [`decision_elimination`](@ref): the
binary64 path with its exact-rational fallback for an underflowed evidence mass
(ADR 0014), or with `stable=true` the exact-rational path. It does not read the
model again. Its initial factors are the certificate's own cells: the compiled
mechanism factors and the materialized utility tables written above, so a
utility callback is not called a second time.

| `numeric_mode` | backend | `arithmetic` | `data` | cells the run reads |
| :-- | :-- | :-- | :-- | :-- |
| `binary64_exact` | `stable=false` | `binary64` | `f64` | the binary64 words |
| `binary64_exact` | `stable=true` | `exact_rational` | `f64` | the words' dyadic values |
| `rational_exact` | `stable=false` | `binary64` | `f64` | the binary64 words (needs `capture_runtime_bits`) |
| `rational_exact` | `stable=true` | `exact_rational` | `q` | the rational companions |

The last row is the one whose data is the exact model of the Lean checker. The
public `stable=true` path converts the bound Float64 cells, so it agrees with
the companion run only when the companions are those dyadic values; on other
companions the tables agree except at near-ties and the values agree within
rounding. A binary64 run that falls back records `arithmetic =
"exact_rational"` and `exact_fallback = true`.

The run conditions on the certificate's `evidence.hard` rows and on nothing
else (`conditioned_on = "evidence.hard"`). The model's current strategy is
ignored, as in version 1. The normalization tolerance is
`runtime_tolerances.kernel_normalization_f64`; the constancy tolerance,
`constancy_atol_f64`, is the backend's `atol`, or that normalization tolerance
when `atol` is `nothing` (`atol_f64 = null`).

### Layout

```json
"solution": {
  "backend": {"name": "DecisionVariableElimination", "order": "MinFill",
              "stable": false, "atol_f64": null,
              "constancy_atol_f64": "3e45798ee2308c3a"},
  "arithmetic": "binary64", "data": "f64", "exact_fallback": false,
  "conditioned_on": "evidence.hard", "julia_version": "1.12.7",
  "elimination_order": ["1", "4", "3", "2"],
  "value": {"f64": "4035000000000000"},
  "policies": [
    {"decision": "1", "action": "2", "axes": [], "scope": [],
     "entries": [{"at": [], "action": "3", "score": {"f64": "4035000000000000"}}]},
    {"decision": "2", "action": "4", "axes": ["2", "3"], "scope": ["2", "3"],
     "entries": [{"at": [0, 0], "action": "8", "score": {"f64": "404c2e8ba2e8ba2e"}},
                 {"at": [0, 1], "action": "9", "score": {"f64": "0000000000000000"}},
                 "..."]}]
}
```

- `elimination_order` lists the variable IDs in the order the run eliminated
  them. With the cells and the tolerances it fixes the run.
- `value` is the maximal expected utility the run computed, conditioned on the
  evidence.
- `policies` has one row per decision, in the order of the certificate's
  `decisions` array. `action` is the action variable; `axes` are the information
  variables in `information_position` order, the certificate's information slots;
  `scope` lists the variables the run's table really depends on.
- `entries` cover every information configuration once. Their zero-based `at`
  coordinates index each axis's states in `state_position` order, the order of
  the variable's `states` rows, and run in lexicographic order with the
  rightmost coordinate fastest, as table entries do. `action` is the state ID of
  the chosen action. `score` is the row's maximal score: the utility potential of
  the action's bucket, maximized over the action. It is zero when no valuation
  mentions the action, which is then the first state.
- A binary64 run writes numbers as `{f64}`. An exact run writes `{q, f64}`, with
  `f64` the nearest-even rounding of `q`, whatever `capture_runtime_bits` is. A
  rational with more than 4096 digits is a `RESOURCE_LIMIT` error.

Each policy table is the one Julia's `DecisionSolution` returned, read in the
label order of the Lean label-order theorems: information slots in position
order, states in `state_position` order. The exporter checks that Julia's
policy axes are that order and raises `STRUCTURAL_PRECONDITION` if they are not.
The tests compare every entry with the `DecisionSolution` and the value with its
`expected_utility`. For the exact run on companions, the tests compare the value
with the exact expected utility of the recorded tables computed from the
certificate alone.

### What the solution claims

It claims only that this Julia run, on this certificate's data, returned these
tables, scores and value. It is the output of a run, not a trusted
optimality flag, and a consumer must not take it as one. Whether the tables are
the least-position maximizers, and whether the value is the optimum, is for a
checker to decide from the certificate's data (`certificate_tables`,
`certificate_solve_spec`); those theorems need nonnegative cells, exactly
normalized rows for optimality, and no evidence row. A binary64 run's tables can
differ from the exact ones near ties, and its value carries rounding error. With
evidence, a table does not read an observed variable, and a row that contradicts
the evidence repeats the observed row's action. On a zero-probability row the
score is the run's own, which may differ from the model's. The solution does not
record the run's intermediate buckets; [`trace_decision_elimination`](@ref)
does.

The [version-2 JSON Schema](dve-certificate-v2.schema.json) is the version-1
schema with `version` 2 and this `solution` object. The Lean decoder
`decodeAnyCertificate` (`Finite/DVE/SolutionJson.lean`) reads version 1 exactly
as before and version 2 as the version-1 fields plus `solution`, rejecting a
version-2 document with the fourteen version-1 keys and a version-1 document with
fifteen. It is faithful key for key (`decodeCertificateV2_eq_ok`), and decoding
checks that decision, action and state IDs exist, that `axes` are the decision's
information slots and that the `at` lists enumerate every configuration once in
order (`decodeSolution_coverage`).

`lake exe check_certificate` compares a decoded solution with the exact DVE run
that `certificate_tables` speaks about, computed over the rationals on Julia's
`elimination_order` (`Finite/DVE/SolutionRun.lean`, `exactRun_spec`), with the
representative of Julia's `sum_out` branch (`keepOfT`, read off the source). For
a run in exact arithmetic on the certificate's own numbers, `solutionMatches`
asks every recorded action to be the least-position maximizer of the exact score
row, every recorded score to be that row's maximum and the value to be the
exact value, all exactly. When it holds, `recorded_solution_optimal`
(`Finite/DVE/SolutionCheck.lean`) proves that Julia's recorded strategy and value
are the exact run's, hence optimal when every CPT row sums to exactly one, and
`recorded_solution_approx_optimal` gives them the bound of
`certificate_approx_optimal` otherwise. A binary64 run is compared within
tolerances (`solutionWithin τ τv`, printed with `τ = τv = 1e-9`):
`recorded_binary64_approx_optimal` proves that each recorded action is within `τ`
of its exact row maximum and the value within `τv + e` of the reference optimum,
and bounds the strategy only when its actions are the exact run's. A binary64
action that differs at a near-tie has no proved bound on the lost expected
utility, the Float64 run itself is not proved, and the checks require a
certificate without evidence rows. The parse, this exporter and the checker's
printing code are trusted.

### Impossible combinations

These raise [`DVEExportError`](@ref) with code `:UNSUPPORTED_SOLUTION_PROFILE`:

- a backend other than `DecisionVariableElimination`;
- a binary64 run on a `rational_exact` certificate with
  `capture_runtime_bits=false`, which leaves out the `f64` cells the run reads.

`trace=true` stays `:UNSUPPORTED_TRACE_PROFILE`, with or without a solution.
Every policy row counts against `max_entries`. A failure of the run itself keeps
its own type: for example, `IrregularDiagramError`, `ImpossibleEvidenceError`,
or `FactorDomainError` for a negative cell in exact arithmetic.

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
