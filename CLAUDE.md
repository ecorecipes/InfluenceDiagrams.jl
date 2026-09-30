# InfluenceDiagrams.jl

Influence diagrams over compositional Bayesian networks: decisions, information sets, utilities, policies, expected utility, decision variable elimination, and value of information.

## Place in the ecosystem

Dependency order (arrows = depends on):
EcologicalBayesianNetworks → InfluenceDiagrams → BayesianNetworkInference → BayesianNetworks →
FiniteKernels,
and BayesianNetworks → BayesianNetworkFormats. Since ADR 0009 this package uses no Catlab
either: schemas are ACSets `BasicSchema` values, graphs are Graphs.jl's, and `to_graphviz`
and `Graphviz` are `BayesianNetworks.jl`'s.
This package depends on: FiniteKernels BayesianNetworkFormats BayesianNetworks BayesianNetworkInference.
Sibling packages are expected at `../<Name>.jl` (see `[sources]` in Project.toml). Do not edit them from here;
record API gaps instead.

## Layout

- `src/schemas.jl`: `SchInfluenceDiagram <: SchBayesNet` (normative; a second hand-written copy of the same schema lives in the Lean project, and the two are *checked to agree* against `proofs/schemas/influence_diagram.schema.json` -- neither is generated from the other), `InfluenceDiagram`, migration to and from `BayesNet` (`copy_parts!` over the shared objects).
- `src/construction.jl`, `src/inspection.jl`, `src/validation.jl`, `src/serialization.jl`, `src/graphics.jl`: structural layer; `validate(id; closed=true)` treats action variables as generated.
- `src/policies.jl`, `src/utilities.jl`, `src/model.jl`: `InfluenceDiagramModel` = `BayesModel{InfluenceDiagram}` + bound utilities + `Strategy`; decision operations edit the strategy, never the syntax (except `do_intervention` on an action, which removes the decision).
- `src/instantiate.jl`, `src/expected_utility.jl`: Proposition 5 and 6; the brute-force reference.
- `src/exhaustive.jl`, `src/valuation.jl`, `src/decision_elimination.jl`: the oracle and the `(φ, ψ)` division algebra with the strong elimination order `I₀ ≺ D₁ ≺ I₁ ≺ … ≺ Dₙ ≺ Iₙ`; exact only with no-forgetting, checked at run time (`IrregularDiagramError`).

## No-forgetting, and why `validate` does not require it

A diagram has **no-forgetting** (perfect recall) when everything known at a decision is still known at every later
one: for `D_k ≺ D_l`, `I_{D_l} ⊇ I_{D_k} ∪ {A_{D_k}}`. Shachter (1986) reserves **regular** for the weaker property
that a directed path runs through all the decisions; the two terms are kept apart in code and prose, and "regular"
is not used as a synonym for no-forgetting.

Decision variable elimination is exact only under no-forgetting. The choice made here (and it is a choice) is
**not** to make it a validity condition: a diagram that forgets is a well-formed limited-memory influence diagram
(Lauritzen and Nilsson, 2001) that `ExhaustivePolicySearch` solves exactly, so `validate` accepts it. Instead:

- `no_forgetting_arcs(id)` reports the missing arcs as `decision => variable` pairs, `is_no_forgetting` is the
  predicate, and `with_no_forgetting` returns the repaired diagram or model (dropping the policies whose signature
  changed);
- `DecisionVariableElimination` throws `IrregularDiagramError` at run time, and its message names both ways out
  (`with_no_forgetting` or `ExhaustivePolicySearch`);
- `with_information(m, D, X)` propagates the new arc to every decision after `D` in `decision_order`, because
  SPEC §35's `info(X, D)` under perfect recall means `X` is known at every later decision. `no_forgetting = false`
  opts out and gives the single-arc, limited-memory reading. This is why
  `expected_value_of_information`/`expected_value_of_perfect_information` work with the default backend on
  sequential diagrams (`EVI(Oil → Test) = 29` on `two_stage_model`; the un-propagated reading is 24).

Note that `decision_order` linearises a partial order by part id, so two decisions with no arcs between them are
ordered but neither knows the other's action: that is a forgetting diagram, and `with_no_forgetting` is the repair.
- `src/formats_bridge.jl`, `src/examples.jl`: Netica/GeNIe/HUGIN bridge; umbrella, SPEC §46 grazing, two-stage examples.
- `src/certificates.jl`: complete version-1 DVE model-data export. Source IDs are strings;
  explicit zero-based coordinates are lexicographic, not `vec` order. Raw CPTs and actual
  diagonal factors must agree. Binary64 bits are retained; rational companions are explicit,
  complete and checked with exact nearest-even midpoint arithmetic. No silent normalization,
  intrinsic-rational inference from floats or execution-trace profile is supported.
- `proofs/`: the Lean model (`instantiate`, `strategyKernel`, `expectedUtility`, `Strategy.fix`,
  information enlargement). Propositions 5 and 6 and `fix_decision` = hard intervention
  are proved over the abstract finite model, not the ACSet or Julia arrays.
  `Finite/Optimization.lean` now proves exact deterministic-table mixture identities and
  global deterministic sufficiency for any finite number of independently parameterised
  decisions, including limited memory. `Finite/OptimalInformation.lean` proves attained
  optimal-value monotonicity, not merely inclusion of an equal-value strategy.
  `Finite/DVE/` now proves the actual exact finite-function bucket algorithm:
  generated no-forgetting schedules, structural probability independence, local policy
  reconstruction and realized global optimality. `Guard/Complete.lean` proves that
  every exact all-row probability diagnostic holds, including zero-outside contexts.
  Its normalized smoothing is a proof device, not part of the algorithm.
  `solveGuarded_spec` has no strict-positivity or assumed-correct-trace premise.
  Supported evidence is a nonnegative likelihood on an action-free chance-ancestral
  set; its mass is strategy independent and the checked solver rejects exactly zero
  mass. All default and Roadmap targets remain `sorry`-free. Do not conflate this
  exact-model Proposition 7 with verification of the literal Float64 arrays, reference
  resolution, explicit array conditioning, min-fill implementation or first-label ties.
  `Finite/OrderedPolicies.lean` separately defines least-state local argmax,
  reconstructs its admissible information table and proves strict `2*epsilon`
  gap stability under uniform score error. Its supplied order is state-position
  order for `Fin n`. It does not establish whole-driver first-label array identity
  or automatically bound Float64 DVE score errors.
  Follow the proof README's build, audit and rendering rules when extending this layer.

## Invariants that must not be broken

- Structural syntax (ACSets) and numerical semantics (kernels, utilities) stay separate; CPT arrays are never ACSet attributes.
- Parent / input order is explicit (`input_position`, `information_position`, `utility_position`) and total. Never rely on part-id order.
- Axis conventions: user-facing CPTs are `(parents..., child)` normalised over the last axis; FinStoch kernels internally are outputs-first. Convert with the documented `permutedims`, never by hand. Policy kernels are `⊗ I_D → A_D` with `I_D` in `information_position` order.
- Information arcs are never causal arcs: `InformationInput` and `Input` are different objects, `variable_graph` ignores information, and only `instantiate` turns an information set into the inputs of a policy mechanism.
- Observation (`observe`), intervention (`do_intervention`) and fixing a decision (`fix_decision`) are different operations and stay different. Evidence never sits on an action variable: an action has no chance mechanism, so there is nothing to condition. `observe` refuses it and `validate(::InfluenceDiagramModel)` (hence `_check_solvable` and both backends) throws `EvidenceOnActionError`.
- No-forgetting is a solver precondition, not a validity condition (see above). Do not add it to `validate`.
- `validate`, `instantiate`, `expected_utility` and `optimize` thread the kernel-normalisation `atol` through the joint/conditional oracle as well as validation. DVE checks no-forgetting and action-free causal ancestry of external evidence structurally; its separate probability diagnostic uses a relative tolerance per row, including arbitrarily small rows. Accepted rounded CPTs are not silently renormalized, so tolerance acceptance is not exact arithmetic.
- The valuation layer reuses BayesianNetworkInference's `_union_axes` and `_broadcastable` helpers for scope/axis agreement and alignment. Keep those internal cross-package contracts in step.
- Every optimised path is checked against a slower oracle (`joint_distribution`, exhaustive policy search) on small models; DVE ties resolve to the first action label.
- Models are immutable values: every operation returns a new model.
- Evidence mass (ADR 0014): `ImpossibleEvidenceError` means probability exactly zero. The Float64
  DVE run throws the internal `_UnresolvedDecisionMass` when its mass is not a normal positive number,
  and `decision_elimination` reruns in `Rational{BigInt}` (`exact_fallback = true`); the value-table
  exhaustive search falls back to per-strategy scoring when a product is unreliable. Tolerated
  negative entries with a mass within `_joint_atol` raise `IndeterminatePosteriorError`.

## Vignettes

01 influence diagrams, 02 policies and expected utility, 03 exhaustive vs DVE, 04 value of
information, 05 composing ecology and management, 06 exact arithmetic for decisions
(`stable=true`: agrees with the Float64 path on the policy in 1200 random cases and differs
only in the last places of the value; the default falls back to it automatically when the
evidence mass underflows, ADR 0014). `ImpossibleEvidenceError` is BayesianNetworks' type: this package
raises it and re-exports it, and must never define a second one (ADR 0012).

## Commands

```sh
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'   # the test suite
julia --project=docs docs/make.jl                                 # build docs locally
cd vignettes && quarto render                                     # render vignettes to html/gfm/pdf (julia engine; PDF needs lualatex + ../fonts/JuliaMono)
julia scripts/sync_vignettes.jl [--check]                         # copy vignettes into docs/src/tutorials
cd proofs && lake build --wfail && make audit && lake exe emit_schema --check
```

## Files not to edit by hand

- `docs/src/tutorials/` is generated by `scripts/sync_vignettes.jl`.
- `vignettes/*/*.md`, `*.html`, `*.pdf` and `*_files/` are quarto output; edit the `.qmd`.
- `proofs/schemas/*.json` is emitted by the Lean project; edit the Lean source.

## Style

JuliaFormatter `yas`; docstrings on every exported name, which `test/test_docstrings.jl` enforces; the docs
build is strict (no `warnonly`), so a docstring left out of the manual or a broken `@ref` fails it; typed
exceptions with variable names in the message, following ADR 0013: they live in `src/errors.jl` and subtype
the nearest root (`FiniteKernelsError`, `BayesianNetworkFormatsError` or `BayesNetError`), invalid arguments
and keywords raise `ArgumentError`, typed errors from a lower package pass through unchanged and documented, content read from a file, document or manifest is checked before it is converted and raises the package's typed error (ADR 0015: never catch the `MethodError` or `InexactError` of an unchecked conversion),
and another package's type is named as a code span, never with `@ref`; no emojis in code or docs.
