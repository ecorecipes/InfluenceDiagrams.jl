# InfluenceDiagrams.jl

[![Build Status](https://github.com/ecorecipes/InfluenceDiagrams.jl/actions/workflows/CI.yml/badge.svg)](https://github.com/ecorecipes/InfluenceDiagrams.jl/actions/workflows/CI.yml)
[![Docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://ecorecipes.github.io/InfluenceDiagrams.jl/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Influence diagrams over compositional Bayesian networks: decisions, information sets, utilities, policies, expected utility, decision variable elimination, and value of information.

Part of the ecorecipes compositional Bayesian-network ecosystem:
`FiniteKernels.jl` -> `BayesianNetworks.jl` -> `BayesianNetworkInference.jl` ->
`InfluenceDiagrams.jl`,
with `BayesianNetworkFormats.jl` (file formats) and `EcologicalBayesianNetworks.jl` (model zoo).

## Features

Structural layer:

- `SchInfluenceDiagram`, an extension of `SchBayesNet` with `Decision`, `InformationInput`,
  `Utility`, `UtilityInput` and `DecisionPrecedence` (SPEC section 24 with `information_position`
  and `utility_position`), and the `InfluenceDiagram` ACSet type. The Lean project in `proofs/`
  carries a second, hand-written definition of the same schema and emits it as JSON; the test
  suite and `emit_schema --check` verify that the two agree. Neither is generated from the
  other.
- Builders (`influence_diagram`, `add_decision!`, `add_information!`, `add_utility!`,
  `add_utility_input!`, `add_precedence!`), inspection (`decisions`, `decision_information`,
  `utility_scope`, `decision_order`, `action_variables`, `chance_variables`, ...),
  `information_graph`, `canonicalize`, `is_isomorphic`, JSON serialisation and `to_graphviz`.
- `validate` / `validation_errors` implementing the twelve checks of SPEC section 37 with typed
  errors (`DecisionUniquenessError`, `InvalidInformationSetError`, `DecisionPrecedenceCycleError`,
  `PolicySignatureError`, `UtilityScopeError`, `IncompleteStrategyError`, ...); `closed = true`
  treats action variables as generated.
- Migration to and from `BayesNet` (`InfluenceDiagram(bn)`, `BayesNet(id)`).

Semantic layer:

- `InfluenceDiagramModel`: a `BayesModel` over the diagram (chance kernels via `bind_kernel` /
  `bind_cpt`, evidence, history) plus bound utilities (`bind_utility`: `TabularUtility`,
  `FunctionUtility`) and a `Strategy` of policies (`DeterministicPolicy`, `StochasticPolicy`,
  `ConstantPolicy`, all with `policy_kernel`).
- Decision operations (SPEC section 41): `fix_decision`, `set_policy`, `with_information`,
  `without_information`; `observe`; `do_intervention` and `soft_intervention`, which on an action
  variable remove the decision (a physical override, distinct from fixing it).
- `instantiate(m, strategy)`: policy substitution into a closed `BayesModel` (Proposition 5),
  `expected_utility` by the reference brute-force algorithm (Proposition 6). Both propositions
  are proved in Lean for an abstract finite model, not for the ACSet types themselves.
- `optimize` with `ExhaustivePolicySearch` (the oracle, capped) and `DecisionVariableElimination`
  over the `Valuation` algebra `(φ, ψ)` with the strong elimination order and policy recovery
  (the Julia implementation is property-tested against the oracle; the exact finite-model
  algorithm is now proved in Lean as described below). Decision variable
  elimination is exact only on diagrams with *no-forgetting* (perfect recall). That is not a
  validity condition, because a diagram that forgets is a well-formed limited-memory influence
  diagram (Lauritzen and Nilsson, 2001; see References) which exhaustive search solves exactly: `validate` accepts
  it, `no_forgetting_arcs` / `is_no_forgetting` report what is missing, `with_no_forgetting` adds
  the arcs, and the solver's `IrregularDiagramError` points at both. Shachter's (1986) *regular*
  is the weaker property that a directed path runs through all the decisions.
  Adding memory is an explicit model change, not a semantics-preserving repair:
  costly-signaling examples have limited-memory value `3/4` but perfect-recall
  value `1`, with both optima independently enumerated.
- `expected_value_of_information`, `expected_value_of_perfect_information` (SPEC section 35).
  `with_information` propagates the new arc to every later decision, which is what `info(X, D)`
  means under perfect recall, so both work with the default backend on sequential diagrams
  (`no_forgetting = false` keeps the single-arc, limited-memory reading).
- `read_influence_diagram` / `write_influence_diagram` for Netica `.dne`, GeNIe `.xdsl` and HUGIN
  `.net` through BayesianNetworkFormats.jl; `umbrella_model`, `reference_grazing_model`
  (SPEC section 46) and `two_stage_model` examples.

## Formal proof scope

The Julia DVE backend checks no-forgetting and rejects external evidence with
an action among its causal ancestors before elimination. Exhaustive search remains
available for such policy-dependent conditioning. The probability diagnostic is
relative to each row, so tiny likelihoods do not bypass it. `atol` is forwarded
through validation and oracle evaluation, but accepted rounded tables are not
silently renormalized and do not imply exact floating-point backend agreement.

The Lean project now proves global deterministic optimality for any finite number of
decisions, including limited-memory diagrams: every nonnegative strategy is a convex
mixture of deterministic policy tables. Policy rows are independently parameterised;
constraints tying different decisions' policies and absent-minded games are not part of
this model. It also proves attainment and monotonicity of the cost-free optimal
information value. All former Roadmap holes are discharged, with only `propext`,
`Classical.choice` and `Quot.sound` in the audit.

`Finite/DVE/` now proves the algorithmic result as well. It compiles separate
probability/utility valuations, generates a strong schedule from no-forgetting,
performs bucket summation/division and decision maximization, and reconstructs local
deterministic policies. `solveGuarded_spec` proves that the checked exact driver returns
a policy realizing the reported value and attaining the existing global optimum.
Probability independence is derived from structure and normalization, and the all-row
diagnostic is proved complete even when outside factors are zero; no strict-positivity
premise or assumed correct trace is used.

For nonnegative evidence likelihoods on action-free chance-ancestral sets, evidence mass
is proved independent of strategy. The guarded solver returns a conditional optimum at
positive mass and rejects exactly zero mass. This does not cover arbitrary
action-descendant evidence.

`Finite/OrderedPolicies.lean` separately proves least-state local argmax,
admissible information-table reconstruction, and label stability under a strict
`2*epsilon` action gap when every row score has error at most `epsilon`.
The order is state-position order when states are `Fin n`, not alphabetical
label order. This does not identify the entire existing DVE driver with that
separate tie selector or certify its floating-point score errors.

These are exact finite-function results, not a complete refinement of the Julia
Float64 arrays, reference lookup, explicit array conditioning or first-label tie rule.
In particular, literal floating-point DVE/oracle equality is not a theorem. See
[`proofs/README.md`](proofs/README.md) for exact statements and implementation boundaries.

The [algorithm contract](docs/src/algorithm_contract.md) collects solver
preconditions, the distinction between perfect recall and full observation,
ties and unreachable policy rows, evidence-support rules, and the separate
exact and floating-point guarantees.

## Model certificates

`export_dve_certificate(model)` captures the complete ordered model, including
raw Float64 bits, original part IDs and repeated-slot CPT/factor correspondence.
An explicit rational-companion mode checks exact nearest-even agreement without
renormalizing. See [the model certificate guide](docs/src/certificates.md).
This data export is not a proof of a production optimization trace.

`trace_decision_elimination(model)` now captures an actual exact-arithmetic
stable-DVE run, including initial/conditioned valuations, every combined and
reduced bucket, local policy choices and the returned strategy/value.
The independent workspace checker requires exact effective CPT normalization,
legal schedules and probability guards, and verifies policy reconstruction.
The default trace guard is exact; not every tolerance-accepted rounded model
is certifiable. This is a separate execution-data profile, not a claim of
verified Julia, JSON parsing or source-CPT compilation.

`trace_decision_elimination(model; include_compilation=true)` selects version 2,
adding bound Float64 kernel/CPT tables, tabular utilities and the actual factors
consumed before rational conversion. The source copies share the trace cell
budget. This provides data for checking the compilation boundary without
rerunning a substitute compiler; linking the bound model to an original JSON
request remains a separate comparison. Version 1 stays the default.

## Installation

The ecosystem packages are not registered. Install by URL, in dependency order:

```julia
using Pkg
Pkg.add(url="https://github.com/ecorecipes/FiniteKernels.jl")
Pkg.add(url="https://github.com/ecorecipes/BayesianNetworkFormats.jl")
Pkg.add(url="https://github.com/ecorecipes/BayesianNetworks.jl")
Pkg.add(url="https://github.com/ecorecipes/BayesianNetworkInference.jl")
Pkg.add(url="https://github.com/ecorecipes/InfluenceDiagrams.jl")
```

Requires Julia >= 1.12. For development, clone the siblings next to this repository
(`../FiniteKernels.jl` and so on; see `[sources]` in `Project.toml`).

## Quick Start

```julia
using InfluenceDiagrams

id = influence_diagram(:Weather => [:sunny, :rainy], :Forecast => [:sunny, :cloudy, :rainy],
                       :Umbrella => [:take, :leave];
                       mechanisms = [:Forecast => :Weather],
                       decisions = [:Umbrella => :Forecast],          # information arc
                       utilities = [:U => (:Weather, :Umbrella)])
validate(id; closed = true)

m = InfluenceDiagramModel(id)
m = bind_cpt(m, [:Weather => [0.7, 0.3], :Forecast => [0.7 0.2 0.1; 0.15 0.25 0.6]])
m = bind_utility(m, :U => [20.0 100.0; 70.0 0.0])

expected_utility(m, :Umbrella => :leave)      # 70: the best fixed action
sol = optimize(m)                              # decision variable elimination
sol.expected_utility                           # 77
policy_table(sol.strategy[:Umbrella])          # [:leave, :leave, :take]
optimize(m, ExhaustivePolicySearch()).expected_utility   # the oracle agrees

noinfo = without_information(m, :Umbrella, :Forecast)
expected_value_of_information(noinfo, :Forecast, :Umbrella)   # 7
expected_value_of_perfect_information(noinfo, :Umbrella)      # 21

bn = instantiate(m, sol.strategy)              # an ordinary closed BayesModel
g = read_influence_diagram(fixture_path("dne/grazing_reference_id.dne"))
```

For underflowed evidence or large cancelling utilities, opt into the stable path:

```julia
sol = optimize(m, DecisionVariableElimination(stable=true))
eu = expected_utility(m, sol.strategy; stable=true)
```

Stable DVE runs the same bucket schedule with exact rational meanings of the
bound data and correctly rounds the returned Float64 value using integer
quotient/remainder arithmetic, independently of ambient BigFloat precision.
Exact arithmetic was chosen over logging signed utilities or relying on a
fixed working precision, which can still lose small terms before cancellation.
It is more expensive per factor cell than Float64, but scales with factor
width rather than the number of policies; it can solve cases beyond the
exhaustive-search cap. Diagnostics retain finite log evidence when ordinary
evidence mass underflows.

`expected_utility(...; stable=true)` instead evaluates utilities separately using
log-domain marginals and compensated accumulation. The capped
`ExhaustivePolicySearch(stable=true)` remains available as a slower comparator.
Stable DVE retains the no-forgetting and action-free evidence requirements.
It does not renormalize accepted rounded CPTs; `exact_probability_guards`
distinguishes exact action independence from tolerance acceptance.
Defaults remain unchanged. These runtime options are not a universal
Julia/compiler/IEEE correctness theorem.

## Vignettes

Rendered vignettes live in [`vignettes/`](vignettes/) and are published in the
[documentation](https://ecorecipes.github.io/InfluenceDiagrams.jl/):

1. Influence diagrams: decisions, information arcs, utilities and validation.
2. Policies and expected utility, and `instantiate` as a Bayesian network.
3. Optimisation: exhaustive policy search against decision variable elimination.
4. Value of information and of perfect information.
5. Composing an ecological model with a management decision.
6. Exact arithmetic for decisions: where `stable=true` matters and where it does not.

## Development

```sh
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
julia --project=docs docs/make.jl
cd vignettes && julia --project=. -e 'using Pkg; Pkg.instantiate()' && quarto render
julia scripts/sync_vignettes.jl --check
cd proofs && lake build && lake exe emit_schema --check
```

See `CONTRIBUTING.md` and `docs/adr/` for the conventions and design decisions.

## References

The works this package implements. The same entries, with the rest of the ecosystem's
bibliography, are in [`vignettes/references.bib`](vignettes/references.bib) and on the
[References page](https://ecorecipes.github.io/InfluenceDiagrams.jl/references/) of the
documentation.

- Howard, R. A. and Matheson, J. E. (2005). Influence diagrams. *Decision Analysis*
  2(3), 127-143.
  doi:[10.1287/deca.1050.0020](https://doi.org/10.1287/deca.1050.0020) (a reprint of the
  1984 chapter) -- the representation.
- Shachter, R. D. (1986). Evaluating influence diagrams. *Operations Research* 34(6),
  871-882. doi:[10.1287/opre.34.6.871](https://doi.org/10.1287/opre.34.6.871)
  -- evaluation, the umbrella example, and *regular* as distinct from no-forgetting.
- Tatman, J. A. and Shachter, R. D. (1990). Dynamic programming and influence diagrams.
  *IEEE Transactions on Systems, Man, and Cybernetics* 20(2), 365-379.
  doi:[10.1109/21.52548](https://doi.org/10.1109/21.52548) -- decision elimination as
  dynamic programming.
- Jensen, F., Jensen, F. V. and Dittmer, S. L. (1994). From influence diagrams to
  junction trees. *UAI 1994*, 367-373 -- the `(φ, ψ)` division algebra of `Valuation`.
- Lauritzen, S. L. and Nilsson, D. (2001). Representing and solving decision problems
  with limited information. *Management Science* 47(9), 1235-1251.
  doi:[10.1287/mnsc.47.9.1235.9779](https://doi.org/10.1287/mnsc.47.9.1235.9779)
  -- limited-memory diagrams, which `validate` accepts and exhaustive search solves.
- Bielza, C., Gomez, M. and Shenoy, P. P. (2011). A review of representation issues and
  modeling challenges with influence diagrams. *Omega* 39(3), 227-241.
  doi:[10.1016/j.omega.2010.07.003](https://doi.org/10.1016/j.omega.2010.07.003)
  -- the representation choices `SchInfluenceDiagram` settles.
- Howard, R. A. (1966). Information value theory. *IEEE Transactions on Systems Science
  and Cybernetics* 2(1), 22-26.
  doi:[10.1109/TSSC.1966.300074](https://doi.org/10.1109/TSSC.1966.300074), and
  Raiffa, H. (1968). *Decision Analysis: Introductory Lectures on Choices under
  Uncertainty*. Addison-Wesley -- `expected_value_of_information` and
  `expected_value_of_perfect_information`, and the test-then-act example.

Related work: `DecisionProgramming.jl` solves influence diagrams by mixed-integer
programming (Salo, A., Andelmin, J. and Oliveira, F., 2022, Decision programming for
mixed-integer multi-stage optimization under uncertainty, *European Journal of
Operational Research* 299(2), 550-565,
doi:[10.1016/j.ejor.2021.12.013](https://doi.org/10.1016/j.ejor.2021.12.013)), where
this package solves them by elimination over a valuation algebra and by exhaustive
search; the two have different scope, and the MILP formulation handles constraints that
elimination cannot.

## License

MIT, copyright 2026 Simon Frost.
