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
  (Proposition 7, property-tested against the oracle on random diagrams). Decision variable
  elimination is exact only on diagrams with *no-forgetting* (perfect recall). That is not a
  validity condition, because a diagram that forgets is a well-formed limited-memory influence
  diagram (Lauritzen and Nilsson, 2001; see References) which exhaustive search solves exactly: `validate` accepts
  it, `no_forgetting_arcs` / `is_no_forgetting` report what is missing, `with_no_forgetting` adds
  the arcs, and the solver's `IrregularDiagramError` points at both. Shachter's (1986) *regular*
  is the weaker property that a directed path runs through all the decisions.
- `expected_value_of_information`, `expected_value_of_perfect_information` (SPEC section 35).
  `with_information` propagates the new arc to every later decision, which is what `info(X, D)`
  means under perfect recall, so both work with the default backend on sequential diagrams
  (`no_forgetting = false` keeps the single-arc, limited-memory reading).
- `read_influence_diagram` / `write_influence_diagram` for Netica `.dne`, GeNIe `.xdsl` and HUGIN
  `.net` through BayesianNetworkFormats.jl; `umbrella_model`, `reference_grazing_model`
  (SPEC section 46) and `two_stage_model` examples.

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
