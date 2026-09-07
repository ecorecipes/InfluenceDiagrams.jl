# InfluenceDiagrams.jl

Influence diagrams over compositional Bayesian networks: decisions, information sets,
utilities, policies, expected utility, decision variable elimination, and value of
information.

Part of the ecorecipes compositional Bayesian-network ecosystem:
`FiniteKernels.jl` -> `BayesianNetworks.jl` ->
`BayesianNetworkInference.jl` ->
`InfluenceDiagrams.jl`, with `BayesianNetworkFormats.jl` (file formats) and
`EcologicalBayesianNetworks.jl` (model zoo).

## What it provides

- The `SchInfluenceDiagram` schema (SPEC section 24), an extension of `SchBayesNet`
  with `Decision`, `InformationInput`, `Utility`, `UtilityInput` and
  `DecisionPrecedence`, and the `InfluenceDiagram` ACSet type with builders,
  inspection, JSON serialisation and the structural checks of SPEC section 37.
- `InfluenceDiagramModel`: chance kernels, bound utilities and a `Strategy` of
  policies (`DeterministicPolicy`, `StochasticPolicy`, `ConstantPolicy`) over the
  syntax, with `fix_decision`, `set_policy`, `observe`, `do_intervention` and the
  information-structure edits `with_information` / `without_information`.
- `instantiate`: policy substitution, the central reduction to a closed `BayesModel`
  (Proposition 5), and `expected_utility` by the reference algorithm (Proposition 6).
  Both are proved in the Lean project in `proofs/`, for an abstract finite model
  (`FinInfluenceDiagram` over `FinBayesNet`, with unordered parent sets and kernels as
  functions) rather than for the ACSet types themselves. Proposition 7 has no proof: the
  Lean file carries a single-decision shadow with a `sorry`, so DVE correctness rests on
  the property tests below.
- `optimize` with `ExhaustivePolicySearch` (the oracle) and
  `DecisionVariableElimination` over the `Valuation` algebra with the strong
  elimination order (Proposition 7, property-tested against the oracle). The latter is
  exact only on diagrams with *no-forgetting* (perfect recall), which `validate`
  deliberately does not require: a diagram that forgets is a well-formed limited-memory
  influence diagram ([LauritzenNilsson2001](@cite)) that exhaustive search solves exactly.
  `no_forgetting_arcs` and `is_no_forgetting` report what is missing,
  `with_no_forgetting` supplies it, and the solver's `IrregularDiagramError` names both
  ways out. The *regular* of [Shachter1986](@cite) is the weaker property that a directed path runs
  through all the decisions.
- `expected_value_of_information` and `expected_value_of_perfect_information`.
  `with_information` propagates the new information arc to every later decision (SPEC
  section 35's `info(X, D)` under perfect recall), so both work with the default backend
  on sequential diagrams; `no_forgetting = false` keeps the single-arc, limited-memory
  reading.
- `read_influence_diagram` / `write_influence_diagram` for Netica, GeNIe and HUGIN
  files through BayesianNetworkFormats.jl, and `to_graphviz` drawings.

## Quick start

```julia
using InfluenceDiagrams

m = umbrella_model()                              # the umbrella problem of Shachter (1986)
expected_utility(m, :Umbrella => :leave)          # 70
optimize(m).expected_utility                      # 77 with the forecast
noinfo = without_information(m, :Umbrella, :Forecast)
expected_value_of_information(noinfo, :Forecast, :Umbrella)     # 7
expected_value_of_perfect_information(noinfo, :Umbrella)        # 21

g = read_influence_diagram(fixture_path("dne/grazing_reference_id.dne"))
sol = optimize(g)
policy_table(sol.strategy[:GrazingManagement])
```

## References

The representation is [HowardMatheson2005](@cite), evaluated in the sense of
[Shachter1986](@cite), with the representation choices surveyed by
[BielzaGomezShenoy2011](@cite). Decision variable elimination is the dynamic programming
of [TatmanShachter1990](@cite) over the division algebra of
[JensenJensenDittmer1994](@cite); diagrams that forget are the limited-memory diagrams
of [LauritzenNilsson2001](@cite). The value of information is [Howard1966](@cite) and
[Raiffa1968](@cite). `DecisionProgramming.jl` [Salo2022](@cite) solves the same problems
by mixed-integer programming instead. Full entries are on the [References](references.md) page.

See the tutorials for the schema, policies and instantiation, the two optimisation
backends, the value of information and the SPEC section 46 ecological management
analyses.
