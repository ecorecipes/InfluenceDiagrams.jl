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
  functions) rather than for the ACSet types themselves. The former single-decision
  Roadmap theorem is now proved and strengthened to global deterministic sufficiency
  for any finite number of independently parameterised decisions, even with limited
  memory. That mixture proof is now complemented by an actual exact finite-function
  DVE algorithm and its correctness proof, rather than being relabelled as an
  algorithm theorem.
- `optimize` with `ExhaustivePolicySearch` (the oracle) and
  `DecisionVariableElimination` over the `Valuation` algebra with the strong
  elimination order (the Julia implementation remains property-tested against the oracle). The latter is
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

The Lean information theorem now concerns attained optimal values: enlarging the
information sets cannot decrease the cost-free optimum. It does not verify a temporal
information edit, an acquisition-cost recommendation or the Julia solver. All default
and compatibility Roadmap targets are `sorry`-free; the axiom audit uses only
`propext`, `Classical.choice` and `Quot.sound`.

The exact DVE development generates its structural schedule from no-forgetting,
compiles separate valuations, executes chance/max bucket steps and reconstructs local
deterministic policies. `solveGuarded_spec` proves realized optimality and acceptance
of the exact probability diagnostic on every row, including zero-outside contexts.
Supported action-free ancestral evidence has a proved strategy-independent normalizer;
the checked solver rejects exactly zero evidence mass. The proof does not add
strict positivity or smooth the input at runtime.

`Finite/OrderedPolicies.lean` adds a separate ordered local argmax and its
admissible information-table reconstruction. A strict `2*epsilon` action gap
protects the selected label against uniformly bounded score errors of
`epsilon`; ties and unreachable rows have no such stability guarantee.
This does not silently replace the DVE driver's existing selector.

The Julia array/reference representation, whole-driver first-label identity and floating-point
rounding remain outside that theorem. The general open-network syntax category is
proved separately in `CategoricalBayesianNetworks.jl/proofs/`; neither result is a
semantic-equality quotient that silently erases hidden mechanisms.

## Perfect recall is not full observation

No-forgetting means retaining information already available, not observing every
chance variable. A hidden state stays hidden unless an information arc makes it
available to the relevant decision.

For example, let a fair hidden binary state determine whether a final guess is
rewarded. An earlier decision has no information, and the final decision
remembers only that earlier action:

```julia
id = influence_diagram(:Hidden => [:zero, :one], :First => [:left, :right],
                       :Guess => [:zero, :one];
                       decisions=[:First => (), :Guess => :First],
                       utilities=[:Reward => (:Hidden, :Guess)])
m = bind_cpt(InfluenceDiagramModel(id), :Hidden => [.5, .5])
m = bind_utility(m, :Reward => [1.0 0.0; 0.0 1.0])
is_no_forgetting(m)                         # true
optimize(m).expected_utility                # 0.5
informed = with_information(m, :Guess, :Hidden)
optimize(informed).expected_utility         # 1.0
```

The original diagram already has perfect recall. Its optimal success
probability is one half because neither decision can read the hidden state.
The larger value belongs to a different information structure. Maximizing the
guess separately for each hidden state before averaging would incorrectly give
the original decision maker that extra information. DVE instead sums out this
unobserved chance coordinate before maximizing the guess.

External evidence is another distinct operation. `observe(m, :Hidden => :zero)`
defines a conditional problem whose evidence mass is one half; it does not add
an information arc or a policy argument. In general, normalized chance kernels
give total unconditional mass one, not evidence mass one. Conditional expected
utility requires the actual evidence mass to be positive; impossible evidence
must reject rather than become an ordinary zero-utility answer.

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
