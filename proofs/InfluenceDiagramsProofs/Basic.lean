import BayesianNetworksProofs.Schema.BayesNet

/-!
# InfluenceDiagramsProofs

Lean 4 / Mathlib formalisation accompanying `InfluenceDiagrams.jl` (toolchain
`leanprover/lean4:v4.30.0`, Mathlib tag `v4.30.0`; ADR 0005). This document is generated from
the Lean sources by [mdgen](https://github.com/Seasawher/mdgen): the prose is the module
docstrings and the code blocks are the verbatim, machine-checked sources. Every library module
is built by `lake build --wfail`; `Audit.lean` prints the axioms of the headline results
(only `propext`, `Classical.choice`, `Quot.sound`). The Roadmap has no remaining proof holes.

The project depends by path on `BayesianNetworks.jl/proofs` (Lake package
`bayesian_networks_proofs`), which supplies the finite Bayesian-network model (`FinBayesNet`,
kernels, `Local`, `Normalised`, `Closed`, `TopoOrder`, `joint`, Propositions 1 and 4) and the
ACSet schema terms; the influence-diagram schema `schInfluenceDiagram` is defined there and
re-emitted here by `lake exe emit_schema`.

## What is formalised

`InfluenceDiagrams.jl` represents an influence diagram as an ACSet on `SchInfluenceDiagram`
(SPEC §24: decisions, information arcs, utilities, decision precedence). A complete strategy
turns it into a Bayesian network (`instantiate`, SPEC §28) whose joint gives the expected
utility (`expected_utility`, SPEC §29–§31); fixing a decision (`fix_decision`, SPEC §41) is an
intervention, and adding information arcs cannot lower the optimal expected utility
(SPEC §34–§35, §55.7). The algebraic results are over an arbitrary commutative semiring `R`;
the optimisation and attained-optimum information results use `ℝ` and nonnegative strategies.

* `Finite/InfluenceDiagram.lean`: decisions, information and utility scopes, validity,
  policies, complete strategies and fixed decisions.
* `Finite/Instantiate.lean`: Proposition 5, policy substitution, factorisation, locality
  and normalisation of the instantiated joint.
* `Finite/ExpectedUtility.lean`: Proposition 6, linearity, additive utilities and fixed
  decisions as hard interventions.
* `Finite/Information.lean`: strategy inclusion under information enlargement, with exactly
  the same expected utility.
* `Finite/Optimization.lean`: exact convex mixtures of deterministic tables and global
  deterministic optimality for any finite number of decisions, including limited memory.
  Signed-weight counterexample.
* `Finite/OptimalInformation.lean`: attainment of the finite optimum, monotonicity of the
  optimal value and nonnegativity of cost-free information value.
* `Finite/DVE/`: an actual probability/utility bucket driver, strong schedules generated from
  no-forgetting, local policy reconstruction, exact realized optimality, and positive-mass
  action-independent evidence. A hidden-state two-decision example checks nonvacuity.
* `Finite/DVE/Guard/`: exact max-minus-min diagnostic completeness on all rows, including
  zero-outside contexts, proved by probability-expression provenance and normalized smoothing.
* `Finite/OrderedPolicies.lean`: first-state local ties in a supplied finite order, finite
  information-table reconstruction, and stability under a strict numerical action gap.
* `Roadmap.lean`: remaining literal-Julia refinement boundaries; no unproved declarations.

## Correspondence with SPEC and the Julia API

| SPEC | Lean | Julia (`InfluenceDiagrams.jl`) |
|:--------------|:-------------------|:---------------|
| §26–§27 policies, strategies | `Policy`, `Policy.ofFun`, `Strategy` | `DeterministicPolicy`, `StochasticPolicy`, `Strategy` |
| §28, §61 Prop 5 — policy instantiation yields a valid BN | `instantiate`, `strategyKernel`, `closed_instantiate`, `IDOrder.toTopoOrder`, `sum_joint_instantiate_eq_one`, `joint_instantiate` | `instantiate(id, strategy) -> BayesNet` (`validate(closed=true)` succeeds) |
| §29–§31, §61 Prop 6 — `EU(σ) = E_{P_σ}[U]` | `Utility`, `totalUtility`, `expectedUtility`, `expectedUtility_eq`, `expectedUtility_eq_sum` | `expected_utility(id, strategy)` (instantiate, enumerate the joint, sum utilities, take the expectation) |
| §41 fixed decision | `Policy.const`, `Strategy.fix`, `strategyKernel_fix_eq_intervene`, `joint_fix` | `fix_decision(model, :D => :a)` = `do_intervention` on the instantiated network |
| §34–§35, §55.7 information monotonicity | `optimalValue_info_mono`, `optimal_information_value_nonneg`, based on attained maxima and `expectedUtility_enlarge` | cost-free exact expected value of information is nonnegative; no solver correctness asserted |
| §32 global policy optimisation | `exists_deterministic_optimal_all`, with the original single-decision theorem as a corollary | finite exhaustive-table optimum, not an implementation proof |
| §33, §61 Prop 7 — DVE correctness | Actual finite-function bucket solver, generated strong order, realized optimal policies, and exact all-row diagnostic completeness | Array layout, first-label tie identity and Float64/tolerance behavior remain refinement questions |
| §24 schema | `schInfluenceDiagram` (BayesianNetworks project), `lake exe emit_schema` | `SchInfluenceDiagram`, compared with the emitted schema JSON |
-/

namespace InfluenceDiagramsProofs

/-- Smoke lemma so that the axiom audit always has a first line. -/
theorem smoke : (1 : Nat) + 1 = 2 := rfl

end InfluenceDiagramsProofs
