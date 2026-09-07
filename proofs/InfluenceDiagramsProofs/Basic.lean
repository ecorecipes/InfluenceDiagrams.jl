import BayesianNetworksProofs.Schema.BayesNet

/-!
# InfluenceDiagramsProofs

Lean 4 / Mathlib formalisation accompanying `InfluenceDiagrams.jl` (toolchain
`leanprover/lean4:v4.30.0`, Mathlib tag `v4.30.0`; ADR 0005). This document is generated from
the Lean sources by [mdgen](https://github.com/Seasawher/mdgen): the prose is the module
docstrings and the code blocks are the verbatim, machine-checked sources. Every declaration
outside the final "Roadmap" section is built by `lake build --wfail` and its axioms are printed
by `Audit.lean` (only `propext`, `Classical.choice`, `Quot.sound`).

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
(SPEC §34–§35, §55.7). All results are over an arbitrary commutative semiring `R`.

| Part | Module | Content |
|:--|:-----------------|:-----------------------------------|
| 1 | `Finite/InfluenceDiagram.lean` | `FinInfluenceDiagram extends FinBayesNet` (decisions, `action`, `info`, utility nodes, `uscope`); validity (`GeneratorsDisjoint`, `GeneratorsCover`, `Closed`, `closed_iff`, `IDOrder`); `Policy`, `Policy.ofFun`, `Policy.const`, `Strategy`, `Strategy.fix`. |
| 2 | `Finite/Instantiate.lean` | Proposition 5: `instantiate`, `strategyKernel`, `closed_instantiate`, `IDOrder.toTopoOrder`, `local_instantiate`, `normalised_instantiate`, `sum_joint_instantiate_eq_one`, `joint_instantiate`. |
| 3 | `Finite/ExpectedUtility.lean` | Proposition 6: `Utility`, `totalUtility`, `expectedUtility`, `expectedUtility_eq`, linearity, `expectedUtility_eq_sum`, `expectedUtility_const`; `fix_decision` as a hard intervention (`strategyKernel_fix_eq_intervene`, `joint_fix`, `expectedUtility_fix`). |
| 4 | `Finite/Information.lean` | Information monotonicity: `localOn_mono`, `withInfo`, `Policy.enlarge`, `Strategy.enlarge`, `expectedUtility_enlarge`, `exists_strategy_enlarged_eq`. |
| — | `Roadmap.lean` | Proposition 7 (single-decision shadow, `sorry`); not in the default target. |

## Correspondence with SPEC and the Julia API

| SPEC | Lean | Julia (`InfluenceDiagrams.jl`) |
|:--------------|:-------------------|:---------------|
| §26–§27 policies, strategies | `Policy`, `Policy.ofFun`, `Strategy` | `DeterministicPolicy`, `StochasticPolicy`, `Strategy` |
| §28, §61 Prop 5 — policy instantiation yields a valid BN | `instantiate`, `strategyKernel`, `closed_instantiate`, `IDOrder.toTopoOrder`, `sum_joint_instantiate_eq_one`, `joint_instantiate` | `instantiate(id, strategy) -> BayesNet` (`validate(closed=true)` succeeds) |
| §29–§31, §61 Prop 6 — `EU(σ) = E_{P_σ}[U]` | `Utility`, `totalUtility`, `expectedUtility`, `expectedUtility_eq`, `expectedUtility_eq_sum` | `expected_utility(id, strategy)` (instantiate, enumerate the joint, sum utilities, take the expectation) |
| §41 fixed decision | `Policy.const`, `Strategy.fix`, `strategyKernel_fix_eq_intervene`, `joint_fix` | `fix_decision(model, :D => :a)` = `do_intervention` on the instantiated network |
| §34–§35, §55.7 information monotonicity | `withInfo`, `Strategy.enlarge`, `exists_strategy_enlarged_eq` | `expected_value_of_information` is non-negative |
| §33, §61 Prop 7 — DVE correctness | `Roadmap.exists_deterministic_optimal` (single-decision shadow, unproved) | `optimize(id; backend=Exhaustive())` versus DVE, property tests (SPEC §55.6) |
| §24 schema | `schInfluenceDiagram` (BayesianNetworks project), `lake exe emit_schema` | `SchInfluenceDiagram`, compared with `schemas/influence_diagram.schema.json` |
-/

namespace InfluenceDiagramsProofs

/-- Smoke lemma so that the axiom audit always has a first line. -/
theorem smoke : (1 : Nat) + 1 = 2 := rfl

end InfluenceDiagramsProofs
