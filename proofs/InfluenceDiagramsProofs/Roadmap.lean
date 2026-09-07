import InfluenceDiagramsProofs.Finite.ExpectedUtility
import Mathlib.Data.Real.Basic

/-!
# Roadmap (contains `sorry`)

Module `InfluenceDiagramsProofs.Roadmap`.
Statements that are **not yet proved**. This module is deliberately *not* imported by the
default target (`InfluenceDiagramsProofs.lean`) and is excluded from `Audit.lean`; build it with
`lake build InfluenceDiagramsProofs.Roadmap` (or `make roadmap`). Every `sorry` here is listed in
`README.md`.

## Proposition 7 — DVE correctness (SPEC §33, §61)

Decision variable elimination returns the maximal expected utility together with a *policy
table*, i.e. a deterministic strategy. Its correctness therefore rests on the fact that, in the
supported regular subset, deterministic policies suffice. The single-decision shadow of that
statement is below: over `ℝ`, with non-negative chance kernels, some deterministic strategy
dominates every non-negative strategy. (With several decisions and imperfect recall this can
fail, which is why the Julia solver restricts itself to a regular subset and is checked against
exhaustive policy enumeration, SPEC §55.6.)
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet

namespace FinInfluenceDiagram

variable {id : FinInfluenceDiagram}

/-- A strategy is deterministic when every policy is of the form `Policy.ofFun`. -/
def Strategy.Deterministic (σ : Strategy id ℝ) : Prop :=
  ∀ d, ∃ f hf, σ d = Policy.ofFun f hf

/-- A strategy is non-negative when every policy kernel is. -/
def Strategy.Nonneg (σ : Strategy id ℝ) : Prop :=
  ∀ d x a, 0 ≤ (σ d).kernel x a

/-- **Proposition 7 (single-decision shadow, unproved).** For one decision, non-negative chance
kernels and any utility, some deterministic strategy is optimal among non-negative strategies:
the exhaustive search over policy tables of `optimize(id; backend=Exhaustive())` finds the
optimum. -/
theorem exists_deterministic_optimal [Unique id.D] (κ : id.Kernel ℝ)
    (hκ : ∀ m x y, 0 ≤ κ m x y) (u : Utility id ℝ) :
    ∃ σ' : Strategy id ℝ, σ'.Deterministic ∧
      ∀ σ : Strategy id ℝ, σ.Nonneg → expectedUtility κ σ u ≤ expectedUtility κ σ' u := by
  sorry

end FinInfluenceDiagram

end InfluenceDiagramsProofs
