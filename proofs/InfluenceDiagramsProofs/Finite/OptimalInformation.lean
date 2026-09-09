import InfluenceDiagramsProofs.Finite.Information
import InfluenceDiagramsProofs.Finite.Optimization

/-!
# InfluenceDiagramsProofs.Finite.OptimalInformation

**Monotonicity of the attained optimal value**, not only existence of an equal-value
enlarged strategy (SPEC §34–§35, §55.7).

The finite optimum from `Optimization.lean` makes the optimal value a real number attained
by a nonnegative deterministic strategy. Enlarging information preserves all old strategies,
their nonnegativity and expected utilities. Hence the new optimal value is at least the old
one, and their difference is nonnegative.

Chance kernels and utilities are held fixed. No acquisition cost is introduced. This is a
statement about the admissible strategy classes, not Julia's solver, automatic propagation
of no-forgetting arcs, or the validity of an information enlargement as a temporal diagram.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.FinInfluenceDiagram

variable {id : FinInfluenceDiagram}

/-- The attained finite optimal expected utility (defined by choice of a proved maximizer). -/
noncomputable def optimalValue (κ : id.Kernel ℝ) (u : Utility id ℝ) : ℝ :=
  expectedUtility κ (Classical.choose (exists_deterministic_optimal_all κ u)) u

theorem optimalValue_attained (κ : id.Kernel ℝ) (u : Utility id ℝ) :
    ∃ σ : Strategy id ℝ, σ.Deterministic ∧ σ.Nonneg ∧
      expectedUtility κ σ u = optimalValue κ u := by
  refine ⟨Classical.choose (exists_deterministic_optimal_all κ u), ?_, ?_, rfl⟩
  · exact (Classical.choose_spec (exists_deterministic_optimal_all κ u)).1
  · exact (Classical.choose_spec (exists_deterministic_optimal_all κ u)).2.1

theorem expectedUtility_le_optimalValue (κ : id.Kernel ℝ) (u : Utility id ℝ)
    (σ : Strategy id ℝ) (hσ : σ.Nonneg) : expectedUtility κ σ u ≤ optimalValue κ u :=
  (Classical.choose_spec (exists_deterministic_optimal_all κ u)).2.2 σ hσ

/-- **Optimal information monotonicity.** Both sides are attained maxima, not unproved suprema. -/
theorem optimalValue_info_mono {info' : id.D → Finset id.V} (h : ∀ d, id.info d ⊆ info' d)
    (κ : id.Kernel ℝ) (u : Utility id ℝ) :
    optimalValue κ u ≤ optimalValue (id := id.withInfo info') κ u := by
  obtain ⟨σ, _, hσ, heq⟩ := optimalValue_attained κ u
  have hen : (σ.enlarge h).Nonneg := hσ
  rw [← heq, ← expectedUtility_enlarge h κ σ u]
  exact expectedUtility_le_optimalValue (id := id.withInfo info') κ u (σ.enlarge h) hen

/-- Cost-free expected value of information is nonnegative for the exact finite optimum. -/
theorem optimal_information_value_nonneg {info' : id.D → Finset id.V}
    (h : ∀ d, id.info d ⊆ info' d) (κ : id.Kernel ℝ) (u : Utility id ℝ) :
    0 ≤ optimalValue (id := id.withInfo info') κ u - optimalValue κ u :=
  sub_nonneg.mpr (optimalValue_info_mono h κ u)

end InfluenceDiagramsProofs.FinInfluenceDiagram
