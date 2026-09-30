import InfluenceDiagramsProofs.Finite.OptimalInformation

/-!
# SA-Pass shadow module: attainment and monotonicity of the optimal information value

Claim `id.optimal-information`, from `optimalValue_attained` and `optimalValue_info_mono`.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.OptimalInformation

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram

/-- `optimalValue_attained` and `optimalValue_info_mono`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (u : Utility id ℝ),
    (∃ σ : Strategy id ℝ, σ.Deterministic ∧ σ.Nonneg ∧ expectedUtility κ σ u = optimalValue κ u) ∧
      ∀ (info' : id.D → Finset id.V), (∀ d, id.info d ⊆ info' d) →
        optimalValue κ u ≤ optimalValue (id := id.withInfo info') κ u

/-- "attainment": the optimal value is attained by an admissible strategy -- nonnegative, and
deterministic, so the optimum is a maximum over finitely many policy tables -- not an unattained
supremum. -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (u : Utility id ℝ),
    ∃ σ : Strategy id ℝ, σ.Deterministic ∧ σ.Nonneg ∧ expectedUtility κ σ u = optimalValue κ u

/-- "monotonicity of the cost-free optimal information value": adding information never makes
the attained optimum worse, so the information value is nonnegative. -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (u : Utility id ℝ)
      (info' : id.D → Finset id.V), (∀ d, id.info d ⊆ info' d) →
    0 ≤ optimalValue (id := id.withInfo info') κ u - optimalValue κ u

theorem forward1 : Candidate → Shadow1 := fun h id κ u => (h id κ u).1

theorem forward2 : Candidate → Shadow2 := by
  intro h id κ u info' hsub
  exact sub_nonneg.mpr ((h id κ u).2 info' hsub)

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 id κ u
  exact ⟨h1 id κ u, fun info' hsub => sub_nonneg.mp (h2 id κ u info' hsub)⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated, so a restatement that
drifts from the proved theorem stops compiling. -/
theorem anchor : Candidate := fun _ κ u =>
  ⟨InfluenceDiagramsProofs.FinInfluenceDiagram.optimalValue_attained κ u,
   fun _ h => InfluenceDiagramsProofs.FinInfluenceDiagram.optimalValue_info_mono h κ u⟩

end InfluenceDiagramsProofs.Shadows.OptimalInformation
