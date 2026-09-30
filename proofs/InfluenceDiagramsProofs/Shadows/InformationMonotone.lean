import InfluenceDiagramsProofs.Finite.OptimalInformation

/-!
# SA-Pass shadow module: "the optimal expected utility cannot decrease when information is added"

Claim `id.information-monotone`. The candidate is `optimalValue_info_mono`, which compares the
two diagrams' *optimal* values directly. (An earlier revision of this file cited
`exists_strategy_enlarged_eq`; that lemma matches each strategy with an equal-expected-utility
strategy of the enlarged diagram and says nothing about either optimum, so the forward check
failed. The citation, not the claim, was wrong.)
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.InformationMonotone

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram

/-- `optimalValue_info_mono` over `ℝ`, restated abstractly over the data. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) (info' : id.D → Finset id.V), (∀ d, id.info d ⊆ info' d) →
    ∀ (κ : id.Kernel ℝ) (u : Utility id ℝ),
      optimalValue κ u ≤ optimalValue (id := id.withInfo info') κ u

/-- The value of the added information is nonnegative: the reading "cannot decrease". -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) (info' : id.D → Finset id.V), (∀ d, id.info d ⊆ info' d) →
    ∀ (κ : id.Kernel ℝ) (u : Utility id ℝ),
      0 ≤ optimalValue (id := id.withInfo info') κ u - optimalValue κ u

/-- No strategy of the smaller-information diagram beats the enlarged optimum. -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) (info' : id.D → Finset id.V), (∀ d, id.info d ⊆ info' d) →
    ∀ (κ : id.Kernel ℝ) (u : Utility id ℝ) (σ : Strategy id ℝ), σ.Nonneg →
      expectedUtility κ σ u ≤ optimalValue (id := id.withInfo info') κ u

theorem forward1 : Candidate → Shadow1 := by
  intro h id info' hsub κ u
  exact sub_nonneg.mpr (h id info' hsub κ u)

theorem forward2 : Candidate → Shadow2 := by
  intro h id info' hsub κ u σ hσ
  exact le_trans (expectedUtility_le_optimalValue κ u σ hσ) (h id info' hsub κ u)

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 _ id info' hsub κ u
  exact sub_nonneg.mp (h1 id info' hsub κ u)

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated, so a restatement that
drifts from the proved theorem stops compiling. -/
theorem anchor : Candidate := fun _ _ h κ u =>
  InfluenceDiagramsProofs.FinInfluenceDiagram.optimalValue_info_mono h κ u

end InfluenceDiagramsProofs.Shadows.InformationMonotone
