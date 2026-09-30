import InfluenceDiagramsProofs.Finite.DVE.Conditioning

/-!
# SA-Pass shadow module: the conditioned driver's final mass is the evidence mass

Claim `id.conditioned-mass`, from `DVE.conditionedMass_eq`: "`conditionedMass_eq` proves that
its final probability is exactly the evidence mass."

"Its final probability" is `conditionedMass`, the final probability potential of the
conditioned driver (Julia's `evidence_probability`), for any selector; "the evidence mass" is
`evidenceMass` of the indicator likelihood of the same hard evidence. No positivity is assumed.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.ConditionedMass

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram InfluenceDiagramsProofs.DVE

/-- `conditionedMass_eq`, restated abstractly with every hypothesis. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j) (H : HardEvidence id),
    conditionedMass sel κ hloc hnonneg u hu ord nf H.observed H.value =
      evidenceMass κ defaultStrategy H.toEvidence

/-- The final probability never exceeds the evidence mass. -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j) (H : HardEvidence id),
    conditionedMass sel κ hloc hnonneg u hu ord nf H.observed H.value ≤
      evidenceMass κ defaultStrategy H.toEvidence

/-- The final probability is at least the evidence mass; with `Shadow1`, "exactly". -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j) (H : HardEvidence id),
    evidenceMass κ defaultStrategy H.toEvidence ≤
      conditionedMass sel κ hloc hnonneg u hu ord nf H.observed H.value

theorem forward1 : Candidate → Shadow1 := fun h id sel κ hc ord nf hloc hnorm hnonneg u hu H =>
  (h id sel κ hc ord nf hloc hnorm hnonneg u hu H).le

theorem forward2 : Candidate → Shadow2 := fun h id sel κ hc ord nf hloc hnorm hnonneg u hu H =>
  (h id sel κ hc ord nf hloc hnorm hnonneg u hu H).ge

theorem backward : Shadow1 → Shadow2 → Candidate :=
  fun h1 h2 id sel κ hc ord nf hloc hnorm hnonneg u hu H =>
    le_antisymm (h1 id sel κ hc ord nf hloc hnorm hnonneg u hu H)
      (h2 id sel κ hc ord nf hloc hnorm hnonneg u hu H)

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ sel κ hc ord nf hloc hnorm hnonneg u hu H =>
  InfluenceDiagramsProofs.DVE.conditionedMass_eq sel κ hc ord nf hloc hnorm hnonneg u hu H

end InfluenceDiagramsProofs.Shadows.ConditionedMass
