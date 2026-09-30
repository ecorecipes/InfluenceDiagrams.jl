import InfluenceDiagramsProofs.Finite.DVE.Conditioning

/-!
# SA-Pass shadow module: DVE on explicitly conditioned (sliced) factors

Claim `id.dve-conditioning`, from `DVE.solveConditioned_spec`: "`solveConditioned_spec` proves
that at positive evidence mass this conditioned driver, with any maximizing selector, returns a
policy realizing the reported conditional value, and that this value equals the likelihood
driver's value and the conditional optimum."

The preceding sentence of the documentation fixes the scope: hard evidence (`HardEvidence`) on
an action-free chance-ancestral set, every chance and utility factor sliced at the observed
states, and chance variables that no factor mentions skipped (`solveConditioned`).
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.DVEConditioning

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram InfluenceDiagramsProofs.DVE

/-- `solveConditioned_spec`, restated abstractly with every hypothesis. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j) (H : HardEvidence id),
    0 < evidenceMass κ defaultStrategy H.toEvidence →
      (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value).strategy.Deterministic ∧
      conditionalEU κ (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value).strategy
        u H.toEvidence =
        (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value).value ∧
      (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value).value =
        (solveEvidence κ hloc hnonneg u hu ord nf H.toEvidence).value ∧
      (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value).value =
        conditionalOptimalValue κ u H.toEvidence

/-- "returns a policy": a deterministic strategy, at positive mass, for any selector. -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j) (H : HardEvidence id),
    0 < evidenceMass κ defaultStrategy H.toEvidence →
      (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value).strategy.Deterministic

/-- "realizing the reported conditional value": its conditional expected utility under the
original model is the value it reports. -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j) (H : HardEvidence id),
    0 < evidenceMass κ defaultStrategy H.toEvidence →
      conditionalEU κ (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value).strategy
        u H.toEvidence =
        (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value).value

/-- "this value equals the likelihood driver's value". -/
abbrev Shadow3 : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j) (H : HardEvidence id),
    0 < evidenceMass κ defaultStrategy H.toEvidence →
      (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value).value =
        (solveEvidence κ hloc hnonneg u hu ord nf H.toEvidence).value

/-- "and the conditional optimum": `conditionalOptimalValue` is the independent global oracle. -/
abbrev Shadow4 : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j) (H : HardEvidence id),
    0 < evidenceMass κ defaultStrategy H.toEvidence →
      (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value).value =
        conditionalOptimalValue κ u H.toEvidence

theorem forward1 : Candidate → Shadow1 := fun h id sel κ hc ord nf hloc hnorm hnonneg u hu H hp =>
  (h id sel κ hc ord nf hloc hnorm hnonneg u hu H hp).1

theorem forward2 : Candidate → Shadow2 := fun h id sel κ hc ord nf hloc hnorm hnonneg u hu H hp =>
  (h id sel κ hc ord nf hloc hnorm hnonneg u hu H hp).2.1

theorem forward3 : Candidate → Shadow3 := fun h id sel κ hc ord nf hloc hnorm hnonneg u hu H hp =>
  (h id sel κ hc ord nf hloc hnorm hnonneg u hu H hp).2.2.1

theorem forward4 : Candidate → Shadow4 := fun h id sel κ hc ord nf hloc hnorm hnonneg u hu H hp =>
  (h id sel κ hc ord nf hloc hnorm hnonneg u hu H hp).2.2.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Candidate :=
  fun h1 h2 h3 h4 id sel κ hc ord nf hloc hnorm hnonneg u hu H hp =>
    ⟨h1 id sel κ hc ord nf hloc hnorm hnonneg u hu H hp,
      h2 id sel κ hc ord nf hloc hnorm hnonneg u hu H hp,
      h3 id sel κ hc ord nf hloc hnorm hnonneg u hu H hp,
      h4 id sel κ hc ord nf hloc hnorm hnonneg u hu H hp⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ sel κ hc ord nf hloc hnorm hnonneg u hu H hp =>
  InfluenceDiagramsProofs.DVE.solveConditioned_spec sel κ hc ord nf hloc hnorm hnonneg u hu H hp

end InfluenceDiagramsProofs.Shadows.DVEConditioning
