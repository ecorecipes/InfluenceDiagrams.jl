import InfluenceDiagramsProofs.Finite.DVE.Conditioning

/-!
# SA-Pass shadow module: conditioned and likelihood first-label tables agree on reachable rows

Claim `id.conditioned-policy`, from `DVE.solveConditioned_policy_eq`: "With the least-state
selector, `solveConditioned_policy_eq` proves that its policy at a row equals the likelihood
driver's policy at the evidence-clamped row whenever that row has positive probability."

"Its policy" is the conditioned driver's (`solveConditioned`), "the likelihood driver" is
`solveEvidenceWith` on the indicator likelihood of the same hard evidence, the evidence-clamped
row is `clamp O o x`, and its probability is `reach` under the likelihood driver's strategy.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.ConditionedPolicy

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram InfluenceDiagramsProofs.DVE

/-- `solveConditioned_policy_eq`, restated abstractly with every hypothesis. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder) (nf : NoForgettingOrder id)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (H : HardEvidence id) (d : id.D)
      (x : id.Assignment),
    reach κ H.toEvidence.likelihood
        (solveEvidenceWith (Selector.ordered id) κ hloc hnonneg u hu ord nf H.toEvidence).strategy
        d (clamp H.observed H.value x) ≠ 0 →
      ((solveConditioned (Selector.ordered id) κ hloc hnonneg u hu ord nf H.observed
          H.value).strategy d).kernel x =
        ((solveEvidenceWith (Selector.ordered id) κ hloc hnonneg u hu ord nf
          H.toEvidence).strategy d).kernel (clamp H.observed H.value x)

/-- "its policy at a row equals the likelihood driver's policy at the evidence-clamped row
whenever that row has positive probability". -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder) (nf : NoForgettingOrder id)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (H : HardEvidence id) (d : id.D)
      (x : id.Assignment),
    0 < reach κ H.toEvidence.likelihood
        (solveEvidenceWith (Selector.ordered id) κ hloc hnonneg u hu ord nf H.toEvidence).strategy
        d (clamp H.observed H.value x) →
      ((solveConditioned (Selector.ordered id) κ hloc hnonneg u hu ord nf H.observed
          H.value).strategy d).kernel x =
        ((solveEvidenceWith (Selector.ordered id) κ hloc hnonneg u hu ord nf
          H.toEvidence).strategy d).kernel (clamp H.observed H.value x)

theorem forward1 : Candidate → Shadow1 := by
  intro h id _ κ hc ord nf hloc hnorm hnonneg u hu H d x hx
  exact h id κ hc ord nf hloc hnorm hnonneg u hu H d x (ne_of_gt hx)

theorem backward : Shadow1 → Candidate := by
  intro h1 id _ κ hc ord nf hloc hnorm hnonneg u hu H d x hx
  have hσ : (solveEvidenceWith (Selector.ordered id) κ hloc hnonneg u hu ord nf
      H.toEvidence).strategy.Nonneg :=
    deterministic_nonneg _ (runWith_deterministic (Selector.ordered id)
      (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu H.toEvidence)
      defaultStrategy defaultStrategy_deterministic)
  exact h1 id κ hc ord nf hloc hnorm hnonneg u hu H d x (lt_of_le_of_ne
    (reach_nonneg κ hnonneg _ H.toEvidence.nonneg _ hσ d _) (Ne.symm hx))

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := by
  intro id _ κ hc ord nf hloc hnorm hnonneg u hu H d x hx
  exact InfluenceDiagramsProofs.DVE.solveConditioned_policy_eq κ hc ord nf hloc hnorm hnonneg u
    hu H d x hx

end InfluenceDiagramsProofs.Shadows.ConditionedPolicy
