import InfluenceDiagramsProofs.Finite.DVE.PlanIndependence

/-!
# SA-Pass shadow module: first-label tables do not depend on the elimination plan

Claim `id.plan-independence`, from `DVE.solvePlanOrdered_table_eq` and
`DVE.solveConditionedPlan_table_eq`:
"`solvePlanOrdered_table_eq` proves that these first-label tables do not depend on the
elimination plan: any two plans, for example two min-fill orders of the chance variables inside
the strong blocks, give the same policy entry on every row of positive probability, and
`solveConditionedPlan_table_eq` proves the same for the conditioned driver on every row whose
evidence-clamped row has positive probability."

"Any two plans" is any two `Plan id Finset.univ`; "positive probability" is positive `reach`
under the first plan's own returned strategy (the theorems accept any strategy, since reach is
strategy independent, `reach_strategy_independent`).
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.PlanIndependence

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram InfluenceDiagramsProofs.DVE

/-- `solvePlanOrdered_table_eq` and `solveConditionedPlan_table_eq`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (_ord : id.IDOrder)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j),
    (∀ (plan₁ plan₂ : Plan id Finset.univ) (d : id.D) (x : id.Assignment) (ρ : Strategy id ℝ),
      reach κ (fun _ => 1) ρ d x ≠ 0 →
      ((solvePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan₁).strategy d).kernel x =
        ((solvePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan₂).strategy d).kernel x) ∧
    (∀ (H : HardEvidence id) (plan₁ plan₂ : Plan id Finset.univ) (d : id.D) (x : id.Assignment)
        (ρ : Strategy id ℝ),
      reach κ H.toEvidence.likelihood ρ d (clamp H.observed H.value x) ≠ 0 →
      ((solveConditionedPlan (Selector.ordered id) κ hloc hnonneg u hu plan₁ H.observed
          H.value).strategy d).kernel x =
        ((solveConditionedPlan (Selector.ordered id) κ hloc hnonneg u hu plan₂ H.observed
          H.value).strategy d).kernel x)

/-- "any two plans … give the same policy entry on every row of positive probability". -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (_ord : id.IDOrder)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
      (plan₁ plan₂ : Plan id Finset.univ) (d : id.D) (x : id.Assignment),
    0 < reach κ (fun _ => 1)
      (solvePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan₁).strategy d x →
    ((solvePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan₁).strategy d).kernel x =
      ((solvePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan₂).strategy d).kernel x

/-- "the same for the conditioned driver on every row whose evidence-clamped row has positive
probability". -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (_ord : id.IDOrder)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (H : HardEvidence id)
      (plan₁ plan₂ : Plan id Finset.univ) (d : id.D) (x : id.Assignment),
    0 < reach κ H.toEvidence.likelihood
      (solveConditionedPlan (Selector.ordered id) κ hloc hnonneg u hu plan₁ H.observed
        H.value).strategy d (clamp H.observed H.value x) →
    ((solveConditionedPlan (Selector.ordered id) κ hloc hnonneg u hu plan₁ H.observed
        H.value).strategy d).kernel x =
      ((solveConditionedPlan (Selector.ordered id) κ hloc hnonneg u hu plan₂ H.observed
        H.value).strategy d).kernel x

theorem forward1 : Candidate → Shadow1 := by
  intro h id _ κ hc ord hloc hnorm hnonneg u hu plan₁ plan₂ d x hx
  exact (h id κ hc ord hloc hnorm hnonneg u hu).1 plan₁ plan₂ d x _ (ne_of_gt hx)

theorem forward2 : Candidate → Shadow2 := by
  intro h id _ κ hc ord hloc hnorm hnonneg u hu H plan₁ plan₂ d x hx
  exact (h id κ hc ord hloc hnorm hnonneg u hu).2 H plan₁ plan₂ d x _ (ne_of_gt hx)

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 id _ κ hc ord hloc hnorm hnonneg u hu
  refine ⟨fun plan₁ plan₂ d x ρ hx => ?_, fun H plan₁ plan₂ d x ρ hx => ?_⟩
  · let σ := (solvePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan₁).strategy
    have hσ : σ.Nonneg := deterministic_nonneg _ (runWith_deterministic _ _ _ _
      defaultStrategy_deterministic)
    have he : reach κ (fun _ => 1) ρ d x = reach κ (fun _ => 1) σ d x :=
      reach_strategy_independent (independent_one κ hc ord hloc hnorm) hc plan₁ _
        (massAll_initial κ hloc hnonneg u hu) d (Finset.mem_univ _) ρ σ x
    rw [he] at hx
    exact h1 id κ hc ord hloc hnorm hnonneg u hu plan₁ plan₂ d x
      (lt_of_le_of_ne (reach_nonneg κ hnonneg _ (fun _ => zero_le_one) σ hσ d x) (Ne.symm hx))
  · let σ := (solveConditionedPlan (Selector.ordered id) κ hloc hnonneg u hu plan₁ H.observed
      H.value).strategy
    have hσ : σ.Nonneg := deterministic_nonneg _ (runSkipWith_deterministic _ _ _ _
      defaultStrategy_deterministic)
    have he : reach κ H.toEvidence.likelihood ρ d (clamp H.observed H.value x) =
        reach κ H.toEvidence.likelihood σ d (clamp H.observed H.value x) :=
      reach_strategy_independent (independent_evidence H.toEvidence κ hc ord hloc hnorm) hc
        plan₁ _ (massAll_initialEvidence κ hloc hnonneg u hu H.toEvidence) d
        (Finset.mem_univ _) ρ σ _
    rw [he] at hx
    exact h2 id κ hc ord hloc hnorm hnonneg u hu H plan₁ plan₂ d x
      (lt_of_le_of_ne (reach_nonneg κ hnonneg _ H.toEvidence.nonneg σ hσ d _) (Ne.symm hx))

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate := by
  intro id _ κ hc ord hloc hnorm hnonneg u hu
  exact ⟨fun plan₁ plan₂ d x ρ hx => InfluenceDiagramsProofs.DVE.solvePlanOrdered_table_eq κ hc
      ord hloc hnorm hnonneg u hu plan₁ plan₂ d x ρ hx,
    fun H plan₁ plan₂ d x ρ hx => InfluenceDiagramsProofs.DVE.solveConditionedPlan_table_eq κ hc
      ord hloc hnorm hnonneg u hu H plan₁ plan₂ d x ρ hx⟩

end InfluenceDiagramsProofs.Shadows.PlanIndependence
