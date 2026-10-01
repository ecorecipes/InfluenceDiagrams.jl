import InfluenceDiagramsProofs.Finite.DVE.Representative

/-!
# SA-Pass shadow module: Julia's utility representative on zero-probability rows

Claim `id.zero-row-representative`, from `DVE.solveRepPlanWith_kernel_eq` and
`DVE.solveRepPlanOrdered_table`:
"`solveRepPlanWith_kernel_eq` proves that this representative cannot change a policy entry on a
row of positive probability, for any elimination plan and any selector, and
`solveRepPlanOrdered_table` proves that on every row, zero-probability rows included, the
first-label table is `orderedTable` of that run's own bucket-utility score."

"This representative" is `sumOutKeep keep` for an arbitrary `keep : id.V → Bool` (the README
says the theorems hold for every choice); "cannot change" compares with the model's driver
`solvePlanWith` on the same plan and selector; "positive probability" is positive `reach` under
the representative run's own returned strategy (the theorem accepts any strategy, since reach
is strategy independent, `reach_strategy_independent`).
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.ZeroRowRepresentative

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram InfluenceDiagramsProofs.DVE

/-- `solveRepPlanWith_kernel_eq` and `solveRepPlanOrdered_table`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (_ord : id.IDOrder)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (keep : id.V → Bool),
    (∀ (sel : Selector id) (plan : Plan id Finset.univ) (d : id.D) (x : id.Assignment)
        (ρ : Strategy id ℝ),
      reach κ (fun _ => 1) ρ d x ≠ 0 →
      ((solveRepPlanWith sel keep κ hloc hnonneg u hu plan).strategy d).kernel x =
        ((solvePlanWith sel κ hloc hnonneg u hu plan).strategy d).kernel x) ∧
    (∀ (plan : Plan id Finset.univ) (d : id.D) (x : id.Assignment)
        (a : id.states (id.action d)),
      ((solveRepPlanWith (Selector.ordered id) keep κ hloc hnonneg u hu plan).strategy d).kernel
          x a =
        if a = orderedTable (solveRepPlanScore keep κ hloc hnonneg u hu plan d)
          (infoAssignment d x) then 1 else 0)

/-- "this representative cannot change a policy entry on a row of positive probability, for
any elimination plan and any selector". -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (_ord : id.IDOrder)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (keep : id.V → Bool)
      (sel : Selector id) (plan : Plan id Finset.univ) (d : id.D) (x : id.Assignment),
    0 < reach κ (fun _ => 1) (solveRepPlanWith sel keep κ hloc hnonneg u hu plan).strategy d x →
    ((solveRepPlanWith sel keep κ hloc hnonneg u hu plan).strategy d).kernel x =
      ((solvePlanWith sel κ hloc hnonneg u hu plan).strategy d).kernel x

/-- "on every row, zero-probability rows included, the first-label table is `orderedTable` of
that run's own bucket-utility score". -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (_ord : id.IDOrder)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (keep : id.V → Bool)
      (plan : Plan id Finset.univ) (d : id.D) (x : id.Assignment),
    ((solveRepPlanWith (Selector.ordered id) keep κ hloc hnonneg u hu plan).strategy d).kernel x =
      fun a => if a = orderedTable (solveRepPlanScore keep κ hloc hnonneg u hu plan d)
        (infoAssignment d x) then 1 else 0

theorem forward1 : Candidate → Shadow1 := by
  intro h id _ κ hc ord hloc hnorm hnonneg u hu keep sel plan d x hx
  exact (h id κ hc ord hloc hnorm hnonneg u hu keep).1 sel plan d x _ (ne_of_gt hx)

theorem forward2 : Candidate → Shadow2 := by
  intro h id _ κ hc ord hloc hnorm hnonneg u hu keep plan d x
  funext a
  exact (h id κ hc ord hloc hnorm hnonneg u hu keep).2 plan d x a

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 id _ κ hc ord hloc hnorm hnonneg u hu keep
  refine ⟨fun sel plan d x ρ hx => ?_, fun plan d x a =>
    congrFun (h2 id κ hc ord hloc hnorm hnonneg u hu keep plan d x) a⟩
  let σ := (solveRepPlanWith sel keep κ hloc hnonneg u hu plan).strategy
  have hσ : σ.Nonneg := deterministic_nonneg _ (runRepWith_deterministic _ _ _ _ _
    defaultStrategy_deterministic)
  have he : reach κ (fun _ => 1) ρ d x = reach κ (fun _ => 1) σ d x :=
    reach_strategy_independent (independent_one κ hc ord hloc hnorm) hc plan _
      (massAll_initial κ hloc hnonneg u hu) d (Finset.mem_univ _) ρ σ x
  rw [he] at hx
  exact h1 id κ hc ord hloc hnorm hnonneg u hu keep sel plan d x
    (lt_of_le_of_ne (reach_nonneg κ hnonneg _ (fun _ => zero_le_one) σ hσ d x) (Ne.symm hx))

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate := by
  intro id _ κ hc ord hloc hnorm hnonneg u hu keep
  exact ⟨fun sel plan d x ρ hx => InfluenceDiagramsProofs.DVE.solveRepPlanWith_kernel_eq sel keep
      κ hc ord hloc hnorm hnonneg u hu plan d x ρ hx,
    fun plan d x a => InfluenceDiagramsProofs.DVE.solveRepPlanOrdered_table keep κ hc hloc
      hnonneg u hu plan d x a⟩

end InfluenceDiagramsProofs.Shadows.ZeroRowRepresentative
