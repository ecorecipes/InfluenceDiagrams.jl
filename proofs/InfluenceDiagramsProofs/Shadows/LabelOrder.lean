import InfluenceDiagramsProofs.Finite.DVE.LabelOrder

/-!
# SA-Pass shadow module: action labels in checked state-position order

Claim `id.label-order`, from `Records.Diagram.solveRepRecords_optimal` and
`Records.Diagram.solveRecords_table`:
"`solveRepRecords_optimal` proves that, for a diagram compiled from checked records, on every
row of positive probability the returned entry is the action of least `state_position` among the
maximizers of the optimal continuation value, for any plan and with any zero-row utility
representative, Julia's included, and `solveRecords_table` that on every row the model's entry
is the least-`state_position` maximizer of its bucket-utility score."

"Compiled from checked records" is `Records.Diagram.compile r h` with `h : r.Valid`; the
first-label selector is `r.selector h`; "the returned entry" is the `t` with
`kernel x a = if a = t then 1 else 0`; "`state_position`" is `statePosition`, the checked
`position` field of the state's record; "any zero-row utility representative" is any
`keep`; "positive probability" is positive `reach` under the run's own returned strategy.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.LabelOrder

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram InfluenceDiagramsProofs.DVE
open InfluenceDiagramsProofs.Records

/-- `solveRepRecords_optimal` and `solveRecords_table`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (r : Diagram) (h : r.Valid) (κ : (r.compile h).Kernel ℝ) (_hclosed : (r.compile h).Closed)
      (ord : (r.compile h).IDOrder) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility (r.compile h) ℝ)
      (hu : ∀ j, Utility.Local u j),
    (∀ (keep : (r.compile h).V → Bool) (plan : Plan (r.compile h) Finset.univ)
        (d : (r.compile h).D) (x : (r.compile h).Assignment) (ρ : Strategy (r.compile h) ℝ),
      reach κ (fun _ => 1) ρ d x ≠ 0 →
      ∃ t, (∀ a, ((solveRepPlanWith (r.selector h) keep κ hloc hnonneg u hu plan).strategy
            d).kernel x a = if a = t then 1 else 0) ∧
        (∀ b, optimalContinuation κ u (fun _ => 1) d x b ≤
          optimalContinuation κ u (fun _ => 1) d x t) ∧
        ∀ b, (∀ c, optimalContinuation κ u (fun _ => 1) d x c ≤
            optimalContinuation κ u (fun _ => 1) d x b) →
          r.statePosition h _ t ≤ r.statePosition h _ b) ∧
    (∀ (nf : NoForgettingOrder (r.compile h)) (d : (r.compile h).D)
        (x : (r.compile h).Assignment),
      ∃ t, (∀ a, ((solveWith (r.selector h) κ hloc hnonneg u hu ord nf).strategy d).kernel x a =
          if a = t then 1 else 0) ∧
        (∀ b, solveScore κ hloc hnonneg u hu ord nf d x b ≤
          solveScore κ hloc hnonneg u hu ord nf d x t) ∧
        ∀ b, (∀ c, solveScore κ hloc hnonneg u hu ord nf d x c ≤
            solveScore κ hloc hnonneg u hu ord nf d x b) →
          r.statePosition h _ t ≤ r.statePosition h _ b)

/-- "on every row of positive probability the returned entry is the action of least
`state_position` among the maximizers of the optimal continuation value, for any plan and with
any zero-row utility representative". -/
abbrev Shadow1 : Prop :=
  ∀ (r : Diagram) (h : r.Valid) (κ : (r.compile h).Kernel ℝ) (_hclosed : (r.compile h).Closed)
      (_ord : (r.compile h).IDOrder) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility (r.compile h) ℝ)
      (hu : ∀ j, Utility.Local u j) (keep : (r.compile h).V → Bool)
      (plan : Plan (r.compile h) Finset.univ) (d : (r.compile h).D)
      (x : (r.compile h).Assignment),
    0 < reach κ (fun _ => 1)
      (solveRepPlanWith (r.selector h) keep κ hloc hnonneg u hu plan).strategy d x →
    ∃ t, (∀ a, ((solveRepPlanWith (r.selector h) keep κ hloc hnonneg u hu plan).strategy
          d).kernel x a = if a = t then 1 else 0) ∧
      (∀ b, optimalContinuation κ u (fun _ => 1) d x b ≤
        optimalContinuation κ u (fun _ => 1) d x t) ∧
      ∀ b, (∀ c, optimalContinuation κ u (fun _ => 1) d x c ≤
          optimalContinuation κ u (fun _ => 1) d x b) →
        r.statePosition h _ t ≤ r.statePosition h _ b

/-- "on every row the model's entry is the least-`state_position` maximizer of its
bucket-utility score". -/
abbrev Shadow2 : Prop :=
  ∀ (r : Diagram) (h : r.Valid) (κ : (r.compile h).Kernel ℝ) (_hclosed : (r.compile h).Closed)
      (ord : (r.compile h).IDOrder) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility (r.compile h) ℝ)
      (hu : ∀ j, Utility.Local u j) (nf : NoForgettingOrder (r.compile h))
      (d : (r.compile h).D) (x : (r.compile h).Assignment),
    ∃ t, (∀ a, ((solveWith (r.selector h) κ hloc hnonneg u hu ord nf).strategy d).kernel x a =
        if a = t then 1 else 0) ∧
      (∀ b, solveScore κ hloc hnonneg u hu ord nf d x b ≤
        solveScore κ hloc hnonneg u hu ord nf d x t) ∧
      ∀ b, (∀ c, solveScore κ hloc hnonneg u hu ord nf d x c ≤
          solveScore κ hloc hnonneg u hu ord nf d x b) →
        r.statePosition h _ t ≤ r.statePosition h _ b

theorem forward1 : Candidate → Shadow1 := by
  intro hc r h κ hcl ord hloc hnorm hnonneg u hu keep plan d x hx
  exact (hc r h κ hcl ord hloc hnorm hnonneg u hu).1 keep plan d x _ (ne_of_gt hx)

theorem forward2 : Candidate → Shadow2 := by
  intro hc r h κ hcl ord hloc hnorm hnonneg u hu nf d x
  exact (hc r h κ hcl ord hloc hnorm hnonneg u hu).2 nf d x

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 r h κ hcl ord hloc hnorm hnonneg u hu
  refine ⟨fun keep plan d x ρ hx => ?_, fun nf d x =>
    h2 r h κ hcl ord hloc hnorm hnonneg u hu nf d x⟩
  let σ := (solveRepPlanWith (r.selector h) keep κ hloc hnonneg u hu plan).strategy
  have hσ : σ.Nonneg := deterministic_nonneg _ (runRepWith_deterministic _ _ _ _ _
    defaultStrategy_deterministic)
  have he : reach κ (fun _ => 1) ρ d x = reach κ (fun _ => 1) σ d x :=
    reach_strategy_independent (independent_one κ hcl ord hloc hnorm) hcl plan _
      (massAll_initial κ hloc hnonneg u hu) d (Finset.mem_univ _) ρ σ x
  rw [he] at hx
  exact h1 r h κ hcl ord hloc hnorm hnonneg u hu keep plan d x
    (lt_of_le_of_ne (reach_nonneg κ hnonneg _ (fun _ => zero_le_one) σ hσ d x) (Ne.symm hx))

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate := by
  intro r h κ hcl ord hloc hnorm hnonneg u hu
  exact ⟨fun keep plan d x ρ hx => Diagram.solveRepRecords_optimal r h keep κ hcl ord hloc hnorm
      hnonneg u hu plan d x ρ hx,
    fun nf d x => Diagram.solveRecords_table r h κ hcl hloc hnonneg u hu ord nf d x⟩

end InfluenceDiagramsProofs.Shadows.LabelOrder
