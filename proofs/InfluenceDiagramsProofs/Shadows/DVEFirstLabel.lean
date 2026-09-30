import InfluenceDiagramsProofs.Finite.DVE.Selector

/-!
# SA-Pass shadow module: the checked driver with any maximizing selector

Claim `id.dve-first-label`, from `DVE.solveGuardedWith_spec`: "`solveGuardedWith_spec` proves
that the checked exact driver with any maximizing selector, in particular the least-state
(first-label) selector, returns a policy realizing the reported value and attaining the existing
global optimum."
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.DVEFirstLabel

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram InfluenceDiagramsProofs.DVE

/-- `solveGuardedWith_spec`, restated abstractly with every hypothesis, for an arbitrary
maximizing selector. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j),
    ∃ sol : Solution id, solveGuardedWith sel κ hloc hnonneg u hu ord nf = some sol ∧
      sol.strategy.Deterministic ∧ expectedUtility κ sol.strategy u = sol.value ∧
      sol.value = optimalValue κ u

/-- "the checked exact driver with any maximizing selector ... returns a policy": the check
never fails, and what it returns is a deterministic strategy. -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j),
    ∃ sol : Solution id, solveGuardedWith sel κ hloc hnonneg u hu ord nf = some sol ∧
      sol.strategy.Deterministic

/-- "realizing the reported value". -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j) (sol : Solution id),
    solveGuardedWith sel κ hloc hnonneg u hu ord nf = some sol →
    expectedUtility κ sol.strategy u = sol.value

/-- "attaining the existing global optimum": `optimalValue` is defined independently of any
algorithm or selector. -/
abbrev Shadow3 : Prop :=
  ∀ (id : FinInfluenceDiagram) (sel : Selector id) (κ : id.Kernel ℝ) (_hclosed : id.Closed)
      (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
      (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
      (hu : ∀ j, Utility.Local u j) (sol : Solution id),
    solveGuardedWith sel κ hloc hnonneg u hu ord nf = some sol → sol.value = optimalValue κ u

/-- "in particular the least-state (first-label) selector": `Selector.ordered`, the least
maximizing state in a supplied linear order on every action space. -/
abbrev Shadow4 : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder) (nf : NoForgettingOrder id)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j),
    ∃ sol : Solution id,
      solveGuardedWith (Selector.ordered id) κ hloc hnonneg u hu ord nf = some sol ∧
      sol.strategy.Deterministic ∧ expectedUtility κ sol.strategy u = sol.value ∧
      sol.value = optimalValue κ u

theorem forward1 : Candidate → Shadow1 := by
  intro h id sel κ hc ord nf hloc hnorm hnonneg u hu
  obtain ⟨sol, hs, hd, _, _⟩ := h id sel κ hc ord nf hloc hnorm hnonneg u hu
  exact ⟨sol, hs, hd⟩

theorem forward2 : Candidate → Shadow2 := by
  intro h id sel κ hc ord nf hloc hnorm hnonneg u hu sol' hs'
  obtain ⟨sol, hs, _, he, _⟩ := h id sel κ hc ord nf hloc hnorm hnonneg u hu
  rw [hs] at hs'
  cases Option.some.inj hs'
  exact he

theorem forward3 : Candidate → Shadow3 := by
  intro h id sel κ hc ord nf hloc hnorm hnonneg u hu sol' hs'
  obtain ⟨sol, hs, _, _, hv⟩ := h id sel κ hc ord nf hloc hnorm hnonneg u hu
  rw [hs] at hs'
  cases Option.some.inj hs'
  exact hv

theorem forward4 : Candidate → Shadow4 := by
  intro h id _ κ hc ord nf hloc hnorm hnonneg u hu
  exact h id (Selector.ordered id) κ hc ord nf hloc hnorm hnonneg u hu

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Candidate := by
  intro h1 h2 h3 _ id sel κ hc ord nf hloc hnorm hnonneg u hu
  obtain ⟨sol, hs, hd⟩ := h1 id sel κ hc ord nf hloc hnorm hnonneg u hu
  exact ⟨sol, hs, hd, h2 id sel κ hc ord nf hloc hnorm hnonneg u hu sol hs,
    h3 id sel κ hc ord nf hloc hnorm hnonneg u hu sol hs⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ sel κ hc ord nf hloc hnorm hnonneg u hu =>
  InfluenceDiagramsProofs.DVE.solveGuardedWith_spec sel κ hc ord nf hloc hnorm hnonneg u hu

end InfluenceDiagramsProofs.Shadows.DVEFirstLabel
