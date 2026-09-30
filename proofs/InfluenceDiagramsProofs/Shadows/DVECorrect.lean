import InfluenceDiagramsProofs.Finite.DVE.Guard.Complete

/-!
# SA-Pass shadow module: the checked exact DVE driver is correct

Claim `id.dve-correct`, from `DVE.solveGuarded_spec`: "`solveGuarded_spec` proves that the
checked exact driver returns a policy realizing the reported value and attaining the existing
global optimum."
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.DVECorrect

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram InfluenceDiagramsProofs.DVE

/-- `solveGuarded_spec`, restated abstractly, with every hypothesis: a closed diagram with an
order and a no-forgetting decision order, local, normalised and nonnegative kernels, and local
utilities. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder)
      (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j),
    ∃ sol : Solution id, solveGuarded κ hloc hnonneg u hu ord nf = some sol ∧
      sol.strategy.Deterministic ∧ expectedUtility κ sol.strategy u = sol.value ∧
      sol.value = optimalValue κ u

/-- "the checked exact driver returns a policy": the check never fails on these inputs, and what
it returns is a deterministic strategy, a policy table per decision. -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder)
      (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j),
    ∃ sol : Solution id, solveGuarded κ hloc hnonneg u hu ord nf = some sol ∧
      sol.strategy.Deterministic

/-- "realizing the reported value": whatever the driver returns, its strategy's expected utility
is the value it reports. -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder)
      (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
      (sol : Solution id), solveGuarded κ hloc hnonneg u hu ord nf = some sol →
    expectedUtility κ sol.strategy u = sol.value

/-- "attaining the existing global optimum": the reported value is `optimalValue`, the optimum
over all strategies defined independently of the algorithm. -/
abbrev Shadow3 : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder)
      (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
      (sol : Solution id), solveGuarded κ hloc hnonneg u hu ord nf = some sol →
    sol.value = optimalValue κ u

theorem forward1 : Candidate → Shadow1 := by
  intro h id κ hc ord nf hloc hnorm hnonneg u hu
  obtain ⟨sol, hs, hd, _, _⟩ := h id κ hc ord nf hloc hnorm hnonneg u hu
  exact ⟨sol, hs, hd⟩

theorem forward2 : Candidate → Shadow2 := by
  intro h id κ hc ord nf hloc hnorm hnonneg u hu sol' hs'
  obtain ⟨sol, hs, _, he, _⟩ := h id κ hc ord nf hloc hnorm hnonneg u hu
  rw [hs] at hs'
  cases Option.some.inj hs'
  exact he

theorem forward3 : Candidate → Shadow3 := by
  intro h id κ hc ord nf hloc hnorm hnonneg u hu sol' hs'
  obtain ⟨sol, hs, _, _, hv⟩ := h id κ hc ord nf hloc hnorm hnonneg u hu
  rw [hs] at hs'
  cases Option.some.inj hs'
  exact hv

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := by
  intro h1 h2 h3 id κ hc ord nf hloc hnorm hnonneg u hu
  obtain ⟨sol, hs, hd⟩ := h1 id κ hc ord nf hloc hnorm hnonneg u hu
  exact ⟨sol, hs, hd, h2 id κ hc ord nf hloc hnorm hnonneg u hu sol hs,
    h3 id κ hc ord nf hloc hnorm hnonneg u hu sol hs⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated, so a restatement that
drifts from the proved theorem stops compiling. -/
theorem anchor : Candidate := fun _ κ hc ord nf hloc hnorm hnonneg u hu =>
  InfluenceDiagramsProofs.DVE.solveGuarded_spec κ hc ord nf hloc hnorm hnonneg u hu

end InfluenceDiagramsProofs.Shadows.DVECorrect
