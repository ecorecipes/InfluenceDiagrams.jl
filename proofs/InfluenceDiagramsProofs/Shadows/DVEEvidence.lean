import InfluenceDiagramsProofs.Finite.DVE.Guard.Complete

/-!
# SA-Pass shadow module: the guarded DVE driver under evidence

Claim `id.dve-evidence`, from `DVE.solveEvidenceGuarded_eq`, `DVE.solveEvidenceChecked_eq`,
`DVE.solveEvidence_spec` and `DVE.solveEvidenceGuarded_none_iff`: "The guarded solver returns a
conditional optimum at positive mass and rejects exactly zero mass."

The evidence is an `Evidence id`: a nonnegative likelihood local to an action-free,
chance-ancestrally closed set, the scope the preceding sentence of the documentation states.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.DVEEvidence

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram InfluenceDiagramsProofs.DVE

/-- The guarded evidence solver's specification, restated abstractly with every hypothesis:
at positive evidence mass it returns a deterministic strategy whose conditional expected utility
is the reported value and which no nonnegative strategy beats; it returns `none` exactly when
the evidence mass is zero. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder)
      (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
      (e : Evidence id),
    (0 < evidenceMass κ defaultStrategy e →
      ∃ sol : Solution id, solveEvidenceGuarded κ hloc hnonneg u hu ord nf e = some sol ∧
        sol.strategy.Deterministic ∧ conditionalEU κ sol.strategy u e = sol.value ∧
        ∀ σ : Strategy id ℝ, σ.Nonneg → conditionalEU κ σ u e ≤ sol.value) ∧
    (solveEvidenceGuarded κ hloc hnonneg u hu ord nf e = none ↔
      evidenceMass κ defaultStrategy e = 0)

/-- "returns a conditional optimum at positive mass": at positive mass the solver returns a
policy (a deterministic strategy) that no nonnegative strategy beats in conditional expected
utility. -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder)
      (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
      (e : Evidence id), 0 < evidenceMass κ defaultStrategy e →
    ∃ sol : Solution id, solveEvidenceGuarded κ hloc hnonneg u hu ord nf e = some sol ∧
      sol.strategy.Deterministic ∧
      ∀ σ : Strategy id ℝ, σ.Nonneg → conditionalEU κ σ u e ≤ conditionalEU κ sol.strategy u e

/-- The optimum it returns is the value it reports: the returned strategy's conditional
expected utility. -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder)
      (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
      (e : Evidence id) (sol : Solution id),
    solveEvidenceGuarded κ hloc hnonneg u hu ord nf e = some sol →
    conditionalEU κ sol.strategy u e = sol.value

/-- "rejects exactly zero mass": the solver fails if and only if the evidence has mass zero, so
it never rejects positive-mass evidence and never answers zero-mass evidence. -/
abbrev Shadow3 : Prop :=
  ∀ (id : FinInfluenceDiagram) (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder)
      (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m)
      (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
      (e : Evidence id),
    (evidenceMass κ defaultStrategy e = 0 →
      solveEvidenceGuarded κ hloc hnonneg u hu ord nf e = none) ∧
    (solveEvidenceGuarded κ hloc hnonneg u hu ord nf e = none →
      evidenceMass κ defaultStrategy e = 0)

theorem forward1 : Candidate → Shadow1 := by
  intro h id κ hc ord nf hloc hnorm hnonneg u hu e hp
  obtain ⟨sol, hs, hd, he, hopt⟩ := (h id κ hc ord nf hloc hnorm hnonneg u hu e).1 hp
  exact ⟨sol, hs, hd, fun σ hσ => he ▸ hopt σ hσ⟩

theorem forward2 : Candidate → Shadow2 := by
  intro h id κ hc ord nf hloc hnorm hnonneg u hu e sol' hs'
  have hne : solveEvidenceGuarded κ hloc hnonneg u hu ord nf e ≠ none := by
    rw [hs']; exact Option.some_ne_none _
  have hpos : 0 < evidenceMass κ defaultStrategy e := by
    rcases (evidenceMass_nonneg e κ hnonneg _
      (deterministic_nonneg _ defaultStrategy_deterministic)).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd ((h id κ hc ord nf hloc hnorm hnonneg u hu e).2.2 heq.symm) hne
  obtain ⟨sol, hs, _, he, _⟩ := (h id κ hc ord nf hloc hnorm hnonneg u hu e).1 hpos
  rw [hs] at hs'
  cases Option.some.inj hs'
  exact he

theorem forward3 : Candidate → Shadow3 := by
  intro h id κ hc ord nf hloc hnorm hnonneg u hu e
  exact ⟨(h id κ hc ord nf hloc hnorm hnonneg u hu e).2.2,
    (h id κ hc ord nf hloc hnorm hnonneg u hu e).2.1⟩

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := by
  intro h1 h2 h3 id κ hc ord nf hloc hnorm hnonneg u hu e
  refine ⟨fun hp => ?_, ⟨(h3 id κ hc ord nf hloc hnorm hnonneg u hu e).2,
    (h3 id κ hc ord nf hloc hnorm hnonneg u hu e).1⟩⟩
  obtain ⟨sol, hs, hd, hopt⟩ := h1 id κ hc ord nf hloc hnorm hnonneg u hu e hp
  have he := h2 id κ hc ord nf hloc hnorm hnonneg u hu e sol hs
  exact ⟨sol, hs, hd, he, fun σ hσ => he ▸ hopt σ hσ⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated, so a restatement that
drifts from the proved theorems stops compiling. -/
theorem anchor : Candidate := by
  intro _ κ hc ord nf hloc hnorm hnonneg u hu e
  refine ⟨fun hp => ?_,
    InfluenceDiagramsProofs.DVE.solveEvidenceGuarded_none_iff κ hc ord nf hloc hnorm hnonneg u hu e⟩
  rw [InfluenceDiagramsProofs.DVE.solveEvidenceGuarded_eq κ hc ord nf hloc hnorm hnonneg u hu e,
    InfluenceDiagramsProofs.DVE.solveEvidenceChecked_eq κ hc ord nf hloc hnorm hnonneg u hu e,
    if_pos hp]
  exact ⟨_, rfl,
    InfluenceDiagramsProofs.DVE.solveEvidence_spec κ hc ord nf hloc hnorm hnonneg u hu e hp⟩

end InfluenceDiagramsProofs.Shadows.DVEEvidence
