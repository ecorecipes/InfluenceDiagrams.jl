import InfluenceDiagramsProofs.Finite.DVE.Guard.Provenance

/-!
# Exact all-row diagnostic completeness

For t>0, Laplace smoothing makes every chance row strictly positive while preserving locality
and normalization. Adding t to the action-free likelihood makes its factors positive too.
The positive-case theorem therefore proves every exact guard along each smoothed run.

The probability-expression trace is fixed by the scopes and plan. Its finite products, sums
and maximum values are continuous at t=0. Every guard equality consequently holds at t=0,
including contexts where the outside probability is zero. No strict-positivity assumption
survives in the public theorems, and no cancellation by zero is performed.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation
open Guard

noncomputable section

variable {id : FinInfluenceDiagram}

def smoothKernel (κ : id.Kernel ℝ) (t : ℝ) : id.Kernel ℝ :=
  fun m x a => (κ m x a + t) / (1 + (Fintype.card (id.states (id.target m)) : ℝ) * t)

theorem smoothing_denominator_pos (m : id.M) (t : ℝ) (ht : 0 ≤ t) :
    0 < 1 + (Fintype.card (id.states (id.target m)) : ℝ) * t :=
  add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (Nat.cast_nonneg _) ht)

theorem smoothKernel_zero (κ : id.Kernel ℝ) : smoothKernel κ 0 = κ := by
  funext m x a
  simp [smoothKernel]

theorem smoothKernel_local (κ : id.Kernel ℝ) (hκ : ∀ m, Local κ m) (t : ℝ) :
    ∀ m, Local (smoothKernel κ t) m := by
  intro m x y h
  funext a
  simp only [smoothKernel, hκ m x y h]

theorem smoothKernel_normalised (κ : id.Kernel ℝ) (hκ : ∀ m, Normalised κ m)
    (t : ℝ) (ht : 0 ≤ t) : ∀ m, Normalised (smoothKernel κ t) m := by
  intro m x
  change (∑ a, (κ m x a + t) / (1 + (Fintype.card (id.states (id.target m)) : ℝ) * t)) = 1
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, hκ m x]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (ne_of_gt (smoothing_denominator_pos m t ht))

theorem smoothKernel_positive (κ : id.Kernel ℝ) (hκ : ∀ m x a, 0 ≤ κ m x a)
    (t : ℝ) (ht : 0 < t) : ∀ m x a, 0 < smoothKernel κ t m x a := by
  intro m x a
  exact div_pos (add_pos_of_nonneg_of_pos (hκ m x a) ht) (smoothing_denominator_pos m t ht.le)

theorem smoothKernel_continuousAt_zero (κ : id.Kernel ℝ) (m : id.M)
    (x : id.Assignment) (a : id.states (id.target m)) :
    ContinuousAt (fun t => smoothKernel κ t m x a) 0 := by
  exact (continuousAt_const.add continuousAt_id).div
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) (by simp)

def smoothEvidence (e : Evidence id) (t : ℝ) (ht : 0 ≤ t) : Evidence id where
  ancestors := e.ancestors
  closed := e.closed
  no_action := e.no_action
  likelihood x := e.likelihood x + t
  localOn x y h := by
    dsimp only
    rw [e.localOn x y h]
  nonneg x := add_nonneg (e.nonneg x) ht

/-- Every probability diagnostic in an actual no-evidence run holds on every row.
Only nonnegativity, not strict positivity, is assumed. The plan is structural. -/
theorem all_guards_complete (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) :
    AllGuards plan (initial κ hloc hnonneg u hu).valuations := by
  apply (represents_guards_iff plan (initial_represents κ hloc hnonneg u hu (fun _ => 1))).2
  intro p hp x a
  have ht : ∀ t : ℝ, 0 < t →
      p.2.eval (smoothKernel κ t) (fun _ => 1) (Function.update x p.1 a) =
        p.2.eval (smoothKernel κ t) (fun _ => 1) x := by
    intro t ht
    let K := smoothKernel κ t
    have hl : ∀ m, Local K m := smoothKernel_local κ hloc t
    have hn : ∀ m, Normalised K m := smoothKernel_normalised κ hnorm t ht.le
    have hpos : ∀ m x a, 0 < K m x a := smoothKernel_positive κ hnonneg t ht
    have hnn : ∀ m x a, 0 ≤ K m x a := fun m x a => (hpos m x a).le
    have hguards := guards_of_positive hclosed ord hl hn plan (initial K hl hnn u hu)
      defaultStrategy (initial_correct K hl hnn u hu _) (initial_positive K hl hnn u hu hpos)
    exact (represents_guards_iff plan (initial_represents K hl hnn u hu (fun _ => 1))).1
      hguards p hp x a
  have hx := p.2.continuousAt (smoothKernel κ) (fun _ _ => 1)
    (smoothKernel_continuousAt_zero κ) (fun _ => continuousAt_const) x
  have ha := p.2.continuousAt (smoothKernel κ) (fun _ _ => 1)
    (smoothKernel_continuousAt_zero κ) (fun _ => continuousAt_const) (Function.update x p.1 a)
  have hzero := eq_at_zero_of_positive _ _ ha hx ht
  simpa only [smoothKernel_zero] using hzero

/-- All-row completeness also holds for supported evidence, even if the entire evidence event
has zero mass. The later evidence-mass check is a different diagnostic. -/
theorem all_guards_complete_evidence (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) (plan : Plan id Finset.univ) :
    AllGuards plan (initialEvidence κ hloc hnonneg u hu e).valuations := by
  apply (represents_guards_iff plan (initialEvidence_represents κ hloc hnonneg u hu e)).2
  intro p hp x a
  have ht : ∀ t : ℝ, 0 < t →
      p.2.eval (smoothKernel κ t) (fun y => e.likelihood y + t) (Function.update x p.1 a) =
        p.2.eval (smoothKernel κ t) (fun y => e.likelihood y + t) x := by
    intro t ht
    let K := smoothKernel κ t
    let et := smoothEvidence e t ht.le
    have hl : ∀ m, Local K m := smoothKernel_local κ hloc t
    have hn : ∀ m, Normalised K m := smoothKernel_normalised κ hnorm t ht.le
    have hpos : ∀ m x a, 0 < K m x a := smoothKernel_positive κ hnonneg t ht
    have hnn : ∀ m x a, 0 ≤ K m x a := fun m x a => (hpos m x a).le
    have hepos : ∀ x, 0 < et.likelihood x := fun x =>
      add_pos_of_nonneg_of_pos (e.nonneg x) ht
    have hguards := guards_of_positive_weighted hclosed ord hl hn plan
      (initialEvidence K hl hnn u hu et) defaultStrategy (initialEvidence_correct K hl hnn u hu et _)
      (initialEvidence_positive K hl hnn u hu et hpos hepos)
    exact (represents_guards_iff plan (initialEvidence_represents K hl hnn u hu et)).1
      hguards p hp x a
  have hL : ∀ y, ContinuousAt (fun t : ℝ => e.likelihood y + t) 0 :=
    fun _ => continuousAt_const.add continuousAt_id
  have hx := p.2.continuousAt (smoothKernel κ) (fun t y => e.likelihood y + t)
    (smoothKernel_continuousAt_zero κ) hL x
  have ha := p.2.continuousAt (smoothKernel κ) (fun t y => e.likelihood y + t)
    (smoothKernel_continuousAt_zero κ) hL (Function.update x p.1 a)
  have hzero := eq_at_zero_of_positive _ _ ha hx ht
  simpa only [smoothKernel_zero, add_zero] using hzero

/-- The exact checked driver cannot reject a valid generated no-forgetting run. -/
theorem checkedRun_generated_eq (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) :
    checkedRun (nf.plan ord.no_self_info) (initial κ hloc hnonneg u hu) defaultStrategy =
      some (run (nf.plan ord.no_self_info) (initial κ hloc hnonneg u hu) defaultStrategy) :=
  checkedRun_eq_run _ _ _ (all_guards_complete κ hclosed ord hloc hnorm hnonneg u hu _)

theorem checkedRun_generated_evidence_eq (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) :
    checkedRun (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e) defaultStrategy =
      some (run (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e) defaultStrategy) :=
  checkedRun_eq_run _ _ _ (all_guards_complete_evidence κ hclosed ord hloc hnorm hnonneg u hu e _)

def solveGuarded (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) : Option (Solution id) :=
  (checkedRun (nf.plan ord.no_self_info) (initial κ hloc hnonneg u hu) defaultStrategy).map
    (fun result => ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩)

theorem solveGuarded_eq (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) :
    solveGuarded κ hloc hnonneg u hu ord nf = some (solve κ hloc hnonneg u hu ord nf) := by
  unfold solveGuarded
  rw [checkedRun_generated_eq κ hclosed ord nf hloc hnorm hnonneg u hu]
  rfl

def solveEvidenceGuarded (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (e : Evidence id) : Option (Solution id) :=
  (checkedRun (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e) defaultStrategy).bind
    (fun result => if 0 < (collect result.1.valuations).prob (baseAssignment id) then
      some ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩ else none)

/-- The guarded evidence solver has exactly the same result as the already-verified
evidence-mass-checked solver: no extra failure is introduced at unreachable rows. -/
theorem solveEvidenceGuarded_eq (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) :
    solveEvidenceGuarded κ hloc hnonneg u hu ord nf e =
      solveEvidenceChecked κ hloc hnonneg u hu ord nf e := by
  unfold solveEvidenceGuarded
  rw [checkedRun_generated_evidence_eq κ hclosed ord nf hloc hnorm hnonneg u hu e]
  rfl

/-- The exact checked solver returns the same realized deterministic optimum; its diagnostic
introduces no additional hypothesis or failure on any valid no-evidence diagram. -/
theorem solveGuarded_spec (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) :
    ∃ sol : Solution id, solveGuarded κ hloc hnonneg u hu ord nf = some sol ∧
      sol.strategy.Deterministic ∧ expectedUtility κ sol.strategy u = sol.value ∧
      sol.value = optimalValue κ u :=
  ⟨solve κ hloc hnonneg u hu ord nf, solveGuarded_eq κ hclosed ord nf hloc hnorm hnonneg u hu,
    solve_spec κ hclosed ord nf hloc hnorm hnonneg u hu⟩

/-- For supported evidence, the only possible rejection is zero evidence mass, not the
exact probability diagnostic, even when many individual information rows are unreachable. -/
theorem solveEvidenceGuarded_none_iff (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) :
    solveEvidenceGuarded κ hloc hnonneg u hu ord nf e = none ↔
      evidenceMass κ defaultStrategy e = 0 := by
  rw [solveEvidenceGuarded_eq κ hclosed ord nf hloc hnorm hnonneg u hu e]
  exact solveEvidenceChecked_none_iff κ hclosed ord nf hloc hnorm hnonneg u hu e

end
end InfluenceDiagramsProofs.DVE
