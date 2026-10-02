import InfluenceDiagramsProofs.Finite.DVE.PlanIndependence

/-!
# Julia's utility representative on zero-probability rows

The model's chance step `Valuation.sumOut` stores the utility `ratio (Σ φψ) (Σ φ)`, which is
`0` wherever the summed probability `Σ φ` is zero. Julia's `sum_out`
(`InfluenceDiagrams.jl/src/valuation.jl`) does that only when the summed variable is in the
scope of the utility potential `ψ`; otherwise it keeps `ψ′ = ψ` unchanged, also on rows where
`Σ φ` is zero. Julia's valuations carry a utility scope that the model's do not, so this module
parameterises the chance step by a Boolean `keep` per summed variable:

* `Valuation.sumOutKeep false` is the model's `sumOut` (`sumOutKeep_false`);
* `Valuation.sumOutKeep true` stores the bucket utility itself on the rows where `Σ φ = 0`, and
  is literally Julia's `ψ′ = ψ` whenever the bucket utility does not depend on the summed
  variable (`sumOutKeep_util_of_const`), which is what Julia's branch condition `x ∉ ψ.vars`
  guarantees.

A plan eliminates every chance variable at most once, so any sequence of Julia branch decisions
along a run is one function `keep : id.V → Bool`; every result below holds for **every** `keep`.
Which `keep` Julia's run uses (`a ∉ ψ.vars` at the step that sums `a`) is read off the source,
not derived.

`runRepWith sel keep` is the bucket driver of `runWith` with this chance step. The results:

* **Agreement where it matters.** `Agrees` (same scope, same probability potential, same
  weighted utility `φψ`) is preserved by every chance step (`agrees_chanceStep`) and, given the
  exact bucket guard, every decision step (`agrees_decisionStep`). The guard holds on every
  row (`all_guards_complete`), so the model's and Julia's runs agree valuation by valuation on
  any plan (`runRep_agrees`). Hence the probability potentials and masses are identical, the
  utilities differ only where the probability is zero, and the value is the same.
* **Realized optimality.** `solveRepPlanWith_spec`: for every selector, every `keep` and every
  plan, the returned deterministic strategy realizes the reported value, which is the global
  optimum.
* **Positive-reach tables.** `solveRepPlanScore_eq` / `solveRepPlanWith_kernel_eq`: on every
  row of positive reach the decision scores, hence the policy entries of any selector, equal the
  model's. So Julia's representative cannot change a returned table entry on a reachable row;
  with `Selector.ordered` the entry is the least maximizer of `optimalContinuation`
  (`solveRepPlanOrdered_optimal`).
* **Every row.** `solveRepPlanOrdered_table`: the ordered solver's policy is exactly
  `orderedTable` of its own score `solveRepPlanScore` on every information row, reachable or
  not. On zero-reach rows that score may differ from the model's; the table is still a
  function of the score, so it is determined by the data and the elimination plan.

Evidence: these theorems cover the no-evidence driver on any plan. Julia's hard-evidence path
(sliced factors, absent variables skipped: `runSkipWith`) combined with this representative is
not modelled here; `Finite/DVE/NearOptimalEvidence.lean` combines them (`runRepSkipWith`).
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

/-! ## Julia's sum-out -/

namespace Valuation

variable {bn : FinBayesNet}

theorem ext' {v w : Valuation bn} (hs : v.scope = w.scope) (hp : v.prob = w.prob)
    (hu : v.util = w.util) : v = w := by
  cases v
  cases w
  cases hs
  cases hp
  cases hu
  rfl

/-- Sum-elimination with the utility representative chosen by `keep`. Where the summed
probability is positive the stored utility is the model's ratio. Where it is zero, `keep = false`
stores `0` (the model) and `keep = true` stores the bucket utility read at a fixed state of
`a` (Julia's `ψ′ = ψ` when `ψ` does not mention `a`). -/
def sumOutKeep (keep : Bool) (a : bn.V) (v : Valuation bn) : Valuation bn where
  scope := v.scope.erase a
  prob := (sumOut a v).prob
  util x := if keep = true ∧ (sumOut a v).prob x = 0 then
      v.util (Function.update x a (Classical.choice (bn.nonemptyS a)))
    else (sumOut a v).util x
  prob_local := (sumOut a v).prob_local
  util_local x y h := by
    have hp : (sumOut a v).prob x = (sumOut a v).prob y := (sumOut a v).prob_local x y h
    have hu : v.util (Function.update x a (Classical.choice (bn.nonemptyS a))) =
        v.util (Function.update y a (Classical.choice (bn.nonemptyS a))) :=
      v.util_local _ _ (update_agree h _)
    have hr : (sumOut a v).util x = (sumOut a v).util y := (sumOut a v).util_local x y h
    simp only [hp, hu, hr]
  nonneg := (sumOut a v).nonneg

/-- The model is the `keep = false` instance. -/
theorem sumOutKeep_false (a : bn.V) (v : Valuation bn) : sumOutKeep false a v = sumOut a v :=
  ext' rfl rfl (funext fun x => by simp [sumOutKeep])

/-- **Julia's branch.** If the bucket utility does not depend on the summed variable, the
`keep = true` representative is that utility on every row, zero-probability rows included:
Julia's `ψ′ = v.ψ`. -/
theorem sumOutKeep_util_of_const (a : bn.V) (v : Valuation bn)
    (hc : ∀ x b, v.util (Function.update x a b) = v.util x) (x : bn.Assignment) :
    (sumOutKeep true a v).util x = v.util x := by
  change (if true = true ∧ (sumOut a v).prob x = 0 then
      v.util (Function.update x a (Classical.choice (bn.nonemptyS a)))
    else (sumOut a v).util x) = v.util x
  by_cases hz : (sumOut a v).prob x = 0
  · rw [if_pos ⟨rfl, hz⟩, hc]
  · rw [if_neg (fun h => hz h.2)]
    change ratio (∑ b, v.weight (Function.update x a b))
      (∑ b, v.prob (Function.update x a b)) = v.util x
    have hz' : ∑ b, v.prob (Function.update x a b) ≠ 0 := hz
    have hs : ∑ b, v.weight (Function.update x a b) =
        (∑ b, v.prob (Function.update x a b)) * v.util x := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by rw [weight, hc]
    rw [ratio, if_neg hz', hs, mul_div_cancel_left₀ _ hz']

/-- The weighted utility of either representative is the summed weighted utility, on every
row. -/
theorem sumOutKeep_weight (keep : Bool) (a : bn.V) (v : Valuation bn) (x : bn.Assignment) :
    (sumOutKeep keep a v).weight x = ∑ b, v.weight (Function.update x a b) := by
  rw [← sumOut_weight]
  change (sumOut a v).prob x * (if keep = true ∧ (sumOut a v).prob x = 0 then
      v.util (Function.update x a (Classical.choice (bn.nonemptyS a)))
    else (sumOut a v).util x) = (sumOut a v).prob x * (sumOut a v).util x
  split_ifs with h
  · rw [h.2, zero_mul, zero_mul]
  · rfl

def chanceStepKeep (keep : Bool) (a : bn.V) (vs : List (Valuation bn)) : List (Valuation bn) :=
  sumOutKeep keep a (collect (bucket a vs)) :: outside a vs

/-! ## Agreement of probabilities and weighted utilities -/

/-- Two valuations with the same scope, probability potential and weighted utility. Their
utilities agree wherever the probability is nonzero (`Agrees.util_eq`). -/
def Agrees (v w : Valuation bn) : Prop :=
  v.scope = w.scope ∧ v.prob = w.prob ∧ v.weight = w.weight

theorem Agrees.refl (v : Valuation bn) : Agrees v v := ⟨rfl, rfl, rfl⟩

theorem Agrees.util_eq {v w : Valuation bn} (h : Agrees v w) {x : bn.Assignment}
    (hx : v.prob x ≠ 0) : v.util x = w.util x := by
  have hw := congrFun h.2.2 x
  have hp := congrFun h.2.1 x
  unfold weight at hw
  rw [← hp] at hw
  exact mul_left_cancel₀ hx hw

theorem agrees_refl_list (vs : List (Valuation bn)) : List.Forall₂ Agrees vs vs :=
  List.forall₂_same.2 fun v _ => Agrees.refl v

theorem agrees_filter {vs ws : List (Valuation bn)} (h : List.Forall₂ Agrees vs ws)
    (p : Finset bn.V → Bool) :
    List.Forall₂ Agrees (vs.filter fun v => p v.scope) (ws.filter fun w => p w.scope) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons v w vs ws hvw _ ih =>
    rw [List.filter_cons, List.filter_cons, hvw.1]
    split
    · exact List.Forall₂.cons hvw ih
    · exact ih

theorem agrees_bucket {vs ws : List (Valuation bn)} (h : List.Forall₂ Agrees vs ws) (a : bn.V) :
    List.Forall₂ Agrees (bucket a vs) (bucket a ws) :=
  agrees_filter h fun S => decide (a ∈ S)

theorem agrees_outside {vs ws : List (Valuation bn)} (h : List.Forall₂ Agrees vs ws) (a : bn.V) :
    List.Forall₂ Agrees (outside a vs) (outside a ws) :=
  agrees_filter h fun S => decide (a ∉ S)

theorem agrees_collect {vs ws : List (Valuation bn)} (h : List.Forall₂ Agrees vs ws) :
    Agrees (collect vs) (collect ws) := by
  induction h with
  | nil => exact Agrees.refl _
  | @cons v w vs ws hvw _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · change v.scope ∪ (collect vs).scope = w.scope ∪ (collect ws).scope
      rw [hvw.1, ih.1]
    · funext x
      change v.prob x * (collect vs).prob x = w.prob x * (collect ws).prob x
      rw [congrFun hvw.2.1 x, congrFun ih.2.1 x]
    · funext x
      have e1 := congrFun hvw.2.2 x
      have e2 := congrFun ih.2.2 x
      have p1 := congrFun hvw.2.1 x
      have p2 := congrFun ih.2.1 x
      unfold weight at e1 e2
      change (v.prob x * (collect vs).prob x) * (v.util x + (collect vs).util x) =
        (w.prob x * (collect ws).prob x) * (w.util x + (collect ws).util x)
      calc
        _ = (collect vs).prob x * (v.prob x * v.util x) +
            v.prob x * ((collect vs).prob x * (collect vs).util x) := by ring
        _ = (collect ws).prob x * (w.prob x * w.util x) +
            w.prob x * ((collect ws).prob x * (collect ws).util x) := by rw [e1, e2, p1, p2]
        _ = _ := by ring

/-- The model's sum-out and either representative agree. -/
theorem agrees_sumOut {v w : Valuation bn} (h : Agrees v w) (keep : Bool) (a : bn.V) :
    Agrees (sumOut a v) (sumOutKeep keep a w) := by
  refine ⟨?_, ?_, ?_⟩
  · change v.scope.erase a = w.scope.erase a
    rw [h.1]
  · funext x
    change ∑ b, v.prob (Function.update x a b) = ∑ b, w.prob (Function.update x a b)
    rw [h.2.1]
  · funext x
    rw [sumOut_weight, sumOutKeep_weight, h.2.2]

theorem agrees_maxOut {v w : Valuation bn} (h : Agrees v w) (a : bn.V)
    (hc : ∀ x b, v.prob (Function.update x a b) = v.prob x) :
    Agrees (maxOut a v) (maxOut a w) := by
  have hpc : ∀ x, probabilityChoice a v x = probabilityChoice a w x := by
    intro x
    unfold probabilityChoice
    rw [h.2.1]
  refine ⟨?_, ?_, ?_⟩
  · change v.scope.erase a = w.scope.erase a
    rw [h.1]
  · funext x
    change v.prob (Function.update x a (probabilityChoice a v x)) =
      w.prob (Function.update x a (probabilityChoice a w x))
    rw [hpc, h.2.1]
  · funext x
    change v.prob (Function.update x a (probabilityChoice a v x)) *
        v.util (Function.update x a (choice a v x)) =
      w.prob (Function.update x a (probabilityChoice a w x)) *
        w.util (Function.update x a (choice a w x))
    rw [← hpc, ← h.2.1, hc]
    by_cases hz : v.prob x = 0
    · rw [hz, zero_mul, zero_mul]
    · have hu : ∀ b, v.util (Function.update x a b) = w.util (Function.update x a b) :=
        fun b => h.util_eq (by rw [hc]; exact hz)
      have hch : choice a v x = choice a w x := by
        unfold choice
        congr 1
        funext b
        exact hu b
      rw [hch, hu]

theorem agrees_chanceStep {vs ws : List (Valuation bn)} (h : List.Forall₂ Agrees vs ws)
    (keep : Bool) (a : bn.V) :
    List.Forall₂ Agrees (chanceStep a vs) (chanceStepKeep keep a ws) :=
  List.Forall₂.cons (agrees_sumOut (agrees_collect (agrees_bucket h a)) keep a)
    (agrees_outside h a)

/-- A decision step preserves agreement when the bucket probability does not depend on the
action on any row: the exact all-row guard. -/
theorem agrees_decisionStep {vs ws : List (Valuation bn)} (h : List.Forall₂ Agrees vs ws)
    (a : bn.V)
    (hc : ∀ x b, (collect (bucket a vs)).prob (Function.update x a b) =
      (collect (bucket a vs)).prob x) :
    List.Forall₂ Agrees (decisionStep a vs) (decisionStep a ws) :=
  List.Forall₂.cons (agrees_maxOut (agrees_collect (agrees_bucket h a)) a hc)
    (agrees_outside h a)

/-- The two chance steps have the same probability potential and weighted utility. -/
theorem chanceStepKeep_collect (keep : Bool) (a : bn.V) (vs : List (Valuation bn)) :
    (collect (chanceStepKeep keep a vs)).prob = (collect (chanceStep a vs)).prob ∧
      (collect (chanceStepKeep keep a vs)).weight = (collect (chanceStep a vs)).weight := by
  have h := agrees_collect (agrees_chanceStep (agrees_refl_list vs) keep a)
  exact ⟨h.2.1.symm, h.2.2.symm⟩

end Valuation

variable {id : FinInfluenceDiagram}

/-! ## The driver with Julia's chance step -/

def State.chanceKeep {R : Finset id.V} (keep : id.V → Bool) (v : id.V) (s : State id R) :
    State id (R.erase v) where
  valuations := chanceStepKeep (keep v) v s.valuations
  supported := (step_scope v s.valuations (sumOutKeep (keep v) v) (fun _ => rfl)).trans
    (Finset.erase_subset_erase v s.supported)

/-- The bucket driver of `runWith` with the chance step `sumOutKeep (keep v)`. -/
def runRepWith (sel : Selector id) (keep : id.V → Bool) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) : State id ∅ × Strategy id ℝ :=
  match plan with
  | .done => (s, σ)
  | .chance v _ _ next => runRepWith sel keep next (s.chanceKeep keep v) σ
  | .decision d _ hi next =>
    runRepWith sel keep next (s.decision d) (Function.update σ d (s.policyWith sel d hi))

/-- The valuations of `runRepWith`; no selector or strategy enters them. -/
def runRepState (keep : id.V → Bool) {R : Finset id.V} (plan : Plan id R) (s : State id R) :
    State id ∅ :=
  match plan with
  | .done => s
  | .chance v _ _ next => runRepState keep next (s.chanceKeep keep v)
  | .decision d _ _ next => runRepState keep next (s.decision d)

theorem runRepWith_state (sel : Selector id) (keep : id.V → Bool) {R : Finset id.V}
    (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ) :
    (runRepWith sel keep plan s σ).1 = runRepState keep plan s := by
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih => exact ih (s.chanceKeep keep v) σ
  | decision d _ hi next ih =>
    exact ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))

theorem State.chanceKeep_false {R : Finset id.V} (v : id.V) (s : State id R) :
    s.chanceKeep (fun _ => false) v = s.chance v := by
  cases s with
  | mk vs hs =>
    simp only [State.chanceKeep, State.chance, chanceStepKeep, chanceStep, sumOutKeep_false]

/-- With `keep = false` everywhere the driver is the model's `runWith`. -/
theorem runRepWith_false (sel : Selector id) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) :
    runRepWith sel (fun _ => false) plan s σ = runWith sel plan s σ := by
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih =>
    show runRepWith sel _ next (s.chanceKeep _ v) σ = runWith sel next (s.chance v) σ
    rw [State.chanceKeep_false]
    exact ih (s.chance v) σ
  | decision d _ hi next ih =>
    exact ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))

theorem runRepWith_snd_of_notMem (sel : Selector id) (keep : id.V → Bool) {R : Finset id.V}
    (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ) (e : id.D)
    (he : id.action e ∉ R) : (runRepWith sel keep plan s σ).2 e = σ e := by
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih =>
    exact ih (s.chanceKeep keep v) σ (fun h => he (Finset.mem_of_mem_erase h))
  | decision d hd hi next ih =>
    refine (ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))
      (fun h => he (Finset.mem_of_mem_erase h))).trans ?_
    exact Function.update_of_ne (fun h : e = d => he (by rw [h]; exact hd)) _ _

theorem runRepWith_policy_at_step (sel : Selector id) (keep : id.V → Bool) {R : Finset id.V}
    (d : id.D) (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d)
    (next : Plan id (R.erase (id.action d))) (s : State id R) (σ : Strategy id ℝ) :
    (runRepWith sel keep (.decision d hd hi next) s σ).2 d = s.policyWith sel d hi := by
  refine (runRepWith_snd_of_notMem sel keep next (s.decision d)
    (Function.update σ d (s.policyWith sel d hi)) d (Finset.notMem_erase _ _)).trans ?_
  exact Function.update_self _ _ _

theorem runRepWith_deterministic (sel : Selector id) (keep : id.V → Bool) {R : Finset id.V}
    (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ) (hσ : σ.Deterministic) :
    (runRepWith sel keep plan s σ).2.Deterministic := by
  induction plan generalizing σ with
  | done => exact hσ
  | chance v _ _ next ih => exact ih (s.chanceKeep keep v) σ hσ
  | decision d _ hi next ih =>
    apply ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))
    intro e
    by_cases h : e = d
    · subst e
      simp only [Function.update_self]
      exact ⟨_, fun x y h => congrArg (sel.pick d) (bucketScore_local s d hi x y h), rfl⟩
    · rw [Function.update_of_ne h]
      exact hσ e

/-! ## The invariant survives Julia's chance step -/

theorem Inv.chanceKeep {κ : id.Kernel ℝ} {u : Utility id ℝ} {L : id.Assignment → ℝ}
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ} (h : Inv κ u L s σ)
    (keep : id.V → Bool) (v : id.V) (hv : v ∈ R) (hc : ∀ d, id.action d ≠ v) :
    Inv κ u L (s.chanceKeep keep v) σ := by
  have hm := h.chance v hv hc
  obtain ⟨hp, hw⟩ := chanceStepKeep_collect (keep v) v s.valuations
  refine ⟨fun x => ?_, fun x => ?_, fun τ hτ x => ?_⟩
  · change (collect (chanceStepKeep (keep v) v s.valuations)).prob x = _
    rw [hp]
    exact hm.mass x
  · change (collect (chanceStepKeep (keep v) v s.valuations)).weight x = _
    rw [hw]
    exact hm.realizes x
  · change _ ≤ (collect (chanceStepKeep (keep v) v s.valuations)).weight x
    rw [hw]
    exact hm.dominates τ hτ x

theorem runRepWith_inv (sel : Selector id) (keep : id.V → Bool) {κ : id.Kernel ℝ}
    {u : Utility id ℝ} {L : id.Assignment → ℝ} (hind : Independent κ L) (hclosed : id.Closed)
    {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ)
    (h : Inv κ u L s σ) :
    Inv κ u L (runRepWith sel keep plan s σ).1 (runRepWith sel keep plan s σ).2 := by
  induction plan generalizing σ with
  | done => exact h
  | chance v hv hc next ih => exact ih (s.chanceKeep keep v) σ (h.chanceKeep keep v hv hc)
  | decision d hd hi next ih =>
    exact ih (s.decision d) _ (h.decisionWith hind hclosed sel d hd hi)

/-! ## Scores and tables -/

/-- The bucket-utility score of `d` when `runRepWith` eliminates its action. -/
def decisionScoreRep (keep : id.V → Bool) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (d : id.D) : id.Assignment → id.states (id.action d) → ℝ :=
  match plan with
  | .done => fun _ _ => 0
  | .chance v _ _ next => decisionScoreRep keep next (s.chanceKeep keep v) d
  | .decision d' _ _ next =>
    if d' = d then bucketScore s.valuations (id.action d)
    else decisionScoreRep keep next (s.decision d') d

theorem decisionScoreRep_local (keep : id.V → Bool) (hinj : Function.Injective id.action)
    {R : Finset id.V} (plan : Plan id R) (s : State id R) (d : id.D) (hd : id.action d ∈ R) :
    LocalOn (id.info d) (decisionScoreRep keep plan s d) := by
  induction plan with
  | done => simp at hd
  | chance v _ hc next ih =>
    exact ih (s.chanceKeep keep v) (Finset.mem_erase.2 ⟨hc d, hd⟩)
  | decision d' hd' hi next ih =>
    by_cases hdd : d' = d
    · subst hdd
      intro x y h
      show (if d' = d' then bucketScore s.valuations (id.action d')
          else decisionScoreRep keep next (s.decision d') d') x =
        (if d' = d' then bucketScore s.valuations (id.action d')
          else decisionScoreRep keep next (s.decision d') d') y
      rw [if_pos rfl]
      exact bucketScore_local s d' hi x y h
    · intro x y h
      show (if d' = d then bucketScore s.valuations (id.action d)
          else decisionScoreRep keep next (s.decision d') d) x =
        (if d' = d then bucketScore s.valuations (id.action d)
          else decisionScoreRep keep next (s.decision d') d) y
      rw [if_neg hdd]
      exact ih (s.decision d') (Finset.mem_erase.2 ⟨fun he => hdd (hinj he).symm, hd⟩) x y h

/-- Every returned policy row is the selector's choice on the recorded score. -/
theorem runRepWith_kernel (sel : Selector id) (keep : id.V → Bool)
    (hinj : Function.Injective id.action) {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (σ : Strategy id ℝ) (d : id.D) (hd : id.action d ∈ R) (x : id.Assignment)
    (a : id.states (id.action d)) :
    ((runRepWith sel keep plan s σ).2 d).kernel x a =
      if a = sel.pick d (decisionScoreRep keep plan s d x) then 1 else 0 := by
  induction plan generalizing σ with
  | done => simp at hd
  | chance v _ hc next ih =>
    exact ih (s.chanceKeep keep v) σ (Finset.mem_erase.2 ⟨hc d, hd⟩)
  | decision d' hd' hi next ih =>
    by_cases hdd : d' = d
    · subst hdd
      rw [runRepWith_policy_at_step]
      show (if a = sel.pick d' (bucketScore s.valuations (id.action d') x) then (1 : ℝ) else 0) =
        if a = sel.pick d' ((if d' = d' then bucketScore s.valuations (id.action d')
          else decisionScoreRep keep next (s.decision d') d') x) then 1 else 0
      rw [if_pos rfl]
    · have hne : id.action d ≠ id.action d' := fun he => hdd (hinj he).symm
      refine (ih (s.decision d') (Function.update σ d' (s.policyWith sel d' hi))
        (Finset.mem_erase.2 ⟨hne, hd⟩)).trans ?_
      show (if a = sel.pick d (decisionScoreRep keep next (s.decision d') d x) then (1 : ℝ)
          else 0) =
        if a = sel.pick d ((if d' = d then bucketScore s.valuations (id.action d)
          else decisionScoreRep keep next (s.decision d') d) x) then 1 else 0
      rw [if_neg hdd]

/-! ## The coupled runs -/

/-- **The model's and Julia's runs agree valuation by valuation** on any plan, given the exact
bucket guards of the model's run (which always hold, `all_guards_complete`). -/
theorem runRep_agrees (keep : id.V → Bool) {R : Finset id.V} (plan : Plan id R)
    (s s' : State id R) (h : List.Forall₂ Agrees s.valuations s'.valuations)
    (hg : AllGuards plan s.valuations) :
    List.Forall₂ Agrees (runState plan s).valuations (runRepState keep plan s').valuations := by
  induction plan with
  | done => exact h
  | chance v _ _ next ih =>
    exact ih (s.chance v) (s'.chanceKeep keep v) (agrees_chanceStep h (keep v) v) hg
  | decision d _ _ next ih =>
    exact ih (s.decision d) (s'.decision d) (agrees_decisionStep h (id.action d) hg.1) hg.2

/-- On a row of positive probability the bucket scores of agreeing states coincide. -/
theorem bucketScore_agree {R : Finset id.V} {s s' : State id R}
    (h : List.Forall₂ Agrees s.valuations s'.valuations) (a : id.V) (x : id.Assignment)
    (hp : ∀ b, (collect s.valuations).prob (Function.update x a b) =
      (collect s.valuations).prob x)
    (hx : (collect s.valuations).prob x ≠ 0) :
    bucketScore s'.valuations a x = bucketScore s.valuations a x := by
  funext b
  have hb := agrees_collect (agrees_bucket h a)
  have hpos : (collect (bucket a s.valuations)).prob (Function.update x a b) ≠ 0 := by
    intro h0
    apply hx
    rw [← hp b, (collect_partition a s.valuations _).1, h0, zero_mul]
  exact (hb.util_eq hpos).symm

/-- **Positive-reach scores agree.** At every row of positive reach the decision score of
Julia's run equals the model's. -/
theorem decisionScoreRep_eq (keep : id.V → Bool) {κ : id.Kernel ℝ} {L : id.Assignment → ℝ}
    (hind : Independent κ L) (hclosed : id.Closed) {R : Finset id.V} (plan : Plan id R)
    (s s' : State id R) (h : List.Forall₂ Agrees s.valuations s'.valuations)
    (hg : AllGuards plan s.valuations) (hs : MassAll κ L s) (d : id.D) (hd : id.action d ∈ R)
    (x : id.Assignment) (ρ : Strategy id ℝ) (hx : reach κ L ρ d x ≠ 0) :
    decisionScoreRep keep plan s' d x = decisionScore plan s d x := by
  have hinj := (id.closed_iff.1 hclosed).2.1
  induction plan with
  | done => simp at hd
  | chance v hv hc next ih =>
    exact ih (s.chance v) (s'.chanceKeep keep v) (agrees_chanceStep h (keep v) v) hg
      (hs.chance v hv hc) (Finset.mem_erase.2 ⟨hc d, hd⟩)
  | @decision R' d' hd' hi next ih =>
    by_cases hdd : d' = d
    · subst hdd
      have hR : insert (id.action d') (id.info d') = R' := by
        rw [← hi, Finset.insert_erase hd']
      have hprob : (collect s.valuations).prob x = reach κ L ρ d' x := by
        unfold reach
        rw [hR, hs ρ]
      show (if d' = d' then bucketScore s'.valuations (id.action d')
          else decisionScoreRep keep next (s'.decision d') d') x =
        (if d' = d' then bucketScore s.valuations (id.action d')
          else decisionScore next (s.decision d') d') x
      rw [if_pos rfl, if_pos rfl]
      exact bucketScore_agree h (id.action d') x (hs.prob_update hind d' hd' hi x)
        (fun h0 => hx (hprob.symm.trans h0))
    · have hne : id.action d ≠ id.action d' := fun he => hdd (hinj he).symm
      show (if d' = d then bucketScore s'.valuations (id.action d)
          else decisionScoreRep keep next (s'.decision d') d) x =
        (if d' = d then bucketScore s.valuations (id.action d)
          else decisionScore next (s.decision d') d) x
      rw [if_neg hdd, if_neg hdd]
      exact ih (s.decision d') (s'.decision d') (agrees_decisionStep h (id.action d') hg.1) hg.2
        (hs.decision hind hclosed d' hd' hi) (Finset.mem_erase.2 ⟨hne, hd⟩)

/-! ## Solvers on an arbitrary plan -/

/-- The solver with Julia's chance step, on any plan (for example Julia's min-fill schedule). -/
def solveRepPlanWith (sel : Selector id) (keep : id.V → Bool) (κ : id.Kernel ℝ)
    (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (plan : Plan id Finset.univ) : Solution id :=
  let result := runRepWith sel keep plan (initial κ hloc hnonneg u hu) defaultStrategy
  ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩

/-- The score row that `solveRepPlanWith` maximizes for `d`. -/
def solveRepPlanScore (keep : id.V → Bool) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) (d : id.D) : id.Assignment → id.states (id.action d) → ℝ :=
  decisionScoreRep keep plan (initial κ hloc hnonneg u hu) d

/-- The model's score row for `d` on the same plan. -/
def solvePlanScore (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (plan : Plan id Finset.univ) (d : id.D) :
    id.Assignment → id.states (id.action d) → ℝ :=
  decisionScore plan (initial κ hloc hnonneg u hu) d

theorem solveRepPlanWith_false (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) :
    solveRepPlanWith sel (fun _ => false) κ hloc hnonneg u hu plan =
      solvePlanWith sel κ hloc hnonneg u hu plan := by
  unfold solveRepPlanWith solvePlanWith
  rw [runRepWith_false]

/-- **Julia's representative: the final valuations agree with the model's.** On any plan,
valuation by valuation: equal scopes, equal probability potentials and equal weighted
utilities. -/
theorem solveRepPlan_agrees (keep : id.V → Bool) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) :
    List.Forall₂ Agrees (runState plan (initial κ hloc hnonneg u hu)).valuations
      (runRepState keep plan (initial κ hloc hnonneg u hu)).valuations :=
  runRep_agrees keep plan _ _ (agrees_refl_list _)
    (all_guards_complete κ hclosed ord hloc hnorm hnonneg u hu plan)

/-- **Julia's representative is still exact.** For every selector, every `keep` and every
plan, the returned deterministic strategy realizes the reported value, which is the global
optimum, and the value equals the model's. -/
theorem solveRepPlanWith_spec (sel : Selector id) (keep : id.V → Bool) (κ : id.Kernel ℝ)
    (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (plan : Plan id Finset.univ) :
    let sol := solveRepPlanWith sel keep κ hloc hnonneg u hu plan
    sol.strategy.Deterministic ∧ expectedUtility κ sol.strategy u = sol.value ∧
      sol.value = optimalValue κ u := by
  intro sol
  let result := runRepWith sel keep plan (initial κ hloc hnonneg u hu) (defaultStrategy (id := id))
  have hc : Inv κ u (fun _ => 1) result.1 result.2 :=
    runRepWith_inv sel keep (independent_one κ hclosed ord hloc hnorm) hclosed _ _ _
      (Inv.ofCorrect (initial_correct κ hloc hnonneg u hu _))
  have hp : (collect result.1.valuations).prob (baseAssignment id) = 1 := by
    rw [hc.mass, Finset.compl_empty, freeJoint_univ, marg_univ]
    simpa only [mul_one] using sum_joint_instantiate_eq_one κ result.2 hclosed ord hloc hnorm
  have hr : expectedUtility κ result.2 u =
      (collect result.1.valuations).util (baseAssignment id) := by
    have h := hc.realizes (baseAssignment id)
    rw [weight, hp, one_mul, Finset.compl_empty, freeJoint_univ, marg_univ] at h
    simp only [one_mul] at h
    exact h.symm
  have hd : result.2.Deterministic :=
    runRepWith_deterministic sel keep _ _ _ defaultStrategy_deterministic
  have ho : ∀ σ : Strategy id ℝ, σ.Nonneg →
      expectedUtility κ σ u ≤ (collect result.1.valuations).util (baseAssignment id) := by
    intro σ hσ
    have h := hc.dominates σ hσ (baseAssignment id)
    rw [weight, hp, one_mul, Finset.compl_empty, freeJoint_univ, marg_univ] at h
    simpa only [one_mul] using h
  change result.2.Deterministic ∧ expectedUtility κ result.2 u =
    (collect result.1.valuations).util (baseAssignment id) ∧
      (collect result.1.valuations).util (baseAssignment id) = optimalValue κ u
  refine ⟨hd, hr, le_antisymm ?_ ?_⟩
  · rw [← hr]
    exact expectedUtility_le_optimalValue κ u result.2 (deterministic_nonneg _ hd)
  · obtain ⟨σ, _, hσ, hvalue⟩ := optimalValue_attained κ u
    rw [← hvalue]
    exact ho σ hσ

/-- The value of Julia's representative run is the model's value on the same plan. -/
theorem solveRepPlanWith_value (sel : Selector id) (keep : id.V → Bool) (κ : id.Kernel ℝ)
    (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (plan : Plan id Finset.univ) :
    (solveRepPlanWith sel keep κ hloc hnonneg u hu plan).value =
      (solvePlanWith sel κ hloc hnonneg u hu plan).value := by
  rw [(solveRepPlanWith_spec sel keep κ hclosed ord hloc hnorm hnonneg u hu plan).2.2,
    ← solveRepPlanWith_false sel κ hloc hnonneg u hu plan,
    (solveRepPlanWith_spec sel (fun _ => false) κ hclosed ord hloc hnorm hnonneg u hu plan).2.2]

/-- **Positive-reach scores of Julia's representative are the model's.** -/
theorem solveRepPlanScore_eq (keep : id.V → Bool) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) (d : id.D) (x : id.Assignment) (ρ : Strategy id ℝ)
    (hx : reach κ (fun _ => 1) ρ d x ≠ 0) :
    solveRepPlanScore keep κ hloc hnonneg u hu plan d x =
      solvePlanScore κ hloc hnonneg u hu plan d x :=
  decisionScoreRep_eq keep (independent_one κ hclosed ord hloc hnorm) hclosed plan _ _
    (agrees_refl_list _) (all_guards_complete κ hclosed ord hloc hnorm hnonneg u hu plan)
    (massAll_initial κ hloc hnonneg u hu) d (Finset.mem_univ _) x ρ hx

/-- **Julia's representative cannot change a reachable table entry.** For every selector, every
`keep` and every plan, on every row of positive reach (under any strategy), the returned policy
entry equals the model's on the same plan. -/
theorem solveRepPlanWith_kernel_eq (sel : Selector id) (keep : id.V → Bool) (κ : id.Kernel ℝ)
    (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (plan : Plan id Finset.univ) (d : id.D) (x : id.Assignment)
    (ρ : Strategy id ℝ) (hx : reach κ (fun _ => 1) ρ d x ≠ 0) :
    ((solveRepPlanWith sel keep κ hloc hnonneg u hu plan).strategy d).kernel x =
      ((solvePlanWith sel κ hloc hnonneg u hu plan).strategy d).kernel x := by
  have hinj := (id.closed_iff.1 hclosed).2.1
  funext a
  have h1 := runRepWith_kernel sel keep hinj plan (initial κ hloc hnonneg u hu) defaultStrategy d
    (Finset.mem_univ _) x a
  have h2 := runWith_kernel sel hinj plan (initial κ hloc hnonneg u hu) defaultStrategy d
    (Finset.mem_univ _) x a
  change ((runRepWith sel keep plan _ defaultStrategy).2 d).kernel x a =
    ((runWith sel plan _ defaultStrategy).2 d).kernel x a
  rw [h1, h2]
  have he := solveRepPlanScore_eq keep κ hclosed ord hloc hnorm hnonneg u hu plan d x ρ hx
  unfold solveRepPlanScore solvePlanScore at he
  rw [he]

section Ordered

variable [∀ d : id.D, LinearOrder (id.states (id.action d))]

/-- **First-label table identity for Julia's representative, on every row.** Reachable or
not, the ordered solver's policy is `orderedTable` of its own bucket-utility score, a finite
table over exactly the information variables. -/
theorem solveRepPlanOrdered_table (keep : id.V → Bool) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (plan : Plan id Finset.univ) (d : id.D) (x : id.Assignment)
    (a : id.states (id.action d)) :
    ((solveRepPlanWith (Selector.ordered id) keep κ hloc hnonneg u hu plan).strategy d).kernel
        x a =
      if a = orderedTable (solveRepPlanScore keep κ hloc hnonneg u hu plan d)
        (infoAssignment d x) then 1 else 0 := by
  have hinj := (id.closed_iff.1 hclosed).2.1
  unfold solveRepPlanScore
  rw [orderedTable_reconstruct _ (decisionScoreRep_local keep hinj plan _ d (Finset.mem_univ _))]
  exact runRepWith_kernel _ keep hinj _ _ _ d (Finset.mem_univ _) x a

/-- On a row of positive reach the ordered entry of Julia's representative is the least
maximizer of the plan- and representative-independent optimal continuation value. -/
theorem solveRepPlanOrdered_optimal (keep : id.V → Bool) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) (d : id.D) (x : id.Assignment) (ρ : Strategy id ℝ)
    (hx : reach κ (fun _ => 1) ρ d x ≠ 0) (a : id.states (id.action d)) :
    ((solveRepPlanWith (Selector.ordered id) keep κ hloc hnonneg u hu plan).strategy d).kernel
        x a =
      if a = firstArgmax (optimalContinuation κ u (fun _ => 1) d x) then 1 else 0 := by
  rw [solveRepPlanWith_kernel_eq _ keep κ hclosed ord hloc hnorm hnonneg u hu plan d x ρ hx]
  exact solvePlanOrdered_optimal κ hclosed ord hloc hnorm hnonneg u hu plan d x ρ hx a

end Ordered

end
end InfluenceDiagramsProofs.DVE
