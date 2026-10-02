import InfluenceDiagramsProofs.Finite.DVE.NearOptimal

/-!
# Julia's evidence run: sliced valuations, skipped variables and the `sum_out` representative

`Finite/DVE/Conditioning.lean` models Julia's evidence path (every chance and utility valuation
sliced at the observed states, absent chance variables skipped) with the model's chance step,
and `Finite/DVE/Representative.lean` models Julia's `sum_out` representative without evidence.
Julia's run does both, on any elimination plan. This module combines them:

* `State.chanceRepSkip keep v` skips `v` when no valuation mentions it, and otherwise is the
  representative step `chanceKeep keep v`; `runRepSkipWith sel keep` is the bucket driver with
  that step, `decisionScoreRepSkip` its score rows, `runRepSkipWith_kernel` its tables;
* `solveCondRepPlanWith sel keep κ … O o plan` runs it from `initialConditioned` (the valuations
  sliced at `clamp O o`), the model of Julia's `_decision_elimination` with hard evidence;
* `ScopeOK`: observed variables are in no scope, every remaining unobserved chance variable is,
  so exactly the observed chance variables are skipped.

**Results.** For hard evidence `ev` (`HardEvidence`: observations on an action-free
chance-ancestral set) the tolerant invariant `TolInv` of `Finite/DVE/NearOptimal.lean`, with the
indicator likelihood as weight, runs through the whole plan: an observed chance step changes
nothing on either side (`TolInv.observed`), an unobserved one adds `(H / L - 1) U`. Against a
normalised reference kernel `κ` and a run kernel `κ'` within `[L, H]` of it, with
`e = approxGap k L H U` and `Z` the evidence mass:

* `solveCondRepPlan_mass`: the run's final mass (Julia's evidence probability) lies in
  `[L Z, H Z]`, so a positive computed mass gives positive evidence mass;
* `solveCondRepPlan_tolerant`: at positive evidence mass, a strategy `ρ` whose actions are within
  `τ` of the maximum of the run's score rows on every row has
  `value - e - card D * τ ≤ conditionalEU κ ρ u ev`, and every nonnegative strategy has
  conditional expected utility at most `value + e`;
* `solveCondRepPlan_approx_optimal`: the run's own strategy is deterministic and within `2 e` of
  the conditional optimum `conditionalOptimalValue`, and the value within `e` of it;
* `solveCondRepPlan_near_optimal`: `ρ` is within `2 e + card D * τ` of every nonnegative strategy
  and of the conditional optimum;
* `solveCondRepPlan_spec`: on the normalised kernel itself (`κ' = κ`, `e = 0`), the run's strategy
  realizes its value, which is the conditional optimum, and `ρ` is within `card D * τ` of it.

The conditional problem is the one of `Evidence.lean`: `conditionalEU`, `conditionalOptimalValue`
for the indicator likelihood `ev.toEvidence`. Tables on rows that contradict the evidence are
representation artefacts of the sliced run; the bounds hold for the recorded table as it is,
since the row condition is required on every row.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

variable {id : FinInfluenceDiagram}

/-! ## The driver -/

open Classical in
/-- Julia's chance step on sliced valuations: skip a variable that no valuation mentions,
otherwise sum it out with the representative `keep`. -/
def State.chanceRepSkip {R : Finset id.V} (keep : id.V → Bool) (v : id.V) (s : State id R) :
    State id (R.erase v) :=
  if h : bucket v s.valuations = [] then
    { valuations := s.valuations
      supported := fun _ hw => Finset.mem_erase.2
        ⟨fun he => notMem_scope_of_bucket_nil v _ h (he ▸ hw), s.supported hw⟩ }
  else s.chanceKeep keep v

theorem State.chanceRepSkip_of_nil {R : Finset id.V} (keep : id.V → Bool) (v : id.V)
    (s : State id R) (h : bucket v s.valuations = []) :
    (s.chanceRepSkip keep v).valuations = s.valuations := by
  unfold State.chanceRepSkip
  rw [dif_pos h]

theorem State.chanceRepSkip_of_ne {R : Finset id.V} (keep : id.V → Bool) (v : id.V)
    (s : State id R) (h : bucket v s.valuations ≠ []) :
    (s.chanceRepSkip keep v).valuations = chanceStepKeep (keep v) v s.valuations := by
  unfold State.chanceRepSkip
  rw [dif_neg h]
  rfl

/-- The bucket driver with Julia's skipping representative chance step. -/
def runRepSkipWith (sel : Selector id) (keep : id.V → Bool) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) : State id ∅ × Strategy id ℝ :=
  match plan with
  | .done => (s, σ)
  | .chance v _ _ next => runRepSkipWith sel keep next (s.chanceRepSkip keep v) σ
  | .decision d _ hi next =>
    runRepSkipWith sel keep next (s.decision d) (Function.update σ d (s.policyWith sel d hi))

/-- The valuations of `runRepSkipWith`. -/
def runRepSkipState (keep : id.V → Bool) {R : Finset id.V} (plan : Plan id R) (s : State id R) :
    State id ∅ :=
  match plan with
  | .done => s
  | .chance v _ _ next => runRepSkipState keep next (s.chanceRepSkip keep v)
  | .decision d _ _ next => runRepSkipState keep next (s.decision d)

theorem runRepSkipWith_state (sel : Selector id) (keep : id.V → Bool) {R : Finset id.V}
    (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ) :
    (runRepSkipWith sel keep plan s σ).1 = runRepSkipState keep plan s := by
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih => exact ih (s.chanceRepSkip keep v) σ
  | decision d _ hi next ih =>
    exact ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))

/-- The score row of `d` when `runRepSkipWith` eliminates its action. -/
def decisionScoreRepSkip (keep : id.V → Bool) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (d : id.D) : id.Assignment → id.states (id.action d) → ℝ :=
  match plan with
  | .done => fun _ _ => 0
  | .chance v _ _ next => decisionScoreRepSkip keep next (s.chanceRepSkip keep v) d
  | .decision d' _ _ next =>
    if d' = d then bucketScore s.valuations (id.action d)
    else decisionScoreRepSkip keep next (s.decision d') d

theorem decisionScoreRepSkip_local (keep : id.V → Bool) (hinj : Function.Injective id.action)
    {R : Finset id.V} (plan : Plan id R) (s : State id R) (d : id.D) (hd : id.action d ∈ R) :
    LocalOn (id.info d) (decisionScoreRepSkip keep plan s d) := by
  induction plan with
  | done => simp at hd
  | chance v _ hc next ih =>
    exact ih (s.chanceRepSkip keep v) (Finset.mem_erase.2 ⟨hc d, hd⟩)
  | decision d' hd' hi next ih =>
    by_cases hdd : d' = d
    · subst hdd
      intro x y h
      show (if d' = d' then bucketScore s.valuations (id.action d')
          else decisionScoreRepSkip keep next (s.decision d') d') x =
        (if d' = d' then bucketScore s.valuations (id.action d')
          else decisionScoreRepSkip keep next (s.decision d') d') y
      rw [if_pos rfl]
      exact bucketScore_local s d' hi x y h
    · intro x y h
      show (if d' = d then bucketScore s.valuations (id.action d)
          else decisionScoreRepSkip keep next (s.decision d') d) x =
        (if d' = d then bucketScore s.valuations (id.action d)
          else decisionScoreRepSkip keep next (s.decision d') d) y
      rw [if_neg hdd]
      exact ih (s.decision d') (Finset.mem_erase.2 ⟨fun he => hdd (hinj he).symm, hd⟩) x y h

theorem runRepSkipWith_snd_of_notMem (sel : Selector id) (keep : id.V → Bool) {R : Finset id.V}
    (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ) (e : id.D)
    (he : id.action e ∉ R) : (runRepSkipWith sel keep plan s σ).2 e = σ e := by
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih =>
    exact ih (s.chanceRepSkip keep v) σ (fun h => he (Finset.mem_of_mem_erase h))
  | decision d hd hi next ih =>
    refine (ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))
      (fun h => he (Finset.mem_of_mem_erase h))).trans ?_
    exact Function.update_of_ne (fun h : e = d => he (by rw [h]; exact hd)) _ _

theorem runRepSkipWith_policy_at_step (sel : Selector id) (keep : id.V → Bool) {R : Finset id.V}
    (d : id.D) (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d)
    (next : Plan id (R.erase (id.action d))) (s : State id R) (σ : Strategy id ℝ) :
    (runRepSkipWith sel keep (.decision d hd hi next) s σ).2 d = s.policyWith sel d hi := by
  refine (runRepSkipWith_snd_of_notMem sel keep next (s.decision d)
    (Function.update σ d (s.policyWith sel d hi)) d (Finset.notMem_erase _ _)).trans ?_
  exact Function.update_self _ _ _

theorem runRepSkipWith_deterministic (sel : Selector id) (keep : id.V → Bool) {R : Finset id.V}
    (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ) (hσ : σ.Deterministic) :
    (runRepSkipWith sel keep plan s σ).2.Deterministic := by
  induction plan generalizing σ with
  | done => exact hσ
  | chance v _ _ next ih => exact ih (s.chanceRepSkip keep v) σ hσ
  | decision d _ hi next ih =>
    apply ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))
    intro e
    by_cases h : e = d
    · subst e
      simp only [Function.update_self]
      exact ⟨_, fun x y h => congrArg (sel.pick d) (bucketScore_local s d hi x y h), rfl⟩
    · rw [Function.update_of_ne h]
      exact hσ e

/-- Every returned policy row is the selector's choice on the run's score. -/
theorem runRepSkipWith_kernel (sel : Selector id) (keep : id.V → Bool)
    (hinj : Function.Injective id.action) {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (σ : Strategy id ℝ) (d : id.D) (hd : id.action d ∈ R) (x : id.Assignment)
    (a : id.states (id.action d)) :
    ((runRepSkipWith sel keep plan s σ).2 d).kernel x a =
      if a = sel.pick d (decisionScoreRepSkip keep plan s d x) then 1 else 0 := by
  induction plan generalizing σ with
  | done => simp at hd
  | chance v _ hc next ih =>
    exact ih (s.chanceRepSkip keep v) σ (Finset.mem_erase.2 ⟨hc d, hd⟩)
  | decision d' hd' hi next ih =>
    by_cases hdd : d' = d
    · subst hdd
      rw [runRepSkipWith_policy_at_step]
      show (if a = sel.pick d' (bucketScore s.valuations (id.action d') x) then (1 : ℝ) else 0) =
        if a = sel.pick d' ((if d' = d' then bucketScore s.valuations (id.action d')
          else decisionScoreRepSkip keep next (s.decision d') d') x) then 1 else 0
      rw [if_pos rfl]
    · have hne : id.action d ≠ id.action d' := fun he => hdd (hinj he).symm
      refine (ih (s.decision d') (Function.update σ d' (s.policyWith sel d' hi))
        (Finset.mem_erase.2 ⟨hne, hd⟩)).trans ?_
      show (if a = sel.pick d (decisionScoreRepSkip keep next (s.decision d') d x) then (1 : ℝ)
          else 0) =
        if a = sel.pick d ((if d' = d then bucketScore s.valuations (id.action d)
          else decisionScoreRepSkip keep next (s.decision d') d) x) then 1 else 0
      rw [if_neg hdd]

/-! ## Scopes -/

/-- Observed variables are in no scope; every remaining unobserved chance variable is in one. -/
structure ScopeOK (O : Finset id.V) {R : Finset id.V} (s : State id R) : Prop where
  unobserved : ∀ v ∈ O, v ∉ (collect s.valuations).scope
  covers : ∀ v ∈ R, v ∉ O → (∀ d, id.action d ≠ v) → v ∈ (collect s.valuations).scope

theorem ScopeOK.chanceRepSkip {O : Finset id.V} {R : Finset id.V} {s : State id R}
    (h : ScopeOK O s) (keep : id.V → Bool) (v : id.V) : ScopeOK O (s.chanceRepSkip keep v) := by
  by_cases hnil : bucket v s.valuations = []
  · have hval := State.chanceRepSkip_of_nil keep v s hnil
    constructor
    · intro w hw hws
      rw [hval] at hws
      exact h.unobserved w hw hws
    · intro w hw hwO hwc
      rw [hval]
      exact h.covers w (Finset.mem_of_mem_erase hw) hwO hwc
  · have hval := State.chanceRepSkip_of_ne keep v s hnil
    have hscope : (collect (chanceStepKeep (keep v) v s.valuations)).scope =
        (collect s.valuations).scope.erase v :=
      step_scope_eq v s.valuations (sumOutKeep (keep v) v) (fun _ => rfl)
    constructor
    · intro w hw hws
      rw [hval, hscope] at hws
      exact h.unobserved w hw (Finset.mem_of_mem_erase hws)
    · intro w hw hwO hwc
      rw [hval, hscope]
      exact Finset.mem_erase.2
        ⟨Finset.ne_of_mem_erase hw, h.covers w (Finset.mem_of_mem_erase hw) hwO hwc⟩

theorem ScopeOK.decision {O : Finset id.V} {R : Finset id.V} {s : State id R}
    (h : ScopeOK O s) (d : id.D) : ScopeOK O (s.decision d) := by
  have hscope : (collect (decisionStep (id.action d) s.valuations)).scope =
      (collect s.valuations).scope.erase (id.action d) :=
    step_scope_eq _ s.valuations (maxOut (id.action d)) (fun _ => rfl)
  constructor
  · intro w hw hws
    change w ∈ (collect (decisionStep (id.action d) s.valuations)).scope at hws
    rw [hscope] at hws
    exact h.unobserved w hw (Finset.mem_of_mem_erase hws)
  · intro w hw hwO hwc
    change w ∈ (collect (decisionStep (id.action d) s.valuations)).scope
    rw [hscope]
    exact Finset.mem_erase.2
      ⟨fun he => hwc d he.symm, h.covers w (Finset.mem_of_mem_erase hw) hwO hwc⟩

/-! ## The invariant along the evidence run -/

theorem approxStep_nonneg {L H U : ℝ} (hL : 0 < L) (hLH : L ≤ H) (hU : 0 ≤ U) :
    0 ≤ (H / L - 1) * U := by
  refine mul_nonneg ?_ hU
  rw [sub_nonneg, le_div_iff₀ hL, one_mul]
  exact hLH

/-- **The tolerant invariant along Julia's evidence run**, for a fixed strategy `ρ` whose action
at every remaining decision is within `τ` of the maximum of the run's score on every row. -/
theorem tolInv_runRepSkip (keep : id.V → Bool) {κ : id.Kernel ℝ} (hκ : ∀ m x a, 0 ≤ κ m x a)
    (ev : HardEvidence id) (hind : Independent κ ev.toEvidence.likelihood)
    (hinj : Function.Injective id.action) {u : Utility id ℝ} {L H U : ℝ} (hL : 0 < L)
    (hLH : L ≤ H) (hU : 0 ≤ U) {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (ρ : Strategy id ℝ) (τ : ℝ)
    (hρ : ∀ d, id.action d ∈ R → ∃ g : id.Assignment → id.states (id.action d),
      (∀ x a, (ρ d).kernel x a = if a = g x then 1 else 0) ∧
        ∀ x b, decisionScoreRepSkip keep plan s d x b ≤
          decisionScoreRepSkip keep plan s d x (g x) + τ)
    (hsc : ScopeOK ev.observed s) (e t : ℝ)
    (h : TolInv κ u ev.toEvidence.likelihood ev.observed ev.value L H U e t s ρ) :
    TolInv κ u ev.toEvidence.likelihood ev.observed ev.value L H U
      (e + plan.chanceCount * ((H / L - 1) * U)) (t + plan.decisionCount * τ)
      (runRepSkipState keep plan s) ρ := by
  have hlik : ∀ y, 0 ≤ ev.toEvidence.likelihood y := ev.toEvidence.nonneg
  induction plan generalizing e t with
  | done => simpa [Plan.chanceCount, Plan.decisionCount, runRepSkipState] using h
  | @chance R v hv hc next ih =>
    have hs : TolInv κ u ev.toEvidence.likelihood ev.observed ev.value L H U
        (e + (H / L - 1) * U) t (s.chanceRepSkip keep v) ρ := by
      by_cases hvO : v ∈ ev.observed
      · have hnil : bucket v s.valuations = [] :=
          bucket_nil_of_notMem v _ (hsc.unobserved v hvO)
        have hval := State.chanceRepSkip_of_nil keep v s hnil
        have h0 := h.observed (fun z w hw hz => ev.likelihood_zero hw z hz) v hv hc hvO
          (s.chanceRepSkip keep v) (fun x => by rw [hval]) (fun x => by rw [hval])
        exact h0.weaken hκ hlik (le_add_of_nonneg_right (approxStep_nonneg hL hLH hU))
      · have hne : bucket v s.valuations ≠ [] :=
          fun hnil => notMem_scope_of_bucket_nil v _ hnil (hsc.covers v hv hvO hc)
        have hval := State.chanceRepSkip_of_ne keep v s hne
        obtain ⟨hp, hw⟩ := chanceStepKeep_collect (keep v) v s.valuations
        refine h.chanceOf hκ hlik hL hU v hv hc hvO _ (fun x => ?_) (fun x => ?_)
        · rw [hval, hp]
          exact chanceStep_prob v s.valuations x
        · rw [hval, hw]
          exact chanceStep_weight v s.valuations x
    have := ih (s.chanceRepSkip keep v) (fun d hd => hρ d (Finset.mem_of_mem_erase hd))
      (hsc.chanceRepSkip keep v) _ _ hs
    simp only [Plan.chanceCount, Plan.decisionCount, Nat.cast_add, Nat.cast_one] at this ⊢
    convert this using 1
    ring
  | @decision R d hd hi next ih =>
    obtain ⟨g, hgk, hgmax⟩ := hρ d hd
    have hmax : ∀ x b, bucketScore s.valuations (id.action d) x b ≤
        bucketScore s.valuations (id.action d) x (g x) + τ := by
      intro x b
      have := hgmax x b
      change (if d = d then bucketScore s.valuations (id.action d)
          else decisionScoreRepSkip keep next (s.decision d) d) x b ≤
        (if d = d then bucketScore s.valuations (id.action d)
          else decisionScoreRepSkip keep next (s.decision d) d) x (g x) + τ at this
      rwa [if_pos rfl] at this
    have hs := h.decisionOf hκ hlik hind hinj hL d hd hi (ev.action_notMem d)
      (fun w hw hwO => hsc.unobserved w hwO hw) (ρ d) g hgk τ hmax
    rw [Function.update_eq_self] at hs
    have hρ' : ∀ d', id.action d' ∈ R.erase (id.action d) →
        ∃ g' : id.Assignment → id.states (id.action d'),
          (∀ x a, (ρ d').kernel x a = if a = g' x then 1 else 0) ∧
            ∀ x b, decisionScoreRepSkip keep next (s.decision d) d' x b ≤
              decisionScoreRepSkip keep next (s.decision d) d' x (g' x) + τ := by
      intro d' hd'
      have hne : d ≠ d' := fun he => (Finset.mem_erase.1 hd').1 (by rw [he])
      obtain ⟨g', hk', hm'⟩ := hρ d' (Finset.mem_of_mem_erase hd')
      refine ⟨g', hk', fun x b => ?_⟩
      have := hm' x b
      change (if d = d' then bucketScore s.valuations (id.action d')
          else decisionScoreRepSkip keep next (s.decision d) d') x b ≤
        (if d = d' then bucketScore s.valuations (id.action d')
          else decisionScoreRepSkip keep next (s.decision d) d') x (g' x) + τ at this
      rwa [if_neg hne] at this
    have := ih (s.decision d) hρ' (hsc.decision d) _ _ hs
    simp only [Plan.chanceCount, Plan.decisionCount, Nat.cast_add, Nat.cast_one] at this ⊢
    convert this using 1
    ring

/-! ## The solver and the conditional problem -/

/-- **Julia's evidence run** on any plan: the sliced initial valuations, the skipping
representative chance step `keep`, and the selector `sel`. -/
def solveCondRepPlanWith (sel : Selector id) (keep : id.V → Bool) (κ : id.Kernel ℝ)
    (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (O : Finset id.V) (o : id.Assignment)
    (plan : Plan id Finset.univ) : Solution id :=
  let result := runRepSkipWith sel keep plan (initialConditioned κ hloc hnonneg u hu O o)
    defaultStrategy
  ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩

/-- The score row that `solveCondRepPlanWith` maximizes for `d`. -/
def solveCondRepPlanScore (keep : id.V → Bool) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (O : Finset id.V) (o : id.Assignment) (plan : Plan id Finset.univ) (d : id.D) :
    id.Assignment → id.states (id.action d) → ℝ :=
  decisionScoreRepSkip keep plan (initialConditioned κ hloc hnonneg u hu O o) d

/-- The final probability potential of `solveCondRepPlanWith` (Julia's `evidence_probability`). -/
def solveCondRepPlanMass (keep : id.V → Bool) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (O : Finset id.V) (o : id.Assignment) (plan : Plan id Finset.univ) : ℝ :=
  (collect (runRepSkipState keep plan (initialConditioned κ hloc hnonneg u hu O o)).valuations).prob
    (baseAssignment id)

theorem solveCondRepPlanWith_value (sel : Selector id) (keep : id.V → Bool) (κ : id.Kernel ℝ)
    (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (O : Finset id.V) (o : id.Assignment)
    (plan : Plan id Finset.univ) :
    (solveCondRepPlanWith sel keep κ hloc hnonneg u hu O o plan).value =
      (collect (runRepSkipState keep plan
        (initialConditioned κ hloc hnonneg u hu O o)).valuations).util (baseAssignment id) := by
  unfold solveCondRepPlanWith
  simp only
  rw [runRepSkipWith_state]

/-- The conditional expected utility through the reference marginals of the empty set. -/
theorem refMarg_empty_evidence (κ : id.Kernel ℝ) (e : Evidence id) (u : Utility id ℝ)
    (σ : Strategy id ℝ) (x : id.Assignment) :
    refMarg κ ∅ σ e.likelihood x = evidenceMass κ σ e ∧
      refMarg κ ∅ σ (likUtil e.likelihood u) x = evidenceNumerator κ σ u e := by
  constructor
  · rw [refMarg_empty]
    rfl
  · rw [refMarg_empty]
    unfold evidenceNumerator likUtil
    exact Finset.sum_congr rfl fun y _ => by ring

theorem conditionalEU_eq_weighted (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (u : Utility id ℝ) (e : Evidence id)
    (σ : Strategy id ℝ) :
    conditionalEU κ σ u e =
      expectedUtility κ σ (weightedUtility u e) / evidenceMass κ defaultStrategy e := by
  rw [conditionalEU, expectedUtility_weighted,
    evidenceMass_independent e κ hclosed ord hloc hnorm σ defaultStrategy]

/-- At positive evidence mass, no nonnegative strategy exceeds the conditional optimum. -/
theorem conditionalEU_le_optimal (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (u : Utility id ℝ) (e : Evidence id)
    (hZ : 0 < evidenceMass κ defaultStrategy e) (σ : Strategy id ℝ) (hσ : σ.Nonneg) :
    conditionalEU κ σ u e ≤ conditionalOptimalValue κ u e := by
  rw [conditionalEU_eq_weighted κ hclosed ord hloc hnorm, conditionalOptimalValue]
  exact div_le_div_of_nonneg_right (expectedUtility_le_optimalValue κ _ σ hσ) hZ.le

/-- The conditional optimum is attained by a nonnegative (deterministic) strategy. -/
theorem conditionalOptimal_attained (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (u : Utility id ℝ)
    (e : Evidence id) :
    ∃ σ : Strategy id ℝ, σ.Nonneg ∧ conditionalEU κ σ u e = conditionalOptimalValue κ u e := by
  obtain ⟨σ, _, hσ, hv⟩ := optimalValue_attained κ (weightedUtility u e)
  exact ⟨σ, hσ, by rw [conditionalEU_eq_weighted κ hclosed ord hloc hnorm, conditionalOptimalValue,
    hv]⟩

/-- The tolerant invariant at the end of Julia's evidence run, for a strategy `ρ` within `τ` of
the run's score rows on every row. -/
theorem tolInv_solveCondRepPlan (keep : id.V → Bool) (κ κ' : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (hloc' : ∀ m, Local κ' m)
    (hnonneg' : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ev : HardEvidence id) (plan : Plan id Finset.univ) (L H U : ℝ)
    (hL : 0 < L) (hLH : L ≤ H) (hU : 0 ≤ U)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U) (ρ : Strategy id ℝ)
    (g : (d : id.D) → id.Assignment → id.states (id.action d))
    (hρ : ∀ d x a, (ρ d).kernel x a = if a = g d x then 1 else 0) (τ : ℝ)
    (hg : ∀ d x b,
      solveCondRepPlanScore keep κ' hloc' hnonneg' u hu ev.observed ev.value plan d x b ≤
        solveCondRepPlanScore keep κ' hloc' hnonneg' u hu ev.observed ev.value plan d x (g d x) +
          τ) :
    TolInv κ u ev.toEvidence.likelihood ev.observed ev.value L H U
      (approxGap plan.chanceCount L H U) (Fintype.card id.D * τ)
      (runRepSkipState keep plan (initialConditioned κ' hloc' hnonneg' u hu ev.observed ev.value))
      ρ := by
  have hinj := (id.closed_iff.1 hclosed).2.1
  have hind := independent_evidence ev.toEvidence κ hclosed ord hloc hnorm
  have h0 : TolInv κ u ev.toEvidence.likelihood ev.observed ev.value L H U 0 0
      (initialConditioned κ' hloc' hnonneg' u hu ev.observed ev.value) ρ :=
    TolInv.initial κ' ev.likelihood_clamp _
      (fun x => by
        show (collect ((initial κ' hloc' hnonneg' u hu).valuations.map _)).prob x = _
        rw [collect_condition_prob, initial_prob])
      (fun x => by
        show (collect ((initial κ' hloc' hnonneg' u hu).valuations.map _)).util x = _
        rw [collect_condition_util, initial_util])
      henv hUb ρ (nonneg_of_kernel ρ g hρ)
  have hcp := initial_coupled κ' hclosed hloc' hnonneg' u hu ev
  have hr := tolInv_runRepSkip keep hnonneg ev hind hinj hL hLH hU plan _ ρ τ
    (fun d _ => ⟨g d, hρ d, hg d⟩) ⟨hcp.unobserved, hcp.covers⟩ 0 0 h0
  rw [zero_add, zero_add, Plan.decisionCount_univ hinj] at hr
  exact hr

/-- At the end of a run, the tolerant invariant bounds conditional expected utilities: the
strategy `σ` of the invariant is within `e + t` below the run's value, every nonnegative
strategy at most `e` above it. -/
theorem TolInv.conditional {κ : id.Kernel ℝ} (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) {u : Utility id ℝ} (e : Evidence id)
    {O : Finset id.V} {o : id.Assignment} {L H U err t : ℝ} {s : State id ∅}
    {σ : Strategy id ℝ} (h : TolInv κ u e.likelihood O o L H U err t s σ)
    (hZ : 0 < evidenceMass κ defaultStrategy e) :
    (collect s.valuations).util (baseAssignment id) - err - t ≤ conditionalEU κ σ u e ∧
      ∀ τ : Strategy id ℝ, τ.Nonneg →
        conditionalEU κ τ u e ≤ (collect s.valuations).util (baseAssignment id) + err := by
  have hind : ∀ ρ : Strategy id ℝ, evidenceMass κ ρ e = evidenceMass κ defaultStrategy e :=
    fun ρ => evidenceMass_independent e κ hclosed ord hloc hnorm ρ defaultStrategy
  constructor
  · have hl := h.lower (baseAssignment id)
    rw [(refMarg_empty_evidence κ e u σ _).1, (refMarg_empty_evidence κ e u σ _).2, hind] at hl
    rw [conditionalEU, hind, le_div_iff₀ hZ]
    exact hl
  · intro τ hτ
    have hd := h.dominates τ hτ (baseAssignment id)
    rw [(refMarg_empty_evidence κ e u τ _).2, (refMarg_empty_evidence κ e u σ _).1, hind] at hd
    rw [conditionalEU, hind, div_le_iff₀ hZ]
    exact hd

/-- The run's own strategy is within `0` of its score rows: the tolerant invariant with no loss. -/
theorem tolInv_solveCondRepPlan_run (sel : Selector id) (keep : id.V → Bool)
    (κ κ' : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (hloc' : ∀ m, Local κ' m)
    (hnonneg' : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ev : HardEvidence id) (plan : Plan id Finset.univ) (L H U : ℝ)
    (hL : 0 < L) (hLH : L ≤ H) (hU : 0 ≤ U)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U) :
    TolInv κ u ev.toEvidence.likelihood ev.observed ev.value L H U
      (approxGap plan.chanceCount L H U) 0
      (runRepSkipState keep plan (initialConditioned κ' hloc' hnonneg' u hu ev.observed ev.value))
      (solveCondRepPlanWith sel keep κ' hloc' hnonneg' u hu ev.observed ev.value
        plan).strategy := by
  have hinj := (id.closed_iff.1 hclosed).2.1
  have hr := tolInv_solveCondRepPlan keep κ κ' hclosed ord hloc hnorm hnonneg hloc' hnonneg' u hu
    ev plan L H U hL hLH hU henv hUb
    (solveCondRepPlanWith sel keep κ' hloc' hnonneg' u hu ev.observed ev.value plan).strategy
    (fun d x => sel.pick d
      (solveCondRepPlanScore keep κ' hloc' hnonneg' u hu ev.observed ev.value plan d x))
    (fun d x a => runRepSkipWith_kernel sel keep hinj plan _ defaultStrategy d (Finset.mem_univ _)
      x a) 0
    (fun d x b => by
      rw [add_zero]
      exact sel.maximizes d _ b)
  rwa [mul_zero] at hr

/-- **Julia's evidence probability brackets the evidence mass**: the run's final mass lies in
`[L Z, H Z]`, `Z` the reference evidence mass. -/
theorem solveCondRepPlan_mass (keep : id.V → Bool) (κ κ' : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (hloc' : ∀ m, Local κ' m)
    (hnonneg' : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ev : HardEvidence id) (plan : Plan id Finset.univ) (L H U : ℝ)
    (hL : 0 < L) (hLH : L ≤ H) (hU : 0 ≤ U)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U) :
    L * evidenceMass κ defaultStrategy ev.toEvidence ≤
        solveCondRepPlanMass keep κ' hloc' hnonneg' u hu ev.observed ev.value plan ∧
      solveCondRepPlanMass keep κ' hloc' hnonneg' u hu ev.observed ev.value plan ≤
        H * evidenceMass κ defaultStrategy ev.toEvidence := by
  have hr := tolInv_solveCondRepPlan_run (Selector.classical id) keep κ κ' hclosed ord hloc hnorm
    hnonneg hloc' hnonneg' u hu ev plan L H U hL hLH hU henv hUb
  have hind := evidenceMass_independent ev.toEvidence κ hclosed ord hloc hnorm
  have h1 := hr.mass_lower (baseAssignment id)
  have h2 := hr.mass_upper (baseAssignment id)
  rw [(refMarg_empty_evidence κ ev.toEvidence u _ _).1, hind] at h1 h2
  exact ⟨h1, h2⟩

/-- **A tolerant strategy on Julia's evidence run.** At positive evidence mass, a strategy `ρ`
reading at every decision `d` an action `g d x` within `τ` of the maximum of the run's score row
(`solveCondRepPlanScore`) on every row has conditional expected utility at least the run's value
minus `e + card D * τ`, and no nonnegative strategy exceeds the value plus `e`, with
`e = approxGap k L H U`. -/
theorem solveCondRepPlan_tolerant (sel : Selector id) (keep : id.V → Bool) (κ κ' : id.Kernel ℝ)
    (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (hloc' : ∀ m, Local κ' m)
    (hnonneg' : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ev : HardEvidence id) (plan : Plan id Finset.univ) (L H U : ℝ)
    (hL : 0 < L) (hLH : L ≤ H) (hU : 0 ≤ U)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U)
    (hZ : 0 < evidenceMass κ defaultStrategy ev.toEvidence) (ρ : Strategy id ℝ)
    (g : (d : id.D) → id.Assignment → id.states (id.action d))
    (hρ : ∀ d x a, (ρ d).kernel x a = if a = g d x then 1 else 0) (τ : ℝ)
    (hg : ∀ d x b,
      solveCondRepPlanScore keep κ' hloc' hnonneg' u hu ev.observed ev.value plan d x b ≤
        solveCondRepPlanScore keep κ' hloc' hnonneg' u hu ev.observed ev.value plan d x (g d x) +
          τ) :
    (solveCondRepPlanWith sel keep κ' hloc' hnonneg' u hu ev.observed ev.value plan).value -
        approxGap plan.chanceCount L H U - Fintype.card id.D * τ ≤
      conditionalEU κ ρ u ev.toEvidence ∧
    ∀ τ' : Strategy id ℝ, τ'.Nonneg →
      conditionalEU κ τ' u ev.toEvidence ≤
        (solveCondRepPlanWith sel keep κ' hloc' hnonneg' u hu ev.observed ev.value plan).value +
          approxGap plan.chanceCount L H U := by
  have hr := tolInv_solveCondRepPlan keep κ κ' hclosed ord hloc hnorm hnonneg hloc' hnonneg' u hu
    ev plan L H U hL hLH hU henv hUb ρ g hρ τ hg
  rw [solveCondRepPlanWith_value]
  exact hr.conditional hclosed ord hloc hnorm ev.toEvidence hZ

/-- **Approximate conditional optimality of Julia's evidence run.** At positive evidence mass, the
run's own strategy is deterministic and within `2 e` of every nonnegative strategy and of the
conditional optimum, and the run's value is within `e` of that optimum. -/
theorem solveCondRepPlan_approx_optimal (sel : Selector id) (keep : id.V → Bool)
    (κ κ' : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (hloc' : ∀ m, Local κ' m)
    (hnonneg' : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ev : HardEvidence id) (plan : Plan id Finset.univ) (L H U : ℝ)
    (hL : 0 < L) (hLH : L ≤ H) (hU : 0 ≤ U)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U)
    (hZ : 0 < evidenceMass κ defaultStrategy ev.toEvidence) :
    let sol := solveCondRepPlanWith sel keep κ' hloc' hnonneg' u hu ev.observed ev.value plan
    let e := approxGap plan.chanceCount L H U
    sol.strategy.Deterministic ∧
      (∀ τ : Strategy id ℝ, τ.Nonneg →
        conditionalEU κ τ u ev.toEvidence ≤ conditionalEU κ sol.strategy u ev.toEvidence + 2 * e) ∧
      conditionalOptimalValue κ u ev.toEvidence - 2 * e ≤
        conditionalEU κ sol.strategy u ev.toEvidence ∧
      conditionalEU κ sol.strategy u ev.toEvidence ≤ conditionalOptimalValue κ u ev.toEvidence ∧
      |sol.value - conditionalOptimalValue κ u ev.toEvidence| ≤ e := by
  intro sol e
  have hr := tolInv_solveCondRepPlan_run sel keep κ κ' hclosed ord hloc hnorm hnonneg hloc'
    hnonneg' u hu ev plan L H U hL hLH hU henv hUb
  obtain ⟨hlo, hdom⟩ := hr.conditional hclosed ord hloc hnorm ev.toEvidence hZ
  rw [← solveCondRepPlanWith_value sel] at hlo hdom
  change sol.value - e - 0 ≤ _ at hlo
  change ∀ τ : Strategy id ℝ, τ.Nonneg → _ ≤ sol.value + e at hdom
  have hdet : sol.strategy.Deterministic :=
    runRepSkipWith_deterministic sel keep _ _ _ defaultStrategy_deterministic
  have hle := conditionalEU_le_optimal κ hclosed ord hloc hnorm u ev.toEvidence hZ sol.strategy
    (deterministic_nonneg _ hdet)
  obtain ⟨σo, hσo, hvo⟩ := conditionalOptimal_attained κ hclosed ord hloc hnorm u ev.toEvidence
  have hopt := hdom σo hσo
  rw [hvo] at hopt
  refine ⟨hdet, fun τ hτ => ?_, by linarith, hle, ?_⟩
  · have := hdom τ hτ
    linarith
  · rw [abs_le]
    constructor <;> linarith

/-- **Near-optimality of a tolerant strategy with hard evidence.** Under the hypotheses of
`solveCondRepPlan_tolerant`, `ρ` is within `2 e + card D * τ` of every nonnegative strategy and of
the conditional optimum. -/
theorem solveCondRepPlan_near_optimal (sel : Selector id) (keep : id.V → Bool)
    (κ κ' : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (hloc' : ∀ m, Local κ' m)
    (hnonneg' : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ev : HardEvidence id) (plan : Plan id Finset.univ) (L H U : ℝ)
    (hL : 0 < L) (hLH : L ≤ H) (hU : 0 ≤ U)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U)
    (hZ : 0 < evidenceMass κ defaultStrategy ev.toEvidence) (ρ : Strategy id ℝ)
    (g : (d : id.D) → id.Assignment → id.states (id.action d))
    (hρ : ∀ d x a, (ρ d).kernel x a = if a = g d x then 1 else 0) (τ : ℝ)
    (hg : ∀ d x b,
      solveCondRepPlanScore keep κ' hloc' hnonneg' u hu ev.observed ev.value plan d x b ≤
        solveCondRepPlanScore keep κ' hloc' hnonneg' u hu ev.observed ev.value plan d x (g d x) +
          τ) :
    let e := approxGap plan.chanceCount L H U
    (∀ τ' : Strategy id ℝ, τ'.Nonneg →
        conditionalEU κ τ' u ev.toEvidence ≤
          conditionalEU κ ρ u ev.toEvidence + 2 * e + Fintype.card id.D * τ) ∧
      conditionalOptimalValue κ u ev.toEvidence - 2 * e - Fintype.card id.D * τ ≤
        conditionalEU κ ρ u ev.toEvidence := by
  intro e
  obtain ⟨hlo, hdom⟩ := solveCondRepPlan_tolerant sel keep κ κ' hclosed ord hloc hnorm hnonneg
    hloc' hnonneg' u hu ev plan L H U hL hLH hU henv hUb hZ ρ g hρ τ hg
  obtain ⟨σo, hσo, hvo⟩ := conditionalOptimal_attained κ hclosed ord hloc hnorm u ev.toEvidence
  have hopt := hdom σo hσo
  rw [hvo] at hopt
  refine ⟨fun τ' hτ' => ?_, by linarith⟩
  have := hdom τ' hτ'
  linarith

/-- The exact case: a kernel is within `[1, 1]` of itself, and the gap is then `0`. -/
theorem exact_envelope (κ : id.Kernel ℝ) (x : id.Assignment) :
    1 * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ m x (x (id.target m)) ∧
      ∏ m, κ m x (x (id.target m)) ≤ 1 * ∏ m, κ m x (x (id.target m)) :=
  ⟨le_of_eq (one_mul _), le_of_eq (one_mul _).symm⟩

theorem approxGap_one (k : ℕ) (U : ℝ) : approxGap k 1 1 U = 0 := by simp [approxGap]

theorem utility_bound (u : Utility id ℝ) :
    0 ≤ ∑ x, |totalUtility u x| ∧ ∀ x, |totalUtility u x| ≤ ∑ x, |totalUtility u x| :=
  ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x =>
    Finset.single_le_sum (f := fun x => |totalUtility u x|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ x)⟩

/-- **Julia's evidence run on exact, normalised data is conditionally optimal.** If the run is on
the normalised kernel `κ` itself and the evidence mass is positive, the run's strategy is
deterministic and realizes the run's value, which is the conditional optimum; its final mass is
the evidence mass; and a strategy within `τ` of the run's score rows on every row is within
`card D * τ` of every nonnegative strategy and of the conditional optimum. -/
theorem solveCondRepPlan_spec (sel : Selector id) (keep : id.V → Bool) (κ : id.Kernel ℝ)
    (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (ev : HardEvidence id) (plan : Plan id Finset.univ)
    (hZ : 0 < evidenceMass κ defaultStrategy ev.toEvidence) :
    let sol := solveCondRepPlanWith sel keep κ hloc hnonneg u hu ev.observed ev.value plan
    sol.strategy.Deterministic ∧ conditionalEU κ sol.strategy u ev.toEvidence = sol.value ∧
      sol.value = conditionalOptimalValue κ u ev.toEvidence ∧
      solveCondRepPlanMass keep κ hloc hnonneg u hu ev.observed ev.value plan =
        evidenceMass κ defaultStrategy ev.toEvidence ∧
      ∀ (ρ : Strategy id ℝ) (g : (d : id.D) → id.Assignment → id.states (id.action d)),
        (∀ d x a, (ρ d).kernel x a = if a = g d x then 1 else 0) → ∀ τ : ℝ,
        (∀ d x b, solveCondRepPlanScore keep κ hloc hnonneg u hu ev.observed ev.value plan d x b ≤
          solveCondRepPlanScore keep κ hloc hnonneg u hu ev.observed ev.value plan d x (g d x) +
            τ) →
        (∀ τ' : Strategy id ℝ, τ'.Nonneg →
          conditionalEU κ τ' u ev.toEvidence ≤
            conditionalEU κ ρ u ev.toEvidence + Fintype.card id.D * τ) ∧
        conditionalOptimalValue κ u ev.toEvidence - Fintype.card id.D * τ ≤
          conditionalEU κ ρ u ev.toEvidence := by
  intro sol
  obtain ⟨hU, hUb⟩ := utility_bound u
  have ha := solveCondRepPlan_approx_optimal sel keep κ κ hclosed ord hloc hnorm hnonneg hloc
    hnonneg u hu ev plan 1 1 _ one_pos le_rfl hU (exact_envelope κ) hUb hZ
  have hm := solveCondRepPlan_mass keep κ κ hclosed ord hloc hnorm hnonneg hloc hnonneg u hu ev
    plan 1 1 _ one_pos le_rfl hU (exact_envelope κ) hUb
  simp only [approxGap_one, mul_zero, add_zero, sub_zero, one_mul] at ha hm
  obtain ⟨hdet, -, hlo, hle, hv⟩ := ha
  have hv' : sol.value = conditionalOptimalValue κ u ev.toEvidence := by
    rw [abs_nonpos_iff, sub_eq_zero] at hv
    exact hv
  refine ⟨hdet, by linarith, hv', le_antisymm hm.2 hm.1, fun ρ g hρ τ hg => ?_⟩
  have hn := solveCondRepPlan_near_optimal sel keep κ κ hclosed ord hloc hnorm hnonneg hloc
    hnonneg u hu ev plan 1 1 _ one_pos le_rfl hU (exact_envelope κ) hUb hZ ρ g hρ τ hg
  simp only [approxGap_one, mul_zero, add_zero, sub_zero] at hn
  exact hn

end
end InfluenceDiagramsProofs.DVE
