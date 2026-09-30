import InfluenceDiagramsProofs.Finite.DVE.Selector
import BayesianNetworksProofs.Finite.Assignments

/-!
# Explicit evidence conditioning versus the likelihood representation

The verified evidence driver multiplies in one likelihood valuation. Julia instead applies
`condition` to every chance factor and every utility factor: each axis of an observed variable
is sliced at its observed label and dropped, so observed variables vanish from all scopes, and
the chance blocks then skip them (`sum_out` of an absent variable is the identity). This module
models that representation literally:

* `Valuation.condition O o` evaluates a valuation at `clamp O o x` and removes `O` from its
  scope, on both the probability and the utility potential;
* `State.chanceSkip` leaves the valuations unchanged when no valuation mentions the variable,
  and `runSkipWith` is the bucket driver with that skip, for any `Selector`.

For hard evidence on an action-free chance-ancestral set (`HardEvidence`), `Coupled` records
that at every stage the conditioned valuations evaluated at `x` have the **same probability and
the same weighted utility** as the likelihood valuations at `clamp O o x`, on every row,
including rows of zero probability. It holds initially and is preserved by every chance,
skipped and decision step. Utility potentials therefore agree wherever the probability is
positive (`Coupled.util_eq`); at zero-probability rows only the weighted valuations are
claimed to agree.

Consequences, at positive evidence mass: the conditioned driver's final mass is exactly the
evidence mass (`conditionedMass_eq`), it reports the same value as the likelihood driver, and
its own strategy realizes that conditional optimum (`solveConditioned_spec`); the checked
version rejects exactly zero mass (`solveConditionedChecked_eq`). With the first-label selector
its table agrees with the likelihood driver's at `clamp O o x` on every information row of
positive reach (`solveConditioned_policy_eq`) and is characterized there semantically
(`solveConditioned_semantic`). Tables at zero-reach rows, including rows inconsistent with the
evidence, are representation artefacts and are not claimed equal.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

/-! ## Clamping and conditioned valuations -/

section Clamp

variable {bn : FinBayesNet}

theorem clamp_agree {S O : Finset bn.V} (o : bn.Assignment) {x y : bn.Assignment}
    (h : ∀ v ∈ S \ O, x v = y v) : ∀ v ∈ S, clamp O o x v = clamp O o y v := by
  intro v hv
  by_cases hO : v ∈ O
  · simp [clamp, hO]
  · simp only [clamp, hO, if_false]
    exact h v (Finset.mem_sdiff.2 ⟨hv, hO⟩)

theorem clamp_update {O : Finset bn.V} (o x : bn.Assignment) {a : bn.V} (ha : a ∉ O)
    (b : bn.states a) :
    clamp O o (Function.update x a b) = Function.update (clamp O o x) a b := by
  funext v
  by_cases hv : v = a
  · subst hv
    simp [clamp, ha]
  · simp [clamp, Function.update_of_ne hv]

theorem update_clamp_self {O : Finset bn.V} (o x : bn.Assignment) {a : bn.V} (ha : a ∈ O) :
    Function.update (clamp O o x) a (o a) = clamp O o x := by
  funext v
  by_cases hv : v = a
  · subst hv
    simp [clamp, ha]
  · simp [Function.update_of_ne hv]

/-- Julia's `condition` on a valuation: both potentials are sliced at the observed states of
`O`, and those axes are dropped. -/
def Valuation.condition (O : Finset bn.V) (o : bn.Assignment) (v : Valuation bn) :
    Valuation bn where
  scope := v.scope \ O
  prob x := v.prob (clamp O o x)
  util x := v.util (clamp O o x)
  prob_local _ _ h := v.prob_local _ _ (clamp_agree o h)
  util_local _ _ h := v.util_local _ _ (clamp_agree o h)
  nonneg _ := v.nonneg _

theorem collect_condition_prob (O : Finset bn.V) (o : bn.Assignment)
    (vs : List (Valuation bn)) (x : bn.Assignment) :
    (collect (vs.map (Valuation.condition O o))).prob x = (collect vs).prob (clamp O o x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show (Valuation.condition O o v).prob x * (collect (vs.map _)).prob x = _
    rw [ih]
    rfl

theorem collect_condition_util (O : Finset bn.V) (o : bn.Assignment)
    (vs : List (Valuation bn)) (x : bn.Assignment) :
    (collect (vs.map (Valuation.condition O o))).util x = (collect vs).util (clamp O o x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show (Valuation.condition O o v).util x + (collect (vs.map _)).util x = _
    rw [ih]
    rfl

theorem collect_condition_scope (O : Finset bn.V) (o : bn.Assignment)
    (vs : List (Valuation bn)) :
    (collect (vs.map (Valuation.condition O o))).scope = (collect vs).scope \ O := by
  induction vs with
  | nil => simp [collect, unit]
  | cons v vs ih =>
    show (v.scope \ O) ∪ (collect (vs.map _)).scope = (v.scope ∪ (collect vs).scope) \ O
    rw [ih, Finset.union_sdiff_distrib]

theorem notMem_scope_of_bucket_nil (a : bn.V) (vs : List (Valuation bn))
    (h : bucket a vs = []) : a ∉ (collect vs).scope := by
  rw [collect_partition_scope a vs, h]
  simpa [collect, unit] using outside_notMem a vs

theorem bucket_nil_of_notMem (a : bn.V) (vs : List (Valuation bn))
    (h : a ∉ (collect vs).scope) : bucket a vs = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro w hw
  obtain ⟨hw, ha⟩ := List.mem_filter.1 hw
  exact h (collect_scope vs hw (of_decide_eq_true ha))

theorem decisionStep_weight_eq (a : bn.V) (vs : List (Valuation bn))
    (hp : ∀ x b, (collect vs).prob (Function.update x a b) = (collect vs).prob x)
    (x : bn.Assignment) :
    (collect (decisionStep a vs)).weight x =
      (collect vs).weight (Function.update x a (choice a (collect (bucket a vs)) x)) := by
  simp only [weight]
  rw [(decisionStep_eval a vs hp x).1, (decisionStep_eval a vs hp x).2]

end Clamp

variable {id : FinInfluenceDiagram}

/-! ## The driver that skips absent chance variables -/

open Classical in
/-- Julia's chance step: a variable that no valuation mentions is skipped. -/
def State.chanceSkip {R : Finset id.V} (v : id.V) (s : State id R) : State id (R.erase v) :=
  if h : bucket v s.valuations = [] then
    { valuations := s.valuations
      supported := fun _ hw => Finset.mem_erase.2
        ⟨fun he => notMem_scope_of_bucket_nil v _ h (he ▸ hw), s.supported hw⟩ }
  else s.chance v

theorem State.chanceSkip_of_nil {R : Finset id.V} (v : id.V) (s : State id R)
    (h : bucket v s.valuations = []) : (s.chanceSkip v).valuations = s.valuations := by
  unfold State.chanceSkip
  rw [dif_pos h]

theorem State.chanceSkip_of_ne {R : Finset id.V} (v : id.V) (s : State id R)
    (h : bucket v s.valuations ≠ []) :
    (s.chanceSkip v).valuations = chanceStep v s.valuations := by
  unfold State.chanceSkip
  rw [dif_neg h]
  rfl

/-- The bucket driver with Julia's skip of absent chance variables. -/
def runSkipWith (sel : Selector id) {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (σ : Strategy id ℝ) : State id ∅ × Strategy id ℝ :=
  match plan with
  | .done => (s, σ)
  | .chance v _ _ next => runSkipWith sel next (s.chanceSkip v) σ
  | .decision d _ hi next =>
    runSkipWith sel next (s.decision d) (Function.update σ d (s.policyWith sel d hi))

theorem runSkipWith_snd_of_notMem (sel : Selector id) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) (e : id.D) (he : id.action e ∉ R) :
    (runSkipWith sel plan s σ).2 e = σ e := by
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih =>
    exact ih (s.chanceSkip v) σ (fun h => he (Finset.mem_of_mem_erase h))
  | decision d hd hi next ih =>
    refine (ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))
      (fun h => he (Finset.mem_of_mem_erase h))).trans ?_
    exact Function.update_of_ne (fun h : e = d => he (by rw [h]; exact hd)) _ _

theorem runSkipWith_policy_at_step (sel : Selector id) {R : Finset id.V} (d : id.D)
    (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d)
    (next : Plan id (R.erase (id.action d))) (s : State id R) (σ : Strategy id ℝ) :
    (runSkipWith sel (.decision d hd hi next) s σ).2 d = s.policyWith sel d hi := by
  refine (runSkipWith_snd_of_notMem sel next (s.decision d)
    (Function.update σ d (s.policyWith sel d hi)) d (Finset.notMem_erase _ _)).trans ?_
  exact Function.update_self _ _ _

theorem runSkipWith_deterministic (sel : Selector id) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) (hσ : σ.Deterministic) :
    (runSkipWith sel plan s σ).2.Deterministic := by
  induction plan generalizing σ with
  | done => exact hσ
  | chance v _ _ next ih => exact ih (s.chanceSkip v) σ hσ
  | decision d _ hi next ih =>
    apply ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))
    intro e
    by_cases h : e = d
    · subst e
      simp only [Function.update_self]
      exact ⟨_, fun x y h => congrArg (sel.pick d) (bucketScore_local s d hi x y h), rfl⟩
    · rw [Function.update_of_ne h]
      exact hσ e

/-! ## Hard evidence and the coupling invariant -/

/-- Hard evidence as Julia accepts it for DVE: observed variables `observed`, observed states
`value`, and an action-free set of chance ancestors closed under causal parents. -/
structure HardEvidence (id : FinInfluenceDiagram) where
  ancestors : Finset id.V
  observed : Finset id.V
  sub : observed ⊆ ancestors
  closed : ∀ m, id.target m ∈ ancestors → id.parents m ⊆ ancestors
  no_action : ∀ d, id.action d ∉ ancestors
  value : id.Assignment

namespace HardEvidence

/-- The indicator-likelihood representation of the same evidence. -/
def toEvidence (H : HardEvidence id) : Evidence id :=
  Evidence.hard H.ancestors H.observed H.sub H.closed H.no_action H.value

theorem likelihood_clamp (H : HardEvidence id) (x : id.Assignment) :
    H.toEvidence.likelihood (clamp H.observed H.value x) = 1 := by
  simp only [toEvidence, Evidence.hard]
  rw [if_pos]
  intro v hv
  simp [clamp, hv]

theorem likelihood_zero (H : HardEvidence id) {v : id.V} (hv : v ∈ H.observed)
    (z : id.Assignment) (hz : z v ≠ H.value v) : H.toEvidence.likelihood z = 0 := by
  simp only [toEvidence, Evidence.hard]
  rw [if_neg]
  exact fun hall => hz (hall v hv)

theorem action_notMem (H : HardEvidence id) (d : id.D) : id.action d ∉ H.observed :=
  fun h => H.no_action d (H.sub h)

end HardEvidence

/-- The likelihood state vanishes on rows that contradict a not yet eliminated observation. -/
theorem Inv.vanish {κ : id.Kernel ℝ} {u : Utility id ℝ} {L : id.Assignment → ℝ}
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ} (h : Inv κ u L s σ) {v : id.V}
    (hv : v ∈ R) (y : id.Assignment) (hL : ∀ z, z v = y v → L z = 0) :
    (collect s.valuations).prob y = 0 ∧ (collect s.valuations).weight y = 0 := by
  have hz : ∀ z ∈ fibre Rᶜ y, L z = 0 := fun z hz => hL z (mem_fibre.1 hz v (by simpa using hv))
  constructor
  · rw [h.mass]
    unfold marg
    exact Finset.sum_eq_zero fun z hz' => by simp only [hz z hz', mul_zero]
  · rw [h.realizes]
    unfold marg
    exact Finset.sum_eq_zero fun z hz' => by simp only [hz z hz', zero_mul, mul_zero]

/-- On a row of positive likelihood-state probability, clamping changes nothing the state reads. -/
theorem Inv.clamp_eq {κ : id.Kernel ℝ} {u : Utility id ℝ} {H : HardEvidence id}
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ}
    (h : Inv κ u H.toEvidence.likelihood s σ) (y : id.Assignment)
    (hy : (collect s.valuations).prob y ≠ 0) :
    ∀ w ∈ (collect s.valuations).scope, y w = clamp H.observed H.value y w := by
  intro w hw
  by_cases hwO : w ∈ H.observed
  · simp only [clamp, hwO, if_true]
    by_contra hne
    exact hy (h.vanish (s.supported hw) y
      (fun z hz => H.likelihood_zero hwO z (by rw [hz]; exact hne))).1
  · simp [clamp, hwO]

/-- Julia's conditioned valuations against the likelihood valuations: equal probability and
weighted utility at `x` and `clamp O o x` respectively, on every row. -/
structure Coupled (O : Finset id.V) (o : id.Assignment) {R : Finset id.V}
    (sc sL : State id R) : Prop where
  prob : ∀ x, (collect sc.valuations).prob x = (collect sL.valuations).prob (clamp O o x)
  weight : ∀ x, (collect sc.valuations).weight x = (collect sL.valuations).weight (clamp O o x)
  unobserved : ∀ v ∈ O, v ∉ (collect sc.valuations).scope
  covers : ∀ v ∈ R, v ∉ O → (∀ d, id.action d ≠ v) → v ∈ (collect sc.valuations).scope

/-- Utility potentials agree wherever the probability is positive; at zero-probability rows the
representatives may differ, and only the weighted valuations are claimed to agree. -/
theorem Coupled.util_eq {O : Finset id.V} {o : id.Assignment} {R : Finset id.V}
    {sc sL : State id R} (hcp : Coupled O o sc sL) (x : id.Assignment)
    (hx : (collect sL.valuations).prob (clamp O o x) ≠ 0) :
    (collect sc.valuations).util x = (collect sL.valuations).util (clamp O o x) := by
  have hw := hcp.weight x
  simp only [Valuation.weight, hcp.prob x] at hw
  exact mul_left_cancel₀ hx hw

theorem Coupled.chance_unobserved {O : Finset id.V} {o : id.Assignment} {R : Finset id.V}
    {sc sL : State id R} (hcp : Coupled O o sc sL) (v : id.V) (hv : v ∈ R) (hvO : v ∉ O)
    (hc : ∀ d, id.action d ≠ v) : Coupled O o (sc.chanceSkip v) (sL.chance v) := by
  have hne : bucket v sc.valuations ≠ [] :=
    fun hnil => notMem_scope_of_bucket_nil v _ hnil (hcp.covers v hv hvO hc)
  have hval := State.chanceSkip_of_ne v sc hne
  have hscope : (collect (chanceStep v sc.valuations)).scope =
      (collect sc.valuations).scope.erase v :=
    step_scope_eq v sc.valuations (sumOut v) (fun _ => rfl)
  constructor
  · intro x
    rw [hval]
    change _ = (collect (chanceStep v sL.valuations)).prob _
    rw [chanceStep_prob, chanceStep_prob]
    exact Finset.sum_congr rfl fun b _ => by rw [hcp.prob, clamp_update o x hvO]
  · intro x
    rw [hval]
    change _ = (collect (chanceStep v sL.valuations)).weight _
    rw [chanceStep_weight, chanceStep_weight]
    exact Finset.sum_congr rfl fun b _ => by rw [hcp.weight, clamp_update o x hvO]
  · intro w hw hws
    rw [hval, hscope] at hws
    exact hcp.unobserved w hw (Finset.mem_of_mem_erase hws)
  · intro w hw hwO hwc
    rw [hval, hscope]
    exact Finset.mem_erase.2
      ⟨Finset.ne_of_mem_erase hw, hcp.covers w (Finset.mem_of_mem_erase hw) hwO hwc⟩

theorem Coupled.chance_observed {κ : id.Kernel ℝ} {u : Utility id ℝ} {H : HardEvidence id}
    {R : Finset id.V} {sc sL : State id R} {τ : Strategy id ℝ}
    (hcp : Coupled H.observed H.value sc sL) (hinv : Inv κ u H.toEvidence.likelihood sL τ)
    (v : id.V) (hv : v ∈ R) (hvO : v ∈ H.observed) :
    Coupled H.observed H.value (sc.chanceSkip v) (sL.chance v) := by
  have hnil : bucket v sc.valuations = [] := bucket_nil_of_notMem v _ (hcp.unobserved v hvO)
  have hval := State.chanceSkip_of_nil v sc hnil
  have hzero : ∀ (y : id.Assignment) (b : id.states v), b ≠ H.value v →
      (collect sL.valuations).prob (Function.update y v b) = 0 ∧
        (collect sL.valuations).weight (Function.update y v b) = 0 :=
    fun y b hb => hinv.vanish hv _ (fun z hz => H.likelihood_zero hvO z (by rw [hz]; simpa using hb))
  constructor
  · intro x
    rw [hval]
    change _ = (collect (chanceStep v sL.valuations)).prob _
    rw [chanceStep_prob, Finset.sum_eq_single (H.value v), update_clamp_self _ _ hvO, hcp.prob]
    · exact fun b _ hb => (hzero _ b hb).1
    · simp
  · intro x
    rw [hval]
    change _ = (collect (chanceStep v sL.valuations)).weight _
    rw [chanceStep_weight, Finset.sum_eq_single (H.value v), update_clamp_self _ _ hvO,
      hcp.weight]
    · exact fun b _ hb => (hzero _ b hb).2
    · simp
  · intro w hw
    rw [hval]
    exact hcp.unobserved w hw
  · intro w hw hwO hwc
    rw [hval]
    exact hcp.covers w (Finset.mem_of_mem_erase hw) hwO hwc

theorem Coupled.decision {O : Finset id.V} {o : id.Assignment} {R : Finset id.V}
    {sc sL : State id R} (hcp : Coupled O o sc sL) (d : id.D) (haO : id.action d ∉ O)
    (hpL : ∀ y b, (collect sL.valuations).prob (Function.update y (id.action d) b) =
      (collect sL.valuations).prob y) :
    Coupled O o (sc.decision d) (sL.decision d) := by
  have hpC : ∀ x b, (collect sc.valuations).prob (Function.update x (id.action d) b) =
      (collect sc.valuations).prob x := by
    intro x b
    rw [hcp.prob, hcp.prob, clamp_update o x haO, hpL]
  have hwc : ∀ x b, (collect sc.valuations).weight (Function.update x (id.action d) b) =
      (collect sL.valuations).weight (Function.update (clamp O o x) (id.action d) b) := by
    intro x b
    rw [hcp.weight, clamp_update o x haO]
  have hscope : (collect (decisionStep (id.action d) sc.valuations)).scope =
      (collect sc.valuations).scope.erase (id.action d) :=
    step_scope_eq _ sc.valuations (maxOut (id.action d)) (fun _ => rfl)
  constructor
  · intro x
    change (collect (decisionStep (id.action d) sc.valuations)).prob x =
      (collect (decisionStep (id.action d) sL.valuations)).prob (clamp O o x)
    rw [(decisionStep_eval _ _ hpC x).1, hpC, (decisionStep_eval _ _ hpL (clamp O o x)).1, hpL,
      hcp.prob]
  · intro x
    change (collect (decisionStep (id.action d) sc.valuations)).weight x =
      (collect (decisionStep (id.action d) sL.valuations)).weight (clamp O o x)
    apply le_antisymm
    · rw [decisionStep_weight_eq _ _ hpC, hwc]
      exact decisionStep_dominates _ _ hpL _ _
    · rw [decisionStep_weight_eq _ _ hpL, ← hwc]
      exact decisionStep_dominates _ _ hpC _ _
  · intro w hw hws
    change w ∈ (collect (decisionStep (id.action d) sc.valuations)).scope at hws
    rw [hscope] at hws
    exact hcp.unobserved w hw (Finset.mem_of_mem_erase hws)
  · intro w hw hwO hwc'
    change w ∈ (collect (decisionStep (id.action d) sc.valuations)).scope
    rw [hscope]
    exact Finset.mem_erase.2
      ⟨fun he => hwc' d he.symm, hcp.covers w (Finset.mem_of_mem_erase hw) hwO hwc'⟩

/-- On a positive row the two representations order the actions identically. -/
theorem Coupled.score_le_iff {O : Finset id.V} {o : id.Assignment} {R : Finset id.V}
    {sc sL : State id R} (hcp : Coupled O o sc sL) (d : id.D) (haO : id.action d ∉ O)
    (hpL : ∀ y b, (collect sL.valuations).prob (Function.update y (id.action d) b) =
      (collect sL.valuations).prob y)
    (x : id.Assignment) (hpos : 0 < (collect sL.valuations).prob (clamp O o x))
    (b c : id.states (id.action d)) :
    bucketScore sc.valuations (id.action d) x b ≤ bucketScore sc.valuations (id.action d) x c ↔
      bucketScore sL.valuations (id.action d) (clamp O o x) b ≤
        bucketScore sL.valuations (id.action d) (clamp O o x) c := by
  have hpC : ∀ b, (collect sc.valuations).prob (Function.update x (id.action d) b) =
      (collect sc.valuations).prob x := by
    intro b
    rw [hcp.prob, hcp.prob, clamp_update o x haO, hpL]
  have hwc : ∀ b, (collect sc.valuations).weight (Function.update x (id.action d) b) =
      (collect sL.valuations).weight (Function.update (clamp O o x) (id.action d) b) := by
    intro b
    rw [hcp.weight, clamp_update o x haO]
  rw [score_le_iff_weight_le sc.valuations _ x hpC (by rw [hcp.prob]; exact hpos),
    score_le_iff_weight_le sL.valuations _ (clamp O o x) (hpL _) hpos, hwc, hwc]

/-- On a positive likelihood row, the conditioned policy maximizes the likelihood bucket. -/
theorem Coupled.maximizes {κ : id.Kernel ℝ} {u : Utility id ℝ} {H : HardEvidence id}
    {R : Finset id.V} {sc sL : State id R} {τ : Strategy id ℝ}
    (hcp : Coupled H.observed H.value sc sL) (hinv : Inv κ u H.toEvidence.likelihood sL τ)
    (sel : Selector id) (d : id.D)
    (hpL : ∀ y b, (collect sL.valuations).prob (Function.update y (id.action d) b) =
      (collect sL.valuations).prob y)
    (y : id.Assignment) (hy : (collect sL.valuations).prob y ≠ 0)
    (b : id.states (id.action d)) :
    bucketScore sL.valuations (id.action d) y b ≤ bucketScore sL.valuations (id.action d) y
      (sel.pick d (bucketScore sc.valuations (id.action d) y)) := by
  have hagree := hinv.clamp_eq y hy
  have hcl : (collect sL.valuations).prob (clamp H.observed H.value y) =
      (collect sL.valuations).prob y :=
    (collect sL.valuations).prob_local _ _ (fun w hw => (hagree w hw).symm)
  have hbs : bucketScore sL.valuations (id.action d) (clamp H.observed H.value y) =
      bucketScore sL.valuations (id.action d) y := by
    funext c
    unfold bucketScore
    apply (collect (bucket (id.action d) sL.valuations)).util_local
    intro w hw
    by_cases hwa : w = id.action d
    · subst hwa
      simp
    · rw [Function.update_of_ne hwa, Function.update_of_ne hwa]
      exact (hagree w (filter_scope_subset _ sL.valuations hw)).symm
  have hpos : 0 < (collect sL.valuations).prob (clamp H.observed H.value y) := by
    rw [hcl]
    exact lt_of_le_of_ne ((collect sL.valuations).nonneg y) (Ne.symm hy)
  rw [← hbs]
  exact (hcp.score_le_iff d (H.action_notMem d) hpL y hpos b _).1 (sel.maximizes d _ b)

/-- The coupled run: final states stay coupled, and the conditioned strategy satisfies the
likelihood invariant, so it realizes the likelihood driver's weighted value. -/
theorem conditioned_run {κ : id.Kernel ℝ} {u : Utility id ℝ} (H : HardEvidence id)
    (sel : Selector id) (hind : Independent κ H.toEvidence.likelihood) (hclosed : id.Closed)
    {R : Finset id.V} (plan : Plan id R) (sc sL : State id R) (σ : Strategy id ℝ)
    (hcp : Coupled H.observed H.value sc sL) (hinv : Inv κ u H.toEvidence.likelihood sL σ) :
    Coupled H.observed H.value (runSkipWith sel plan sc σ).1 (runState plan sL) ∧
      Inv κ u H.toEvidence.likelihood (runState plan sL) (runSkipWith sel plan sc σ).2 := by
  induction plan generalizing σ with
  | done => exact ⟨hcp, hinv⟩
  | chance v hv hc next ih =>
    by_cases hvO : v ∈ H.observed
    · exact ih (sc.chanceSkip v) (sL.chance v) σ (hcp.chance_observed hinv v hv hvO)
        (hinv.chance v hv hc)
    · exact ih (sc.chanceSkip v) (sL.chance v) σ (hcp.chance_unobserved v hv hvO hc)
        (hinv.chance v hv hc)
  | decision d hd hi next ih =>
    have hpL := hinv.prob_update hind d hd hi
    refine ih (sc.decision d) (sL.decision d) (Function.update σ d (sc.policyWith sel d hi))
      (hcp.decision d (H.action_notMem d) hpL) ?_
    exact hinv.decisionOf hind hclosed d hd hi _
      (fun y => sel.pick d (bucketScore sc.valuations (id.action d) y)) (fun _ _ => rfl)
      (fun y hy b => hcp.maximizes hinv sel d hpL y hy b)

/-- First-label policies of the two representations agree on every row of positive reach,
and are characterized there by the conditioned driver's own continuation values. -/
theorem conditioned_policy [∀ d : id.D, LinearOrder (id.states (id.action d))]
    {κ : id.Kernel ℝ} {u : Utility id ℝ} (H : HardEvidence id)
    (hind : Independent κ H.toEvidence.likelihood) (hclosed : id.Closed)
    {R : Finset id.V} (plan : Plan id R) (sc sL : State id R) (σc σL : Strategy id ℝ)
    (hcp : Coupled H.observed H.value sc sL)
    (hinvC : Inv κ u H.toEvidence.likelihood sL σc)
    (hinvL : Inv κ u H.toEvidence.likelihood sL σL)
    (d : id.D) (hd : id.action d ∈ R) (x : id.Assignment) :
    (reach κ H.toEvidence.likelihood (runWith (Selector.ordered id) plan sL σL).2 d
        (clamp H.observed H.value x) ≠ 0 →
      ((runSkipWith (Selector.ordered id) plan sc σc).2 d).kernel x =
        ((runWith (Selector.ordered id) plan sL σL).2 d).kernel (clamp H.observed H.value x)) ∧
    (reach κ H.toEvidence.likelihood (runSkipWith (Selector.ordered id) plan sc σc).2 d
        (clamp H.observed H.value x) ≠ 0 → ∀ a,
      ((runSkipWith (Selector.ordered id) plan sc σc).2 d).kernel x a =
        if a = firstArgmax (continuation κ u H.toEvidence.likelihood
          (runSkipWith (Selector.ordered id) plan sc σc).2 d (clamp H.observed H.value x))
        then 1 else 0) := by
  have hinj := (id.closed_iff.1 hclosed).2.1
  induction plan generalizing σc σL with
  | done => simp at hd
  | @chance R' v hv hc next ih =>
    have hd' : id.action d ∈ R'.erase v := Finset.mem_erase.2 ⟨hc d, hd⟩
    by_cases hvO : v ∈ H.observed
    · exact ih (sc.chanceSkip v) (sL.chance v) σc σL (hcp.chance_observed hinvC v hv hvO)
        (hinvC.chance v hv hc) (hinvL.chance v hv hc) hd'
    · exact ih (sc.chanceSkip v) (sL.chance v) σc σL (hcp.chance_unobserved v hv hvO hc)
        (hinvC.chance v hv hc) (hinvL.chance v hv hc) hd'
  | @decision R' d' hd' hi next ih =>
    have hpL := hinvL.prob_update hind d' hd' hi
    by_cases hdd : d' = d
    · subst hdd
      have hτL : ∀ e, id.action e ∉ R' →
          (runWith (Selector.ordered id) (.decision d' hd' hi next) sL σL).2 e = σL e := by
        intro e he
        refine (runWith_snd_of_notMem _ next (sL.decision d')
          (Function.update σL d' (sL.policyWith (Selector.ordered id) d' hi)) e
          (fun h' => he (Finset.mem_of_mem_erase h'))).trans ?_
        exact Function.update_of_ne (fun h' : e = d' => he (by rw [h']; exact hd')) _ _
      have hτC : ∀ e, id.action e ∉ R' →
          (runSkipWith (Selector.ordered id) (.decision d' hd' hi next) sc σc).2 e = σc e := by
        intro e he
        refine (runSkipWith_snd_of_notMem _ next (sc.decision d')
          (Function.update σc d' (sc.policyWith (Selector.ordered id) d' hi)) e
          (fun h' => he (Finset.mem_of_mem_erase h'))).trans ?_
        exact Function.update_of_ne (fun h' : e = d' => he (by rw [h']; exact hd')) _ _
      obtain ⟨hreachL, _⟩ :=
        reach_continuation_at_step hinvL d' hd' hi _ hτL (clamp H.observed H.value x)
      obtain ⟨hreachC, hcontC⟩ :=
        reach_continuation_at_step hinvC d' hd' hi _ hτC (clamp H.observed H.value x)
      have key : ∀ hpos : 0 < (collect sL.valuations).prob (clamp H.observed H.value x),
          firstArgmax (bucketScore sc.valuations (id.action d') x) =
            firstArgmax (bucketScore sL.valuations (id.action d') (clamp H.observed H.value x)) :=
        fun hpos => firstArgmax_congr
          (hcp.score_le_iff d' (H.action_notMem d') hpL x hpos)
      have hposOf : ∀ r, r = (collect sL.valuations).prob (clamp H.observed H.value x) →
          r ≠ 0 → 0 < (collect sL.valuations).prob (clamp H.observed H.value x) :=
        fun r hr hne => lt_of_le_of_ne ((collect sL.valuations).nonneg _)
          (fun h0 => hne (hr.trans h0.symm))
      constructor
      · intro hx
        rw [runSkipWith_policy_at_step, runWith_policy_at_step]
        funext a
        show (if a = firstArgmax (bucketScore sc.valuations (id.action d') x) then (1 : ℝ)
            else 0) = if a = firstArgmax (bucketScore sL.valuations (id.action d')
              (clamp H.observed H.value x)) then 1 else 0
        rw [key (hposOf _ hreachL hx)]
      · intro hx a
        have hpos := hposOf _ hreachC hx
        rw [hcontC, runSkipWith_policy_at_step,
          ← firstArgmax_score_eq_weight sL.valuations (id.action d') _ (hpL _) hpos, ← key hpos]
        rfl
    · have hne : id.action d ≠ id.action d' := fun he => hdd (hinj he).symm
      exact ih (sc.decision d') (sL.decision d') _ _ (hcp.decision d' (H.action_notMem d') hpL)
        (hinvC.decisionOf hind hclosed d' hd' hi (sc.policyWith (Selector.ordered id) d' hi)
          (fun y => (Selector.ordered id).pick d' (bucketScore sc.valuations (id.action d') y))
          (fun _ _ => rfl) (fun y hy b => hcp.maximizes hinvC _ d' hpL y hy b))
        (hinvL.decisionWith hind hclosed (Selector.ordered id) d' hd' hi)
        (Finset.mem_erase.2 ⟨hne, hd⟩)

/-! ## The conditioned solver -/

/-- Julia's initial valuations: every chance and utility valuation conditioned on `O`. -/
def initialConditioned (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (O : Finset id.V) (o : id.Assignment) : State id Finset.univ where
  valuations := (initial κ hloc hnonneg u hu).valuations.map (Valuation.condition O o)
  supported := Finset.subset_univ _

theorem initial_coupled (κ : id.Kernel ℝ) (hclosed : id.Closed) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (H : HardEvidence id) :
    Coupled H.observed H.value (initialConditioned κ hloc hnonneg u hu H.observed H.value)
      (initialEvidence κ hloc hnonneg u hu H.toEvidence) where
  prob x := by
    show (collect ((initial κ hloc hnonneg u hu).valuations.map _)).prob x =
      H.toEvidence.likelihood _ * (collect (initial κ hloc hnonneg u hu).valuations).prob _
    rw [collect_condition_prob, H.likelihood_clamp, one_mul]
  weight x := by
    show (collect ((initial κ hloc hnonneg u hu).valuations.map _)).prob x *
        (collect ((initial κ hloc hnonneg u hu).valuations.map _)).util x =
      (H.toEvidence.likelihood _ * (collect (initial κ hloc hnonneg u hu).valuations).prob _) *
        (0 + (collect (initial κ hloc hnonneg u hu).valuations).util _)
    rw [collect_condition_prob, collect_condition_util, H.likelihood_clamp, one_mul, zero_add]
  unobserved v hv := by
    show v ∉ (collect ((initial κ hloc hnonneg u hu).valuations.map _)).scope
    rw [collect_condition_scope]
    exact fun h => (Finset.mem_sdiff.1 h).2 hv
  covers v hv hvO hc := by
    show v ∈ (collect ((initial κ hloc hnonneg u hu).valuations.map _)).scope
    rw [collect_condition_scope]
    exact Finset.mem_sdiff.2 ⟨initial_covers_chance κ hclosed hloc hnonneg u hu v hv hc, hvO⟩

/-- The model of Julia's evidence path: condition, then run the skipping bucket driver. -/
def conditionedRun (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (O : Finset id.V) (o : id.Assignment) :
    State id ∅ × Strategy id ℝ :=
  runSkipWith sel (nf.plan ord.no_self_info) (initialConditioned κ hloc hnonneg u hu O o)
    defaultStrategy

def solveConditioned (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (O : Finset id.V) (o : id.Assignment) :
    Solution id :=
  ⟨(collect (conditionedRun sel κ hloc hnonneg u hu ord nf O o).1.valuations).util
      (baseAssignment id),
    (conditionedRun sel κ hloc hnonneg u hu ord nf O o).2⟩

/-- The final probability potential of the conditioned run (Julia's `evidence_probability`). -/
def conditionedMass (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (O : Finset id.V) (o : id.Assignment) : ℝ :=
  (collect (conditionedRun sel κ hloc hnonneg u hu ord nf O o).1.valuations).prob
    (baseAssignment id)

/-- Julia's check: an exactly zero final mass is impossible evidence. -/
def solveConditionedChecked (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (O : Finset id.V) (o : id.Assignment) :
    Option (Solution id) :=
  if 0 < conditionedMass sel κ hloc hnonneg u hu ord nf O o then
    some (solveConditioned sel κ hloc hnonneg u hu ord nf O o) else none

theorem State.empty_const (s : State id ∅) (x y : id.Assignment) :
    (collect s.valuations).prob x = (collect s.valuations).prob y ∧
      (collect s.valuations).util x = (collect s.valuations).util y := by
  have h : ∀ w ∈ (collect s.valuations).scope, x w = y w :=
    fun w hw => absurd (s.supported hw) (Finset.notMem_empty w)
  exact ⟨(collect s.valuations).prob_local _ _ h, (collect s.valuations).util_local _ _ h⟩

/-- The final coupled facts at the empty remaining set. -/
theorem conditioned_final (sel : Selector id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (H : HardEvidence id) :
    (collect (conditionedRun sel κ hloc hnonneg u hu ord nf H.observed
        H.value).1.valuations).prob (baseAssignment id) =
        (collect (runState (nf.plan ord.no_self_info)
          (initialEvidence κ hloc hnonneg u hu H.toEvidence)).valuations).prob
            (baseAssignment id) ∧
      (collect (conditionedRun sel κ hloc hnonneg u hu ord nf H.observed
        H.value).1.valuations).weight (baseAssignment id) =
        (collect (runState (nf.plan ord.no_self_info)
          (initialEvidence κ hloc hnonneg u hu H.toEvidence)).valuations).weight
            (baseAssignment id) ∧
      Inv κ u H.toEvidence.likelihood (runState (nf.plan ord.no_self_info)
          (initialEvidence κ hloc hnonneg u hu H.toEvidence))
        (conditionedRun sel κ hloc hnonneg u hu ord nf H.observed H.value).2 := by
  obtain ⟨hcp, hinv⟩ := conditioned_run H sel
    (independent_evidence H.toEvidence κ hclosed ord hloc hnorm) hclosed
    (nf.plan ord.no_self_info) (initialConditioned κ hloc hnonneg u hu H.observed H.value)
    (initialEvidence κ hloc hnonneg u hu H.toEvidence) defaultStrategy
    (initial_coupled κ hclosed hloc hnonneg u hu H)
    (Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu H.toEvidence _))
  have hc := State.empty_const (runState (nf.plan ord.no_self_info)
      (initialEvidence κ hloc hnonneg u hu H.toEvidence))
    (clamp H.observed H.value (baseAssignment id)) (baseAssignment id)
  refine ⟨(hcp.prob _).trans hc.1, (hcp.weight _).trans ?_, hinv⟩
  simp only [Valuation.weight, hc.1, hc.2]

/-- **Julia's evidence probability is the evidence mass.** -/
theorem conditionedMass_eq (sel : Selector id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (H : HardEvidence id) :
    conditionedMass sel κ hloc hnonneg u hu ord nf H.observed H.value =
      evidenceMass κ defaultStrategy H.toEvidence := by
  rw [conditionedMass, (conditioned_final sel κ hclosed ord nf hloc hnorm hnonneg u hu H).1,
    ← run_state _ _ defaultStrategy]
  exact runEvidence_mass κ hclosed ord nf hloc hnorm hnonneg u hu H.toEvidence

/-- **Explicit conditioning is correct.** At positive evidence mass, running the driver on
Julia's conditioned (sliced) chance and utility valuations, with any maximizing selector,
returns a deterministic strategy that realizes the reported conditional value; that value is
the likelihood driver's value and the independent conditional optimum. -/
theorem solveConditioned_spec (sel : Selector id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (H : HardEvidence id)
    (hpositive : 0 < evidenceMass κ defaultStrategy H.toEvidence) :
    let sol := solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value
    sol.strategy.Deterministic ∧
      conditionalEU κ sol.strategy u H.toEvidence = sol.value ∧
      sol.value = (solveEvidence κ hloc hnonneg u hu ord nf H.toEvidence).value ∧
      sol.value = conditionalOptimalValue κ u H.toEvidence := by
  intro sol
  obtain ⟨hprob, hweight, hinv⟩ :=
    conditioned_final sel κ hclosed ord nf hloc hnorm hnonneg u hu H
  have hZL := runEvidence_mass κ hclosed ord nf hloc hnorm hnonneg u hu H.toEvidence
  dsimp only at hZL
  rw [run_state] at hZL
  have hZ : evidenceMass κ defaultStrategy H.toEvidence ≠ 0 := ne_of_gt hpositive
  have hvalue : (collect (conditionedRun sel κ hloc hnonneg u hu ord nf H.observed
      H.value).1.valuations).util (baseAssignment id) =
      (solveEvidence κ hloc hnonneg u hu ord nf H.toEvidence).value := by
    show _ = (collect (run (nf.plan ord.no_self_info)
      (initialEvidence κ hloc hnonneg u hu H.toEvidence) defaultStrategy).1.valuations).util
        (baseAssignment id)
    rw [run_state]
    have hw := hweight
    simp only [weight] at hw
    rw [hprob, hZL] at hw
    exact mul_left_cancel₀ hZ hw
  have hr : evidenceNumerator κ (conditionedRun sel κ hloc hnonneg u hu ord nf H.observed
      H.value).2 u H.toEvidence = evidenceMass κ defaultStrategy H.toEvidence *
        (collect (conditionedRun sel κ hloc hnonneg u hu ord nf H.observed
          H.value).1.valuations).util (baseAssignment id) := by
    have h := hinv.realizes (baseAssignment id)
    rw [← hweight] at h
    simp only [weight] at h
    rw [hprob, hZL, Finset.compl_empty, freeJoint_univ, marg_univ] at h
    simpa only [evidenceNumerator, mul_assoc] using h.symm
  refine ⟨runSkipWith_deterministic sel _ _ _ defaultStrategy_deterministic, ?_, hvalue, ?_⟩
  · show conditionalEU κ (conditionedRun sel κ hloc hnonneg u hu ord nf H.observed H.value).2 u
        H.toEvidence = (collect (conditionedRun sel κ hloc hnonneg u hu ord nf H.observed
          H.value).1.valuations).util (baseAssignment id)
    unfold conditionalEU
    rw [hr, evidenceMass_independent H.toEvidence κ hclosed ord hloc hnorm
      (conditionedRun sel κ hloc hnonneg u hu ord nf H.observed H.value).2 defaultStrategy]
    exact mul_div_cancel_left₀ _ hZ
  · show (collect (conditionedRun sel κ hloc hnonneg u hu ord nf H.observed
        H.value).1.valuations).util (baseAssignment id) = _
    rw [hvalue]
    exact solveEvidence_eq_optimal κ hclosed ord nf hloc hnorm hnonneg u hu H.toEvidence hpositive

/-- The checked conditioned driver answers exactly at positive evidence mass. -/
theorem solveConditionedChecked_eq (sel : Selector id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (H : HardEvidence id) :
    solveConditionedChecked sel κ hloc hnonneg u hu ord nf H.observed H.value =
      if 0 < evidenceMass κ defaultStrategy H.toEvidence then
        some (solveConditioned sel κ hloc hnonneg u hu ord nf H.observed H.value) else none := by
  unfold solveConditionedChecked
  rw [conditionedMass_eq sel κ hclosed ord nf hloc hnorm hnonneg u hu H]

theorem solveConditionedChecked_none_iff (sel : Selector id) (κ : id.Kernel ℝ)
    (hclosed : id.Closed) (ord : id.IDOrder) (nf : NoForgettingOrder id)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (H : HardEvidence id) :
    solveConditionedChecked sel κ hloc hnonneg u hu ord nf H.observed H.value = none ↔
      evidenceMass κ defaultStrategy H.toEvidence = 0 := by
  rw [solveConditionedChecked_eq sel κ hclosed ord nf hloc hnorm hnonneg u hu H]
  by_cases hp : 0 < evidenceMass κ defaultStrategy H.toEvidence
  · simp [hp, ne_of_gt hp]
  · have hz : evidenceMass κ defaultStrategy H.toEvidence = 0 := le_antisymm (le_of_not_gt hp)
      (evidenceMass_nonneg _ κ hnonneg _ (deterministic_nonneg _ defaultStrategy_deterministic))
    simp [hz]

/-- Sliced valuations never mention an observed variable, so every conditioned policy reads
its observed information coordinates as the observed states. -/
theorem runSkipWith_kernel_clamp (sel : Selector id) (O : Finset id.V) (o : id.Assignment)
    {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ)
    (hs : ∀ v ∈ O, v ∉ (collect s.valuations).scope)
    (hσ : ∀ e x, (σ e).kernel x = (σ e).kernel (clamp O o x)) (d : id.D) (x : id.Assignment) :
    ((runSkipWith sel plan s σ).2 d).kernel x =
      ((runSkipWith sel plan s σ).2 d).kernel (clamp O o x) := by
  induction plan generalizing σ with
  | done => exact hσ d x
  | chance v _ _ next ih =>
    apply ih (s.chanceSkip v) σ _ hσ
    intro w hw hws
    by_cases hnil : bucket v s.valuations = []
    · rw [State.chanceSkip_of_nil v s hnil] at hws
      exact hs w hw hws
    · have hscope : (collect (chanceStep v s.valuations)).scope =
          (collect s.valuations).scope.erase v :=
        step_scope_eq v s.valuations (sumOut v) (fun _ => rfl)
      rw [State.chanceSkip_of_ne v s hnil, hscope] at hws
      exact hs w hw (Finset.mem_of_mem_erase hws)
  | decision d' _ hi next ih =>
    apply ih (s.decision d') (Function.update σ d' (s.policyWith sel d' hi))
    · intro w hw hws
      change w ∈ (collect (decisionStep (id.action d') s.valuations)).scope at hws
      have hscope : (collect (decisionStep (id.action d') s.valuations)).scope =
          (collect s.valuations).scope.erase (id.action d') :=
        step_scope_eq _ s.valuations (maxOut (id.action d')) (fun _ => rfl)
      rw [hscope] at hws
      exact hs w hw (Finset.mem_of_mem_erase hws)
    · intro e y
      by_cases he : e = d'
      · subst he
        simp only [Function.update_self]
        have hb : bucketScore s.valuations (id.action e) y =
            bucketScore s.valuations (id.action e) (clamp O o y) := by
          funext b
          unfold bucketScore
          apply (collect (bucket (id.action e) s.valuations)).util_local
          intro w hw
          by_cases hwa : w = id.action e
          · subst hwa
            simp
          · rw [Function.update_of_ne hwa, Function.update_of_ne hwa]
            have hwO : w ∉ O := fun hO => hs w hO (filter_scope_subset _ s.valuations hw)
            simp [clamp, hwO]
        funext a
        show (if a = sel.pick e (bucketScore s.valuations (id.action e) y) then (1 : ℝ) else 0) =
          if a = sel.pick e (bucketScore s.valuations (id.action e) (clamp O o y)) then 1 else 0
        rw [hb]
      · rw [Function.update_of_ne he]
        exact hσ e y

/-- **Julia's conditioned tables are constant along observed coordinates**: the entry on a
row that contradicts the evidence is the entry of the evidence-clamped row. -/
theorem solveConditioned_kernel_clamp (sel : Selector id) (κ : id.Kernel ℝ)
    (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (ord : id.IDOrder) (nf : NoForgettingOrder id)
    (O : Finset id.V) (o : id.Assignment) (d : id.D) (x : id.Assignment) :
    ((solveConditioned sel κ hloc hnonneg u hu ord nf O o).strategy d).kernel x =
      ((solveConditioned sel κ hloc hnonneg u hu ord nf O o).strategy d).kernel (clamp O o x) := by
  refine runSkipWith_kernel_clamp sel O o (nf.plan ord.no_self_info)
    (initialConditioned κ hloc hnonneg u hu O o) defaultStrategy ?_ (fun _ _ => rfl) d x
  intro v hv hvs
  change v ∈ (collect ((initial κ hloc hnonneg u hu).valuations.map _)).scope at hvs
  rw [collect_condition_scope] at hvs
  exact (Finset.mem_sdiff.1 hvs).2 hv

section Ordered

variable [∀ d : id.D, LinearOrder (id.states (id.action d))]

/-- **Same first-label tables on reachable rows.** Julia's conditioned driver and the verified
likelihood driver, both with the first-label selector, choose the same action at `x` and at
`clamp O o x` respectively, on every row whose clamped information row has positive reach. -/
theorem solveConditioned_policy_eq (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (H : HardEvidence id) (d : id.D) (x : id.Assignment)
    (hx : reach κ H.toEvidence.likelihood
      (solveEvidenceWith (Selector.ordered id) κ hloc hnonneg u hu ord nf H.toEvidence).strategy
      d (clamp H.observed H.value x) ≠ 0) :
    ((solveConditioned (Selector.ordered id) κ hloc hnonneg u hu ord nf H.observed
        H.value).strategy d).kernel x =
      ((solveEvidenceWith (Selector.ordered id) κ hloc hnonneg u hu ord nf
        H.toEvidence).strategy d).kernel (clamp H.observed H.value x) :=
  (conditioned_policy H (independent_evidence H.toEvidence κ hclosed ord hloc hnorm) hclosed
    (nf.plan ord.no_self_info) (initialConditioned κ hloc hnonneg u hu H.observed H.value)
    (initialEvidence κ hloc hnonneg u hu H.toEvidence) defaultStrategy defaultStrategy
    (initial_coupled κ hclosed hloc hnonneg u hu H)
    (Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu H.toEvidence _))
    (Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu H.toEvidence _))
    d (Finset.mem_univ _) x).1 hx

/-- **Semantic first-label rule for Julia's evidence path.** On every row whose clamped
information row has positive reach under its own strategy, the conditioned driver chooses the
least action maximizing the conditional continuation value. -/
theorem solveConditioned_semantic (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (H : HardEvidence id) (d : id.D) (x : id.Assignment)
    (hx : reach κ H.toEvidence.likelihood
      (solveConditioned (Selector.ordered id) κ hloc hnonneg u hu ord nf H.observed
        H.value).strategy d (clamp H.observed H.value x) ≠ 0)
    (a : id.states (id.action d)) :
    ((solveConditioned (Selector.ordered id) κ hloc hnonneg u hu ord nf H.observed
        H.value).strategy d).kernel x a =
      if a = firstArgmax (continuation κ u H.toEvidence.likelihood
        (solveConditioned (Selector.ordered id) κ hloc hnonneg u hu ord nf H.observed
          H.value).strategy d (clamp H.observed H.value x))
      then 1 else 0 :=
  (conditioned_policy H (independent_evidence H.toEvidence κ hclosed ord hloc hnorm) hclosed
    (nf.plan ord.no_self_info) (initialConditioned κ hloc hnonneg u hu H.observed H.value)
    (initialEvidence κ hloc hnonneg u hu H.toEvidence) defaultStrategy defaultStrategy
    (initial_coupled κ hclosed hloc hnonneg u hu H)
    (Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu H.toEvidence _))
    (Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu H.toEvidence _))
    d (Finset.mem_univ _) x).2 hx a

end Ordered

end
end InfluenceDiagramsProofs.DVE
