import InfluenceDiagramsProofs.Finite.DVE.Approximate

/-!
# The expected-utility loss of near-optimal actions

`solveRepPlanWith_spec` and `solveRepPlanWith_approx_optimal` are about the run's **own**
strategy, which maximizes every score row exactly. A binary64 run can record, at a near-tie, an
action that is not a maximizer of the exact score row but whose exact score is within `τ` of the
row maximum. This module bounds the expected utility such a strategy loses.

**The scores.** The score row of a decision `d` (`decisionScoreRep`, `solveRepPlanScore`) is the
utility potential of `d`'s bucket at the moment the plan eliminates `d`'s action, read at an
information row. It is a *divided* utility: a chance elimination stores the ratio of summed
weight to summed mass, so the score is a conditional expected utility given the row, of the
bucket's part of the utility, assuming the decisions eliminated before `d` (the later ones in
time) play the exact run's policies. Losing `τ` on a row therefore loses `τ` times the row's
probability, and the rows of one decision partition the probability mass.

**The invariant (`TolInv`).** The proof follows the run, as `ApproxInv` does, against a normalised
reference kernel `κ` and a weight `lik` (`1` without evidence, the hard-evidence indicator with
it; rows are read at `clamp O o x`, the identity when `O = ∅`), but for an **arbitrary**
deterministic strategy `σ` on the eliminated decisions, given by one action function `g` per
decision. It keeps the mass envelope `[L, H]`, the utility bound `U`, a two-sided error `e` for
the chance eliminations, and the one-sided bound

`(W x - e - t) M_σ(x) ≤ V_σ(x)`,

where `W` is the run's utility potential, `M_σ` and `V_σ` the reference mass and value of the
eliminated part under `σ`, and `t` the accumulated loss. A decision step at which `g` is within
`τ` of the maximum of the run's own score row, on every row, adds `τ` to `t`
(`TolInv.decisionOf`); the run's own selector is the case `τ = 0`. This is the telescoping of a
performance-difference argument: the decisions are replaced one at a time in elimination order
(from the last in time to the first), each replacement losing at most `τ` times the total mass of
its rows, `τ M`. A chance step adds `(H / L - 1) U` to `e` (`TolInv.chanceOf`) and nothing to
`t`.

**Results** (`card D` is the number of decisions; a plan eliminates each exactly once,
`Plan.decisionCount_univ`):

* `solveRepPlan_tolerant`: for any selector, representative choice and plan, and any strategy
  `ρ` reading actions `g d x` with `score d x b ≤ score d x (g d x) + τ` on **every** row of the
  run's score (`solveRepPlanScore`), `value - e - card D * τ ≤ EU κ ρ`, with
  `e = approxGap k L H U` as in `solveRepPlanWith_approx`;
* `solveRepPlan_near_optimal`: hence `EU κ τ' ≤ EU κ ρ + 2 e + card D * τ` for every nonnegative
  `τ'`, and `optimalValue κ u - 2 e - card D * τ ≤ EU κ ρ`;
* `solveRepPlan_tolerant_optimal`: **the exactly normalised case** (`κ' = κ`): the loss is at most
  `card D * τ`, `optimalValue κ u - card D * τ ≤ EU κ ρ`.

The constant `card D` is the number of decision steps, each weighted by a total row mass of one;
the bound needs the row condition on every row, including rows the exact run's own strategy
reaches with probability zero, because the replaced later decisions change which rows are
reached. Everything is exact real arithmetic about the stated run and strategy.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

variable {id : FinInfluenceDiagram}

/-! ## Counting decisions -/

/-- The number of decision steps of a plan. -/
def Plan.decisionCount : {R : Finset id.V} → Plan id R → ℕ
  | _, .done => 0
  | _, .chance _ _ _ next => next.decisionCount
  | _, .decision _ _ _ next => next.decisionCount + 1

/-- A plan eliminates every decision whose action it contains exactly once. -/
theorem Plan.decisionCount_eq (hinj : Function.Injective id.action) {R : Finset id.V}
    (plan : Plan id R) :
    plan.decisionCount = (Finset.univ.filter fun d => id.action d ∈ R).card := by
  induction plan with
  | done => simp [Plan.decisionCount]
  | @chance R v hv hc next ih =>
    rw [Plan.decisionCount, ih]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    exact ⟨fun h => h.2, fun h => ⟨hc d, h⟩⟩
  | @decision R d hd hi next ih =>
    rw [Plan.decisionCount, ih]
    have hset : (Finset.univ.filter fun e => id.action e ∈ R.erase (id.action d)) =
        (Finset.univ.filter fun e => id.action e ∈ R).erase d := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨hne, he⟩
        exact ⟨fun h => hne (congrArg id.action h), he⟩
      · rintro ⟨hne, he⟩
        exact ⟨fun h => hne (hinj h), he⟩
    rw [hset, Finset.card_erase_of_mem (s := Finset.univ.filter fun e => id.action e ∈ R) (a := d)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩)]
    have : 0 < (Finset.univ.filter fun e => id.action e ∈ R).card :=
      Finset.card_pos.2 ⟨d, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩⟩
    omega

/-- A plan of all variables has one decision step per decision. -/
theorem Plan.decisionCount_univ (hinj : Function.Injective id.action)
    (plan : Plan id Finset.univ) : plan.decisionCount = Fintype.card id.D := by
  rw [Plan.decisionCount_eq hinj]
  simp

/-! ## Reference marginals with a weight -/

/-- The weighted utility `lik * U`. -/
def likUtil (lik : id.Assignment → ℝ) (u : Utility id ℝ) (y : id.Assignment) : ℝ :=
  lik y * totalUtility u y

theorem refMarg_nonneg_of (κ : id.Kernel ℝ) (hκ : ∀ m x a, 0 ≤ κ m x a) (R : Finset id.V)
    (σ : Strategy id ℝ) (hσ : σ.Nonneg) (F : id.Assignment → ℝ) (hF : ∀ y, 0 ≤ F y)
    (x : id.Assignment) : 0 ≤ refMarg κ R σ F x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (freeJoint_nonneg κ hκ _ σ hσ y) (hF y)

theorem clamp_empty (o x : id.Assignment) : clamp (∅ : Finset id.V) o x = x := by
  funext v
  simp [clamp]

/-- Summing out an unobserved chance variable, read at clamped rows. -/
theorem refMarg_unobserved (κ : id.Kernel ℝ) {R : Finset id.V} (σ : Strategy id ℝ)
    {O : Finset id.V} (o : id.Assignment) {v : id.V} (hv : v ∈ R) (hc : ∀ d, id.action d ≠ v)
    (hvO : v ∉ O) (F : id.Assignment → ℝ) (x : id.Assignment) :
    refMarg κ (R.erase v) σ F (clamp O o x) =
      ∑ b, refMarg κ R σ F (clamp O o (Function.update x v b)) := by
  rw [refMarg_chance κ σ F v hv hc]
  exact Finset.sum_congr rfl fun b _ => by rw [clamp_update o x hvO]

/-- Summing out an observed chance variable, read at clamped rows, keeps only the observed
state when the weight vanishes off it. -/
theorem refMarg_observed (κ : id.Kernel ℝ) {R : Finset id.V} (σ : Strategy id ℝ)
    {O : Finset id.V} (o : id.Assignment) {v : id.V} (hv : v ∈ R) (hc : ∀ d, id.action d ≠ v)
    (hvO : v ∈ O) (F : id.Assignment → ℝ) (hF : ∀ z, z v ≠ o v → F z = 0)
    (x : id.Assignment) :
    refMarg κ (R.erase v) σ F (clamp O o x) = refMarg κ R σ F (clamp O o x) := by
  rw [refMarg_chance κ σ F v hv hc, Finset.sum_eq_single (o v)]
  · rw [update_clamp_self o x hvO]
  · intro b _ hb
    unfold refMarg marg
    apply Finset.sum_eq_zero
    intro z hz
    have hzv : z v = b := by
      have := mem_fibre.1 hz v (by simpa using hv)
      simpa using this
    rw [hF z (by rw [hzv]; exact hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem nonneg_of_kernel (ρ : Strategy id ℝ)
    (g : (d : id.D) → id.Assignment → id.states (id.action d))
    (hρ : ∀ d x a, (ρ d).kernel x a = if a = g d x then 1 else 0) : ρ.Nonneg := by
  intro d x a
  rw [hρ]
  split_ifs <;> norm_num

/-! ## The invariant -/

/-- **The tolerant invariant** of a run state `s` against the normalised reference kernel `κ`,
the weight `lik` and the clamp `O, o`, for a strategy `σ` on the eliminated decisions: the mass
envelope, the utility bound, the one-sided realization bound with chance error `e` and decision
loss `t`, and dominance of every competitor with error `e`. -/
structure TolInv (κ : id.Kernel ℝ) (u : Utility id ℝ) (lik : id.Assignment → ℝ)
    (O : Finset id.V) (o : id.Assignment) (L H U e t : ℝ) {R : Finset id.V} (s : State id R)
    (σ : Strategy id ℝ) : Prop where
  nonneg : σ.Nonneg
  mass_lower : ∀ x, L * refMarg κ R σ lik (clamp O o x) ≤ (collect s.valuations).prob x
  mass_upper : ∀ x, (collect s.valuations).prob x ≤ H * refMarg κ R σ lik (clamp O o x)
  bounded : ∀ x, (collect s.valuations).prob x ≠ 0 → |(collect s.valuations).util x| ≤ U
  lower : ∀ x, ((collect s.valuations).util x - e - t) * refMarg κ R σ lik (clamp O o x) ≤
    refMarg κ R σ (likUtil lik u) (clamp O o x)
  dominates : ∀ τ : Strategy id ℝ, τ.Nonneg → ∀ x,
    refMarg κ R τ (likUtil lik u) (clamp O o x) ≤
      ((collect s.valuations).util x + e) * refMarg κ R σ lik (clamp O o x)

section Steps

variable {κ : id.Kernel ℝ} {u : Utility id ℝ} {lik : id.Assignment → ℝ} {O : Finset id.V}
  {o : id.Assignment} {L H U e t : ℝ}

/-- A larger chance error is still an error bound. -/
theorem TolInv.weaken (hκ : ∀ m x a, 0 ≤ κ m x a) (hlik : ∀ y, 0 ≤ lik y) {R : Finset id.V}
    {s : State id R} {σ : Strategy id ℝ} (h : TolInv κ u lik O o L H U e t s σ) {e' : ℝ}
    (he : e ≤ e') : TolInv κ u lik O o L H U e' t s σ := by
  have hM0 := refMarg_nonneg_of κ hκ R σ h.nonneg lik hlik
  refine ⟨h.nonneg, h.mass_lower, h.mass_upper, h.bounded, fun x => ?_, fun τ hτ x => ?_⟩
  · exact (mul_le_mul_of_nonneg_right (by linarith) (hM0 _)).trans (h.lower x)
  · exact (h.dominates τ hτ x).trans (mul_le_mul_of_nonneg_right (by linarith) (hM0 _))

/-- **An unobserved chance step adds `(H / L - 1) U` to the chance error.** -/
theorem TolInv.chanceOf (hκ : ∀ m x a, 0 ≤ κ m x a) (hlik : ∀ y, 0 ≤ lik y) (hL : 0 < L)
    (hU : 0 ≤ U) {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ}
    (h : TolInv κ u lik O o L H U e t s σ) (v : id.V) (hv : v ∈ R) (hc : ∀ d, id.action d ≠ v)
    (hvO : v ∉ O) (s' : State id (R.erase v))
    (hp : ∀ x, (collect s'.valuations).prob x =
      ∑ b, (collect s.valuations).prob (Function.update x v b))
    (hw : ∀ x, (collect s'.valuations).weight x =
      ∑ b, (collect s.valuations).weight (Function.update x v b)) :
    TolInv κ u lik O o L H U (e + (H / L - 1) * U) t s' σ := by
  set P := (collect s.valuations).prob
  set W := (collect s.valuations).util
  have hP0 : ∀ y, 0 ≤ P y := fun y => (collect s.valuations).nonneg y
  have hM0 := refMarg_nonneg_of κ hκ R σ h.nonneg lik hlik
  have havg : ∀ x, (∑ b, P (Function.update x v b)) * (collect s'.valuations).util x =
      ∑ b, P (Function.update x v b) * W (Function.update x v b) := by
    intro x
    have := hw x
    rw [weight, hp] at this
    simpa only [weight] using this
  have hre : ∀ x, |∑ b, W (Function.update x v b) *
        refMarg κ R σ lik (clamp O o (Function.update x v b)) -
      (collect s'.valuations).util x *
        ∑ b, refMarg κ R σ lik (clamp O o (Function.update x v b))| ≤
      (H / L - 1) * U * ∑ b, refMarg κ R σ lik (clamp O o (Function.update x v b)) := fun x =>
    reweight_error (fun b => P (Function.update x v b))
      (fun b => refMarg κ R σ lik (clamp O o (Function.update x v b)))
      (fun b => W (Function.update x v b)) _ L H U hL (fun b => hM0 _)
      (fun b => h.mass_lower _) (fun b => h.mass_upper _) (fun b hb => h.bounded _ hb) hU
      (havg x)
  refine ⟨h.nonneg, fun x => ?_, fun x => ?_, fun x hx => ?_, fun x => ?_, fun τ hτ x => ?_⟩
  · rw [refMarg_unobserved κ σ o hv hc hvO, hp, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => h.mass_lower _
  · rw [refMarg_unobserved κ σ o hv hc hvO, hp, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => h.mass_upper _
  · have hpos : 0 < ∑ b, P (Function.update x v b) := by
      rw [← hp]
      exact lt_of_le_of_ne ((collect s'.valuations).nonneg x) (Ne.symm hx)
    have hb : |∑ b, P (Function.update x v b) * W (Function.update x v b)| ≤
        U * ∑ b, P (Function.update x v b) := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [abs_mul, abs_of_nonneg (hP0 _), mul_comm]
      by_cases hz : P (Function.update x v b) = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_right (h.bounded _ hz) (hP0 _)
    rw [← havg x, abs_mul, abs_of_pos hpos, mul_comm] at hb
    exact le_of_mul_le_mul_right hb hpos
  · rw [refMarg_unobserved κ σ o hv hc hvO, refMarg_unobserved κ σ o hv hc hvO]
    set S := ∑ b, refMarg κ R σ lik (clamp O o (Function.update x v b))
    set A := ∑ b, W (Function.update x v b) *
      refMarg κ R σ lik (clamp O o (Function.update x v b))
    have h1 : ∑ b, (W (Function.update x v b) - e - t) *
        refMarg κ R σ lik (clamp O o (Function.update x v b)) ≤
        ∑ b, refMarg κ R σ (likUtil lik u) (clamp O o (Function.update x v b)) :=
      Finset.sum_le_sum fun b _ => h.lower _
    have h3 : ∑ b, (W (Function.update x v b) - e - t) *
        refMarg κ R σ lik (clamp O o (Function.update x v b)) = A - (e + t) * S := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    have h2 := (abs_le.1 (hre x)).1
    have hexp : ((collect s'.valuations).util x - (e + (H / L - 1) * U) - t) * S =
        (collect s'.valuations).util x * S - (H / L - 1) * U * S - (e + t) * S := by ring
    rw [hexp]
    linarith
  · rw [refMarg_unobserved κ τ o hv hc hvO, refMarg_unobserved κ σ o hv hc hvO]
    set S := ∑ b, refMarg κ R σ lik (clamp O o (Function.update x v b))
    set A := ∑ b, W (Function.update x v b) *
      refMarg κ R σ lik (clamp O o (Function.update x v b))
    have h1 : ∑ b, refMarg κ R τ (likUtil lik u) (clamp O o (Function.update x v b)) ≤
        A + e * S := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun b _ => by
        have := h.dominates τ hτ (Function.update x v b)
        linarith
    have h2 := (abs_le.1 (hre x)).2
    have hexp : ((collect s'.valuations).util x + (e + (H / L - 1) * U)) * S =
        (collect s'.valuations).util x * S + (H / L - 1) * U * S + e * S := by ring
    rw [hexp]
    linarith

/-- **An observed chance step changes nothing**: the run skips it, and the reference keeps only
the observed state, since the weight vanishes off it. -/
theorem TolInv.observed (hlik : ∀ z, ∀ v ∈ O, z v ≠ o v → lik z = 0) {R : Finset id.V}
    {s : State id R} {σ : Strategy id ℝ} (h : TolInv κ u lik O o L H U e t s σ) (v : id.V)
    (hv : v ∈ R) (hc : ∀ d, id.action d ≠ v) (hvO : v ∈ O) (s' : State id (R.erase v))
    (hp : ∀ x, (collect s'.valuations).prob x = (collect s.valuations).prob x)
    (hu : ∀ x, (collect s'.valuations).util x = (collect s.valuations).util x) :
    TolInv κ u lik O o L H U e t s' σ := by
  have hm : ∀ (τ : Strategy id ℝ) x,
      refMarg κ (R.erase v) τ lik (clamp O o x) = refMarg κ R τ lik (clamp O o x) :=
    fun τ x => refMarg_observed κ τ o hv hc hvO lik (fun z hz => hlik z v hvO hz) x
  have hn : ∀ (τ : Strategy id ℝ) x,
      refMarg κ (R.erase v) τ (likUtil lik u) (clamp O o x) =
        refMarg κ R τ (likUtil lik u) (clamp O o x) :=
    fun τ x => refMarg_observed κ τ o hv hc hvO _
      (fun z hz => by rw [likUtil, hlik z v hvO hz, zero_mul]) x
  refine ⟨h.nonneg, fun x => ?_, fun x => ?_, fun x hx => ?_, fun x => ?_, fun τ hτ x => ?_⟩
  · rw [hm, hp]
    exact h.mass_lower x
  · rw [hm, hp]
    exact h.mass_upper x
  · rw [hu]
    exact h.bounded x (by rwa [← hp])
  · rw [hm, hn, hu]
    exact h.lower x
  · rw [hm, hn, hu]
    exact h.dominates τ hτ x

/-- **A decision step adds the tolerance `τ` to the loss** when the policy `π` of the step reads
an action `g` within `τ` of the maximum of the run's bucket score, on every row. With the run's
own maximizing selector, `τ = 0`. -/
theorem TolInv.decisionOf (hκ : ∀ m x a, 0 ≤ κ m x a) (hlik : ∀ y, 0 ≤ lik y)
    (hind : Independent κ lik) (hinj : Function.Injective id.action) (hL : 0 < L)
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ}
    (h : TolInv κ u lik O o L H U e t s σ) (d : id.D) (hd : id.action d ∈ R)
    (hi : R.erase (id.action d) = id.info d) (haO : id.action d ∉ O)
    (hsc : ∀ w ∈ (collect s.valuations).scope, w ∉ O) (π : Policy id ℝ d)
    (g : id.Assignment → id.states (id.action d))
    (hπ : ∀ x b, π.kernel x b = if b = g x then 1 else 0) (τ : ℝ)
    (hmax : ∀ x b, bucketScore s.valuations (id.action d) x b ≤
      bucketScore s.valuations (id.action d) x (g x) + τ) :
    TolInv κ u lik O o L H U e (t + τ) (s.decision d) (Function.update σ d π) := by
  have hn : id.action d ∉ Rᶜ := by simpa using hd
  have hinfo := info_disjoint d hi
  set P := (collect s.valuations).prob
  set W := (collect s.valuations).util
  have hM0 := refMarg_nonneg_of κ hκ R σ h.nonneg lik hlik
  have heval : ∀ (F : id.Assignment → ℝ) (z : id.Assignment),
      refMarg κ (R.erase (id.action d)) (Function.update σ d π) F z =
        refMarg κ R σ F (Function.update z (id.action d) (g z)) := by
    intro F z
    unfold refMarg
    rw [compl_erase, decision_marginal κ Rᶜ σ hinj d hn hinfo]
    simp [hπ, ite_mul]
  have hM : ∀ z b, refMarg κ R σ lik (Function.update z (id.action d) b) = refMarg κ R σ lik z :=
    fun z b => hind Rᶜ σ d hn (by simpa using information_boundary d hi) z b
  have hcl : ∀ x b, clamp O o (Function.update x (id.action d) b) =
      Function.update (clamp O o x) (id.action d) b :=
    fun x b => clamp_update o x haO b
  have hsclamp : ∀ x, bucketScore s.valuations (id.action d) (clamp O o x) =
      bucketScore s.valuations (id.action d) x := by
    intro x
    funext b
    unfold bucketScore
    apply (collect (bucket (id.action d) s.valuations)).util_local
    intro w hw
    by_cases hwa : w = (id.action d)
    · subst hwa
      simp
    · rw [Function.update_of_ne hwa, Function.update_of_ne hwa]
      have hwO : w ∉ O := hsc w (filter_scope_subset _ s.valuations hw)
      simp [clamp, hwO]
  have hWnew : ∀ x, (collect (s.decision d).valuations).util x =
      W (Function.update x (id.action d)
        (choice (id.action d) (collect (bucket (id.action d) s.valuations)) x)) :=
    fun x => decisionStep_util_eq (id.action d) s.valuations x
  have hWmax : ∀ x b, W (Function.update x (id.action d) b) ≤
      (collect (s.decision d).valuations).util x := by
    intro x b
    rw [hWnew]
    show (collect s.valuations).util _ ≤ (collect s.valuations).util _
    rw [util_update_eq_score, util_update_eq_score]
    exact add_le_add (le_argmax (bucketScore s.valuations (id.action d) x) b) le_rfl
  have hgood : ∀ x, (collect (s.decision d).valuations).util x ≤
      W (Function.update x (id.action d) (g (clamp O o x))) + τ := by
    intro x
    rw [hWnew]
    show (collect s.valuations).util _ ≤ (collect s.valuations).util _ + τ
    rw [util_update_eq_score, util_update_eq_score]
    have := hmax (clamp O o x)
      (choice (id.action d) (collect (bucket (id.action d) s.valuations)) x)
    rw [hsclamp] at this
    linarith
  have hprob : ∀ x, (collect (s.decision d).valuations).prob x =
      P (Function.update x (id.action d)
        (probabilityChoice (id.action d) (collect (bucket (id.action d) s.valuations)) x)) :=
    fun x => decisionStep_prob_eq (id.action d) s.valuations x
  have hmass : ∀ x, refMarg κ (R.erase (id.action d)) (Function.update σ d π) lik (clamp O o x) =
      refMarg κ R σ lik (clamp O o x) := fun x => by rw [heval, hM]
  refine ⟨?_, fun x => ?_, fun x => ?_, fun x hx => ?_, fun x => ?_, fun τ' hτ' x => ?_⟩
  · intro e' y b
    by_cases he : e' = d
    · subst he
      rw [Function.update_self, hπ]
      split_ifs <;> norm_num
    · rw [Function.update_of_ne he]
      exact h.nonneg e' y b
  · rw [hmass, hprob]
    have := h.mass_lower (Function.update x (id.action d)
      (probabilityChoice (id.action d) (collect (bucket (id.action d) s.valuations)) x))
    rwa [hcl, hM] at this
  · rw [hmass, hprob]
    have := h.mass_upper (Function.update x (id.action d)
      (probabilityChoice (id.action d) (collect (bucket (id.action d) s.valuations)) x))
    rwa [hcl, hM] at this
  · rw [hprob] at hx
    rw [hWnew]
    apply h.bounded
    have hpos : 0 < P (Function.update x (id.action d)
        (probabilityChoice (id.action d) (collect (bucket (id.action d) s.valuations)) x)) :=
      lt_of_le_of_ne ((collect s.valuations).nonneg _) (Ne.symm hx)
    have hmpos : 0 < refMarg κ R σ lik (clamp O o x) := by
      have := h.mass_upper (Function.update x (id.action d)
        (probabilityChoice (id.action d) (collect (bucket (id.action d) s.valuations)) x))
      rw [hcl, hM] at this
      rcases (hM0 (clamp O o x)).lt_or_eq with hlt | heq
      · exact hlt
      · rw [← heq, mul_zero] at this
        exact absurd (lt_of_lt_of_le hpos this) (lt_irrefl 0)
    have := h.mass_lower (Function.update x (id.action d)
      (choice (id.action d) (collect (bucket (id.action d) s.valuations)) x))
    rw [hcl, hM] at this
    exact ne_of_gt (lt_of_lt_of_le (mul_pos hL hmpos) this)
  · rw [hmass, heval]
    have h1 := h.lower (Function.update x (id.action d) (g (clamp O o x)))
    rw [hcl, hM] at h1
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_right (by linarith [hgood x]) (hM0 _)
  · have hc := decision_marginal κ Rᶜ τ' hinj d hn hinfo (τ' d) (likUtil lik u) (clamp O o x)
    simp only [Function.update_eq_self] at hc
    have hlhs : refMarg κ (R.erase (id.action d)) τ' (likUtil lik u) (clamp O o x) =
        ∑ b, (τ' d).kernel (clamp O o x) b *
          refMarg κ R τ' (likUtil lik u) (Function.update (clamp O o x) (id.action d) b) := by
      unfold refMarg
      rw [compl_erase]
      exact hc
    rw [hlhs, hmass]
    calc ∑ b, (τ' d).kernel (clamp O o x) b *
          refMarg κ R τ' (likUtil lik u) (Function.update (clamp O o x) (id.action d) b)
        ≤ ∑ b, (τ' d).kernel (clamp O o x) b *
            (((collect (s.decision d).valuations).util x + e) *
              refMarg κ R σ lik (clamp O o x)) := by
          refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hτ' d _ b)
          have := h.dominates τ' hτ' (Function.update x (id.action d) b)
          rw [hcl, hM] at this
          exact this.trans (mul_le_mul_of_nonneg_right (by linarith [hWmax x b]) (hM0 _))
      _ = _ := by rw [← Finset.sum_mul, (τ' d).normalised, one_mul]

/-- **The invariant at the start of a run**: no error and no loss yet, for any nonnegative
strategy, when the run's initial mass is the run kernel's joint weight and its utility the total
utility, both read at `clamp O o x`, and the weight is one there. -/
theorem TolInv.initial (κ' : id.Kernel ℝ) (hlik1 : ∀ x, lik (clamp O o x) = 1)
    (s : State id Finset.univ)
    (hP : ∀ x, (collect s.valuations).prob x =
      ∏ m, κ' m (clamp O o x) (clamp O o x (id.target m)))
    (hW : ∀ x, (collect s.valuations).util x = totalUtility u (clamp O o x))
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U) (σ : Strategy id ℝ) (hσ : σ.Nonneg) :
    TolInv κ u lik O o L H U 0 0 s σ := by
  refine ⟨hσ, fun x => ?_, fun x => ?_, fun x _ => ?_, fun x => ?_, fun τ _ x => ?_⟩
  · rw [refMarg_univ, hlik1, mul_one, hP]
    exact (henv _).1
  · rw [refMarg_univ, hlik1, mul_one, hP]
    exact (henv _).2
  · rw [hW]
    exact hUb _
  · rw [refMarg_univ, refMarg_univ, hW, likUtil, hlik1]
    exact le_of_eq (by ring)
  · rw [refMarg_univ, refMarg_univ, hW, likUtil, hlik1]
    exact le_of_eq (by ring)

end Steps

/-! ## The run without evidence -/

/-- **The invariant along the representative run**, without evidence, for a fixed strategy `ρ`
whose action `g d` at every remaining decision `d` is within `τ` of the maximum of the run's
score of `d` on every row. -/
theorem tolInv_runRep (keep : id.V → Bool) {κ : id.Kernel ℝ} (hκ : ∀ m x a, 0 ≤ κ m x a)
    {lik : id.Assignment → ℝ} (hlik : ∀ y, 0 ≤ lik y) (hind : Independent κ lik)
    (hinj : Function.Injective id.action) {u : Utility id ℝ} {o : id.Assignment} {L H U : ℝ}
    (hL : 0 < L) (hU : 0 ≤ U) {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (ρ : Strategy id ℝ) (τ : ℝ)
    (hρ : ∀ d, id.action d ∈ R → ∃ g : id.Assignment → id.states (id.action d),
      (∀ x a, (ρ d).kernel x a = if a = g x then 1 else 0) ∧
        ∀ x b, decisionScoreRep keep plan s d x b ≤ decisionScoreRep keep plan s d x (g x) + τ)
    (e t : ℝ) (h : TolInv κ u lik ∅ o L H U e t s ρ) :
    TolInv κ u lik ∅ o L H U (e + plan.chanceCount * ((H / L - 1) * U))
      (t + plan.decisionCount * τ) (runRepState keep plan s) ρ := by
  induction plan generalizing e t with
  | done => simpa [Plan.chanceCount, Plan.decisionCount, runRepState] using h
  | @chance R v hv hc next ih =>
    have hs : TolInv κ u lik ∅ o L H U (e + (H / L - 1) * U) t (s.chanceKeep keep v) ρ := by
      obtain ⟨hp, hw⟩ := chanceStepKeep_collect (keep v) v s.valuations
      refine h.chanceOf hκ hlik hL hU v hv hc (Finset.notMem_empty v) _ (fun x => ?_)
        (fun x => ?_)
      · change (collect (chanceStepKeep (keep v) v s.valuations)).prob x = _
        rw [hp]
        exact chanceStep_prob v s.valuations x
      · change (collect (chanceStepKeep (keep v) v s.valuations)).weight x = _
        rw [hw]
        exact chanceStep_weight v s.valuations x
    have := ih (s.chanceKeep keep v) (fun d hd => hρ d (Finset.mem_of_mem_erase hd)) _ _ hs
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
          else decisionScoreRep keep next (s.decision d) d) x b ≤
        (if d = d then bucketScore s.valuations (id.action d)
          else decisionScoreRep keep next (s.decision d) d) x (g x) + τ at this
      rwa [if_pos rfl] at this
    have hs := h.decisionOf hκ hlik hind hinj hL d hd hi (Finset.notMem_empty _)
      (fun w _ => Finset.notMem_empty w) (ρ d) g hgk τ hmax
    rw [Function.update_eq_self] at hs
    have hρ' : ∀ d', id.action d' ∈ R.erase (id.action d) →
        ∃ g' : id.Assignment → id.states (id.action d'),
          (∀ x a, (ρ d').kernel x a = if a = g' x then 1 else 0) ∧
            ∀ x b, decisionScoreRep keep next (s.decision d) d' x b ≤
              decisionScoreRep keep next (s.decision d) d' x (g' x) + τ := by
      intro d' hd'
      have hne : d ≠ d' := fun he => (Finset.mem_erase.1 hd').1 (by rw [he])
      obtain ⟨g', hk', hm'⟩ := hρ d' (Finset.mem_of_mem_erase hd')
      refine ⟨g', hk', fun x b => ?_⟩
      have := hm' x b
      change (if d = d' then bucketScore s.valuations (id.action d')
          else decisionScoreRep keep next (s.decision d) d') x b ≤
        (if d = d' then bucketScore s.valuations (id.action d')
          else decisionScoreRep keep next (s.decision d) d') x (g' x) + τ at this
      rwa [if_neg hne] at this
    have := ih (s.decision d) hρ' _ _ hs
    simp only [Plan.chanceCount, Plan.decisionCount, Nat.cast_add, Nat.cast_one] at this ⊢
    convert this using 1
    ring

/-- The final reference quantities without evidence: total mass one and expected utility. -/
theorem refMarg_empty_one (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (u : Utility id ℝ) (σ : Strategy id ℝ)
    (x : id.Assignment) :
    refMarg κ ∅ σ (fun _ => 1) x = 1 ∧
      refMarg κ ∅ σ (likUtil (fun _ => 1) u) x = expectedUtility κ σ u := by
  constructor
  · rw [refMarg_empty]
    simpa only [mul_one] using sum_joint_instantiate_eq_one κ σ hclosed ord hloc hnorm
  · rw [refMarg_empty]
    simp only [likUtil, one_mul]
    rfl

/-- **The tolerant strategy's expected utility**, without evidence. For any selector,
representative choice and plan of the run on `κ'`, and any strategy `ρ` that reads at every
decision `d` an action `g d x` within `τ` of the maximum of the run's score row
(`solveRepPlanScore`) on every row, the reference expected utility of `ρ` is at least the run's
value minus the chance error `e = approxGap k L H U` minus `card D * τ`. -/
theorem solveRepPlan_tolerant (sel : Selector id) (keep : id.V → Bool) (κ κ' : id.Kernel ℝ)
    (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (hloc' : ∀ m, Local κ' m)
    (hnonneg' : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) (L H U : ℝ) (hL : 0 < L) (hU : 0 ≤ U)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U) (ρ : Strategy id ℝ)
    (g : (d : id.D) → id.Assignment → id.states (id.action d))
    (hρ : ∀ d x a, (ρ d).kernel x a = if a = g d x then 1 else 0) (τ : ℝ)
    (hg : ∀ d x b, solveRepPlanScore keep κ' hloc' hnonneg' u hu plan d x b ≤
      solveRepPlanScore keep κ' hloc' hnonneg' u hu plan d x (g d x) + τ) :
    (solveRepPlanWith sel keep κ' hloc' hnonneg' u hu plan).value -
        approxGap plan.chanceCount L H U - Fintype.card id.D * τ ≤
      expectedUtility κ ρ u := by
  have hinj := (id.closed_iff.1 hclosed).2.1
  have hind := independent_one κ hclosed ord hloc hnorm
  have hρn := nonneg_of_kernel ρ g hρ
  have h0 : TolInv κ u (fun _ => 1) ∅ (baseAssignment id) L H U 0 0
      (initial κ' hloc' hnonneg' u hu) ρ :=
    TolInv.initial κ' (fun _ => rfl) _
      (fun x => by rw [initial_prob, clamp_empty])
      (fun x => by rw [initial_util, clamp_empty]) henv hUb ρ hρn
  have hr := tolInv_runRep keep hnonneg (fun _ => zero_le_one) hind hinj hL hU plan _ ρ τ
    (fun d _ => ⟨g d, hρ d, hg d⟩) 0 0 h0
  have hl := hr.lower (baseAssignment id)
  rw [clamp_empty, (refMarg_empty_one κ hclosed ord hloc hnorm u ρ _).1,
    (refMarg_empty_one κ hclosed ord hloc hnorm u ρ _).2, mul_one,
    Plan.decisionCount_univ hinj] at hl
  have hv : (solveRepPlanWith sel keep κ' hloc' hnonneg' u hu plan).value =
      (collect (runRepState keep plan (initial κ' hloc' hnonneg' u hu)).valuations).util
        (baseAssignment id) := by
    unfold solveRepPlanWith
    simp only
    rw [runRepWith_state]
  rw [hv]
  unfold approxGap
  linarith

/-- **Near-optimality of a tolerant strategy**, without evidence. Under the hypotheses of
`solveRepPlan_tolerant` and with `e = approxGap k L H U`: every nonnegative strategy's reference
expected utility exceeds `ρ`'s by at most `2 e + card D * τ`, and `ρ` is within
`2 e + card D * τ` of the reference optimum. -/
theorem solveRepPlan_near_optimal (sel : Selector id) (keep : id.V → Bool) (κ κ' : id.Kernel ℝ)
    (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (hloc' : ∀ m, Local κ' m)
    (hnonneg' : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) (L H U : ℝ) (hL : 0 < L) (hU : 0 ≤ U)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U) (ρ : Strategy id ℝ)
    (g : (d : id.D) → id.Assignment → id.states (id.action d))
    (hρ : ∀ d x a, (ρ d).kernel x a = if a = g d x then 1 else 0) (τ : ℝ)
    (hg : ∀ d x b, solveRepPlanScore keep κ' hloc' hnonneg' u hu plan d x b ≤
      solveRepPlanScore keep κ' hloc' hnonneg' u hu plan d x (g d x) + τ) :
    let e := approxGap plan.chanceCount L H U
    (∀ τ' : Strategy id ℝ, τ'.Nonneg →
        expectedUtility κ τ' u ≤ expectedUtility κ ρ u + 2 * e + Fintype.card id.D * τ) ∧
      optimalValue κ u - 2 * e - Fintype.card id.D * τ ≤ expectedUtility κ ρ u := by
  intro e
  have ht := solveRepPlan_tolerant sel keep κ κ' hclosed ord hloc hnorm hnonneg hloc' hnonneg' u
    hu plan L H U hL hU henv hUb ρ g hρ τ hg
  obtain ⟨-, -, hdom⟩ := solveRepPlanWith_approx sel keep κ κ' hclosed ord hloc hnorm hnonneg
    hloc' hnonneg' u hu plan L H U hL hU henv hUb
  have hall : ∀ τ' : Strategy id ℝ, τ'.Nonneg →
      expectedUtility κ τ' u ≤ expectedUtility κ ρ u + 2 * e + Fintype.card id.D * τ := by
    intro τ' hτ'
    have := hdom τ' hτ'
    change _ ≤ _ + e at this
    change _ - e - _ ≤ _ at ht
    linarith
  refine ⟨hall, ?_⟩
  obtain ⟨σo, _, hσo, hvo⟩ := optimalValue_attained κ u
  have := hall σo hσo
  rw [hvo] at this
  linarith

/-- **The exactly normalised case**: if the run is on the normalised kernel `κ` itself, a
strategy whose actions are within `τ` of every row maximum of the run's score loses at most
`card D * τ` in expected utility: it is within `card D * τ` of every nonnegative strategy and
of the optimum. -/
theorem solveRepPlan_tolerant_optimal (sel : Selector id) (keep : id.V → Bool)
    (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (plan : Plan id Finset.univ) (ρ : Strategy id ℝ)
    (g : (d : id.D) → id.Assignment → id.states (id.action d))
    (hρ : ∀ d x a, (ρ d).kernel x a = if a = g d x then 1 else 0) (τ : ℝ)
    (hg : ∀ d x b, solveRepPlanScore keep κ hloc hnonneg u hu plan d x b ≤
      solveRepPlanScore keep κ hloc hnonneg u hu plan d x (g d x) + τ) :
    (∀ τ' : Strategy id ℝ, τ'.Nonneg →
        expectedUtility κ τ' u ≤ expectedUtility κ ρ u + Fintype.card id.D * τ) ∧
      optimalValue κ u - Fintype.card id.D * τ ≤ expectedUtility κ ρ u := by
  set U := ∑ x, |totalUtility u x|
  have hU : 0 ≤ U := Finset.sum_nonneg fun x _ => abs_nonneg _
  have hUb : ∀ x, |totalUtility u x| ≤ U := fun x =>
    Finset.single_le_sum (f := fun x => |totalUtility u x|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ x)
  have henv : ∀ x, 1 * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ m x (x (id.target m)) ∧
      ∏ m, κ m x (x (id.target m)) ≤ 1 * ∏ m, κ m x (x (id.target m)) :=
    fun x => ⟨le_of_eq (one_mul _), le_of_eq (one_mul _).symm⟩
  have h := solveRepPlan_near_optimal sel keep κ κ hclosed ord hloc hnorm hnonneg hloc hnonneg u
    hu plan 1 1 U one_pos hU henv hUb ρ g hρ τ hg
  have h0 : approxGap plan.chanceCount 1 1 U = 0 := by simp [approxGap]
  simp only [h0, mul_zero, add_zero, sub_zero] at h
  exact h

end
end InfluenceDiagramsProofs.DVE
