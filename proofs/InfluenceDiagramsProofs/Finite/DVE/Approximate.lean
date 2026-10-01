import InfluenceDiagramsProofs.Finite.DVE.Representative

/-!
# Approximate optimality of the exact DVE run on approximately normalised kernels

`solve_spec`, `solveWith_spec` and `solveRepPlanWith_spec` need every chance row to sum to one.
This module drops that hypothesis. The run is the exact DVE run (`runRepWith`: any maximizing
selector, any representative choice `keep`, any plan) on a kernel `κ` whose rows need not sum to
one. Its decisions are compared with a **reference model** `κ̂` that is normalised: the run's
joint weight is the reference joint times a factor in `[L, H]`,

`L * ∏ m, κ̂ m x (x (target m)) ≤ ∏ m, κ m x (x (target m)) ≤ H * ∏ m, κ̂ m x (x (target m))`,

with `0 < L ≤ H`, and every total utility satisfies `|U x| ≤ U`. Policies are not rows of `κ`:
they are the strategy's, normalised by `Policy.normalised`, so `L` and `H` are about the chance
mechanisms only.

**Why the bound is not `2 (H - 1) U`.** The run does not maximise the unnormalised expected
utility `∑ x, (∏ κ) (∏ δ) U`: a chance elimination stores the ratio of summed weight to summed
mass, so a row-sum factor of a mechanism is divided out at the elimination of its target, while
the factors carried by the eliminated part re-weight later averages; and the mass a decision
step keeps is read at the action maximizing the probability potential, not at the chosen one.
With a decision `D` and a child `X` of `D` whose rows sum to `s_a`, the run chooses the action
maximizing `E_{κ̂(·|a)}[U]`, the unnormalised score of `a` is `s_a E_{κ̂(·|a)}[U]`, and the two
maximizers differ. So the argument "the run maximizes the unnormalised score, which is within
`(H - 1) U` of the reference expected utility for every policy" does not apply to the run.

**What is proved instead (`ApproxInv`).** For the reference marginals of the eliminated part
(`refMarg`), the run's probability potential stays within `[L, H]` times the reference mass, its
utility potential stays bounded by `U` on rows of positive mass, and the reference continuation
value of the run's partial strategy, and of every competitor, stays within `e` of the run's
utility potential. Decision steps add nothing to `e` (the reference mass does not depend on the
free action, `probability_independent`). A chance elimination averages the stored utilities with
the run's masses instead of the reference masses; since both are within `[L, H]` of each other,
it adds at most `(H / L - 1) U` (`reweight_error`). Hence, with `k` chance eliminations in the
plan (`Plan.chanceCount`, the number of chance variables, `Plan.chanceCount_eq`), and
`e = k (H / L - 1) U` (`approxGap`):

* `solveRepPlanWith_approx`: the returned strategy is deterministic,
  `|EU κ̂ σ* - value| ≤ e`, and `EU κ̂ τ ≤ value + e` for every nonnegative strategy `τ`;
* `solveRepPlanWith_approx_optimal`: `EU κ̂ τ ≤ EU κ̂ σ* + 2 e` for every nonnegative `τ`,
  `optimalValue κ̂ u - 2 e ≤ EU κ̂ σ* ≤ optimalValue κ̂ u`, and `|value - optimalValue κ̂ u| ≤ e`.

With `κ = κ̂` and `L = H = 1` the gap is `0` and these are `solveRepPlanWith_spec`'s
conclusions. Everything is exact real arithmetic about the stated run: not a statement about a
Float64 run.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

/-! ## A finite re-weighting lemma -/

/-- **Averaging with perturbed weights.** If `P b` is within `[L, H]` of `M b ≥ 0`, `w b` is
bounded by `U` where `P b ≠ 0`, and `w'` is the `P`-weighted average of `w`, then the
`M`-weighted sum of `w` differs from `w' * ∑ M` by at most `(H / L - 1) U ∑ M`. -/
theorem reweight_error {B : Type} [Fintype B] (P M w : B → ℝ) (w' L H U : ℝ)
    (hL : 0 < L) (hM : ∀ b, 0 ≤ M b) (hlo : ∀ b, L * M b ≤ P b) (hhi : ∀ b, P b ≤ H * M b)
    (hw : ∀ b, P b ≠ 0 → |w b| ≤ U) (hU : 0 ≤ U)
    (hw' : (∑ b, P b) * w' = ∑ b, P b * w b) :
    |∑ b, w b * M b - w' * ∑ b, M b| ≤ (H / L - 1) * U * ∑ b, M b := by
  set S := ∑ b, M b with hSdef
  set T := ∑ b, P b with hTdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun b _ => hM b
  have hTlo : L * S ≤ T := by
    rw [hSdef, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => hlo b
  have hThi : T ≤ H * S := by
    rw [hSdef, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => hhi b
  rcases hS.lt_or_eq with hSpos | hS0
  · have hTpos : 0 < T := lt_of_lt_of_le (mul_pos hL hSpos) hTlo
    have hLH : L ≤ H := le_of_mul_le_mul_right (hTlo.trans hThi) hSpos
    have hkey : T * (∑ b, w b * M b - w' * S) = ∑ b, w b * (T * M b - S * P b) := by
      have h1 : T * (w' * S) = S * ∑ b, P b * w b := by rw [← hw']; ring
      rw [mul_sub, h1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hterm : ∀ b, |w b * (T * M b - S * P b)| ≤ U * ((H - L) * S * M b) := by
      intro b
      by_cases hP : P b = 0
      · have hMb : M b = 0 := by
          have h := hlo b
          rw [hP] at h
          exact le_antisymm (by nlinarith [hM b]) (hM b)
        rw [hP, hMb]
        simp
      · rw [abs_mul]
        refine mul_le_mul (hw b hP) ?_ (abs_nonneg _) hU
        have h1 := mul_nonneg (sub_nonneg.2 hThi) (hM b)
        have h2 := mul_nonneg (sub_nonneg.2 (hlo b)) hS
        have h3 := mul_nonneg (sub_nonneg.2 hTlo) (hM b)
        have h4 := mul_nonneg (sub_nonneg.2 (hhi b)) hS
        rw [abs_le]
        constructor <;> nlinarith
    have hsum : T * |∑ b, w b * M b - w' * S| ≤ T * ((H / L - 1) * U * S) := by
      rw [← abs_of_pos hTpos, ← abs_mul, abs_of_pos hTpos, hkey]
      calc |∑ b, w b * (T * M b - S * P b)|
          ≤ ∑ b, |w b * (T * M b - S * P b)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ b, U * ((H - L) * S * M b) := Finset.sum_le_sum fun b _ => hterm b
        _ = U * (H - L) * S * S := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, hSdef]
          ring
        _ ≤ T * ((H / L - 1) * U * S) := by
          have hHL : (H / L - 1) * L = H - L := by field_simp
          have hc : 0 ≤ (H / L - 1) * U * S := by
            refine mul_nonneg (mul_nonneg ?_ hU) hS
            rw [sub_nonneg, le_div_iff₀ hL, one_mul]
            exact hLH
          calc U * (H - L) * S * S = ((H / L - 1) * U * S) * (L * S) := by
                rw [← hHL]; ring
            _ ≤ ((H / L - 1) * U * S) * T := mul_le_mul_of_nonneg_left hTlo hc
            _ = T * ((H / L - 1) * U * S) := by ring
    exact le_of_mul_le_mul_left hsum hTpos
  · have hMz : ∀ b, M b = 0 := fun b =>
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hM b).1 hS0.symm b (Finset.mem_univ b)
    rw [← hS0]
    simp [hMz]

/-! ## Decision steps without probability independence -/

section Steps

variable {bn : FinBayesNet}

/-- The probability potential after a decision step, read at the probability maximizer. -/
theorem decisionStep_prob_eq (a : bn.V) (vs : List (Valuation bn)) (x : bn.Assignment) :
    (collect (decisionStep a vs)).prob x =
      (collect vs).prob (Function.update x a (probabilityChoice a (collect (bucket a vs)) x)) := by
  rw [(collect_partition a vs _).1, prob_update_of_notMem _ (outside_notMem a vs)]
  rfl

/-- The utility potential after a decision step, read at the utility maximizer. -/
theorem decisionStep_util_eq (a : bn.V) (vs : List (Valuation bn)) (x : bn.Assignment) :
    (collect (decisionStep a vs)).util x =
      (collect vs).util (Function.update x a (choice a (collect (bucket a vs)) x)) := by
  rw [(collect_partition a vs _).2, util_update_of_notMem _ (outside_notMem a vs)]
  rfl

end Steps

variable {id : FinInfluenceDiagram}

/-! ## The reference marginals -/

/-- The reference marginal of `F` over the eliminated variables `Rᶜ`, with the strategy `σ` on
the eliminated decisions. -/
def refMarg (κ : id.Kernel ℝ) (R : Finset id.V) (σ : Strategy id ℝ) (F : id.Assignment → ℝ)
    (x : id.Assignment) : ℝ :=
  marg Rᶜ (fun y => freeJoint κ Rᶜ σ y * F y) x

theorem refMarg_mass_nonneg (κ : id.Kernel ℝ) (hκ : ∀ m x a, 0 ≤ κ m x a) (R : Finset id.V)
    (σ : Strategy id ℝ) (hσ : σ.Nonneg) (x : id.Assignment) :
    0 ≤ refMarg κ R σ (fun _ => 1) x :=
  Finset.sum_nonneg fun y _ => by
    simpa only [mul_one] using freeJoint_nonneg κ hκ Rᶜ σ hσ y

theorem refMarg_chance (κ : id.Kernel ℝ) {R : Finset id.V} (σ : Strategy id ℝ)
    (F : id.Assignment → ℝ) (v : id.V) (hv : v ∈ R) (hc : ∀ d, id.action d ≠ v)
    (x : id.Assignment) :
    refMarg κ (R.erase v) σ F x = ∑ b, refMarg κ R σ F (Function.update x v b) := by
  have hn : v ∉ Rᶜ := by simpa using hv
  unfold refMarg
  rw [compl_erase, freeJoint_insert_chance κ Rᶜ σ v hc, marg_insert hn]

theorem refMarg_univ (κ : id.Kernel ℝ) (σ : Strategy id ℝ) (F : id.Assignment → ℝ)
    (x : id.Assignment) :
    refMarg κ Finset.univ σ F x = (∏ m, κ m x (x (id.target m))) * F x := by
  unfold refMarg
  rw [Finset.compl_univ, marg_empty, freeJoint_empty]

theorem refMarg_empty (κ : id.Kernel ℝ) (σ : Strategy id ℝ) (F : id.Assignment → ℝ)
    (x : id.Assignment) :
    refMarg κ ∅ σ F x = ∑ y, joint (strategyKernel κ σ) y * F y := by
  unfold refMarg
  rw [Finset.compl_empty, freeJoint_univ, marg_univ]

/-! ## The approximate invariant -/

/-- **The approximate invariant** of a run state `s` (any kernel) against the normalised
reference kernel `κ`: mass within `[L, H]` of the reference mass, utility bounded by `U` on rows
of positive mass, and reference values of the run's strategy and of every competitor within `e`
of the stored utility. -/
structure ApproxInv (κ : id.Kernel ℝ) (u : Utility id ℝ) (L H U e : ℝ) {R : Finset id.V}
    (s : State id R) (σ : Strategy id ℝ) : Prop where
  nonneg : σ.Nonneg
  mass_lower : ∀ x, L * refMarg κ R σ (fun _ => 1) x ≤ (collect s.valuations).prob x
  mass_upper : ∀ x, (collect s.valuations).prob x ≤ H * refMarg κ R σ (fun _ => 1) x
  bounded : ∀ x, (collect s.valuations).prob x ≠ 0 → |(collect s.valuations).util x| ≤ U
  realizes : ∀ x, |refMarg κ R σ (totalUtility u) x -
      (collect s.valuations).util x * refMarg κ R σ (fun _ => 1) x| ≤
    e * refMarg κ R σ (fun _ => 1) x
  dominates : ∀ τ : Strategy id ℝ, τ.Nonneg → ∀ x,
    refMarg κ R τ (totalUtility u) x ≤
      ((collect s.valuations).util x + e) * refMarg κ R σ (fun _ => 1) x

/-- The invariant at the start of a run: no error yet. -/
theorem ApproxInv.initial (κ κ' : id.Kernel ℝ) (hloc : ∀ m, Local κ' m)
    (hnonneg : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (L H U : ℝ)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hU : ∀ x, |totalUtility u x| ≤ U) :
    ApproxInv κ u L H U 0 (initial κ' hloc hnonneg u hu) defaultStrategy where
  nonneg := deterministic_nonneg _ defaultStrategy_deterministic
  mass_lower x := by
    rw [refMarg_univ, initial_prob, mul_one]
    exact (henv x).1
  mass_upper x := by
    rw [refMarg_univ, initial_prob, mul_one]
    exact (henv x).2
  bounded x _ := by
    rw [initial_util]
    exact hU x
  realizes x := by
    rw [refMarg_univ, refMarg_univ, initial_util]
    simp [mul_comm]
  dominates τ _ x := by
    rw [refMarg_univ, refMarg_univ, initial_util]
    simp [mul_comm]

/-- **A chance step adds at most `(H / L - 1) U` to the error**, for any step whose mass and
weighted utility are the sums over the eliminated variable (both `sumOut` representatives). -/
theorem ApproxInv.chanceOf {κ : id.Kernel ℝ} (hκ : ∀ m x a, 0 ≤ κ m x a) {u : Utility id ℝ}
    {L H U e : ℝ} (hL : 0 < L) (hU : 0 ≤ U) {R : Finset id.V} {s : State id R}
    {σ : Strategy id ℝ} (h : ApproxInv κ u L H U e s σ) (v : id.V) (hv : v ∈ R)
    (hc : ∀ d, id.action d ≠ v) (s' : State id (R.erase v))
    (hp : ∀ x, (collect s'.valuations).prob x =
      ∑ b, (collect s.valuations).prob (Function.update x v b))
    (hw : ∀ x, (collect s'.valuations).weight x =
      ∑ b, (collect s.valuations).weight (Function.update x v b)) :
    ApproxInv κ u L H U (e + (H / L - 1) * U) s' σ := by
  set P := (collect s.valuations).prob
  set W := (collect s.valuations).util
  have hP0 : ∀ y, 0 ≤ P y := fun y => (collect s.valuations).nonneg y
  have hM0 := refMarg_mass_nonneg κ hκ R σ h.nonneg
  -- the stored utility is the `P`-weighted average
  have havg : ∀ x, (∑ b, P (Function.update x v b)) * (collect s'.valuations).util x =
      ∑ b, P (Function.update x v b) * W (Function.update x v b) := by
    intro x
    have := hw x
    rw [weight, hp] at this
    simpa only [weight] using this
  have hre : ∀ x, |∑ b, W (Function.update x v b) * refMarg κ R σ (fun _ => 1)
      (Function.update x v b) - (collect s'.valuations).util x *
        ∑ b, refMarg κ R σ (fun _ => 1) (Function.update x v b)| ≤
      (H / L - 1) * U * ∑ b, refMarg κ R σ (fun _ => 1) (Function.update x v b) := fun x =>
    reweight_error (fun b => P (Function.update x v b))
      (fun b => refMarg κ R σ (fun _ => 1) (Function.update x v b))
      (fun b => W (Function.update x v b)) _ L H U hL (fun b => hM0 _)
      (fun b => h.mass_lower _) (fun b => h.mass_upper _) (fun b hb => h.bounded _ hb) hU
      (havg x)
  refine ⟨h.nonneg, fun x => ?_, fun x => ?_, fun x hx => ?_, fun x => ?_, fun τ hτ x => ?_⟩
  · rw [refMarg_chance κ σ _ v hv hc, hp, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => h.mass_lower _
  · rw [refMarg_chance κ σ _ v hv hc, hp, Finset.mul_sum]
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
  · rw [refMarg_chance κ σ _ v hv hc, refMarg_chance κ σ _ v hv hc]
    have h1 : |∑ b, (refMarg κ R σ (totalUtility u) (Function.update x v b) -
        W (Function.update x v b) * refMarg κ R σ (fun _ => 1) (Function.update x v b))| ≤
        e * ∑ b, refMarg κ R σ (fun _ => 1) (Function.update x v b) := by
      rw [Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun b _ => h.realizes _)
    have h2 := hre x
    rw [Finset.sum_sub_distrib] at h1
    calc _ = |(∑ b, refMarg κ R σ (totalUtility u) (Function.update x v b) -
            ∑ b, W (Function.update x v b) * refMarg κ R σ (fun _ => 1) (Function.update x v b)) +
          (∑ b, W (Function.update x v b) * refMarg κ R σ (fun _ => 1) (Function.update x v b) -
            (collect s'.valuations).util x *
              ∑ b, refMarg κ R σ (fun _ => 1) (Function.update x v b))| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  · rw [refMarg_chance κ τ _ v hv hc, refMarg_chance κ σ _ v hv hc]
    have h1 : ∑ b, refMarg κ R τ (totalUtility u) (Function.update x v b) ≤
        ∑ b, W (Function.update x v b) * refMarg κ R σ (fun _ => 1) (Function.update x v b) +
          e * ∑ b, refMarg κ R σ (fun _ => 1) (Function.update x v b) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun b _ => by
        have := h.dominates τ hτ (Function.update x v b)
        linarith
    have h2 := (abs_le.1 (hre x)).2
    nlinarith

/-- **A decision step adds nothing to the error.** The reference mass does not depend on the free
action (`Independent`), so the run's mass at its probability maximizer and the reference mass at
the chosen action are comparable, and every competitor's action average is dominated. -/
theorem ApproxInv.decisionWith {κ : id.Kernel ℝ} (hκ : ∀ m x a, 0 ≤ κ m x a)
    (hind : Independent κ (fun _ => 1)) (hinj : Function.Injective id.action)
    {u : Utility id ℝ} {L H U e : ℝ} (hL : 0 < L) {R : Finset id.V} {s : State id R}
    {σ : Strategy id ℝ} (h : ApproxInv κ u L H U e s σ) (sel : Selector id) (d : id.D)
    (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d) :
    ApproxInv κ u L H U e (s.decision d) (Function.update σ d (s.policyWith sel d hi)) := by
  have hn : id.action d ∉ Rᶜ := by simpa using hd
  have hinfo := info_disjoint d hi
  set a := id.action d
  set π := s.policyWith sel d hi
  set f : id.Assignment → id.states a := fun x => sel.pick d (bucketScore s.valuations a x)
  set P := (collect s.valuations).prob
  set W := (collect s.valuations).util
  have hπ : ∀ x b, π.kernel x b = if b = f x then 1 else 0 := fun _ _ => rfl
  have hM0 := refMarg_mass_nonneg κ hκ R σ h.nonneg
  have heval : ∀ (F : id.Assignment → ℝ) (x : id.Assignment),
      refMarg κ (R.erase a) (Function.update σ d π) F x =
        refMarg κ R σ F (Function.update x a (f x)) := by
    intro F x
    unfold refMarg
    rw [compl_erase, decision_marginal κ Rᶜ σ hinj d hn hinfo]
    simp [hπ, ite_mul]
    rfl
  have hM : ∀ x b, refMarg κ R σ (fun _ => 1) (Function.update x a b) =
      refMarg κ R σ (fun _ => 1) x := fun x b =>
    hind Rᶜ σ d hn (by simpa using information_boundary d hi) x b
  have hscore : ∀ x b, W (Function.update x a b) ≤ W (Function.update x a (f x)) := by
    intro x b
    show (collect s.valuations).util _ ≤ (collect s.valuations).util _
    rw [util_update_eq_score, util_update_eq_score]
    exact add_le_add (sel.maximizes d _ b) le_rfl
  have hutil : ∀ x, (collect (s.decision d).valuations).util x = W (Function.update x a (f x)) := by
    intro x
    change (collect (decisionStep a s.valuations)).util x = _
    rw [decisionStep_util_eq]
    exact le_antisymm (hscore x _) (by
      show (collect s.valuations).util _ ≤ (collect s.valuations).util _
      rw [util_update_eq_score, util_update_eq_score]
      exact add_le_add (le_argmax (bucketScore s.valuations a x) (f x)) le_rfl)
  have hprob : ∀ x, (collect (s.decision d).valuations).prob x =
      P (Function.update x a (probabilityChoice a (collect (bucket a s.valuations)) x)) :=
    fun x => decisionStep_prob_eq a s.valuations x
  have hmass : ∀ x, refMarg κ (R.erase a) (Function.update σ d π) (fun _ => 1) x =
      refMarg κ R σ (fun _ => 1) x := fun x => by rw [heval, hM]
  refine ⟨?_, fun x => ?_, fun x => ?_, fun x hx => ?_, fun x => ?_, fun τ hτ x => ?_⟩
  · intro e' y b
    by_cases he : e' = d
    · subst he
      rw [Function.update_self, hπ]
      split_ifs <;> norm_num
    · rw [Function.update_of_ne he]
      exact h.nonneg e' y b
  · rw [hmass, hprob, ← hM x (probabilityChoice a (collect (bucket a s.valuations)) x)]
    exact h.mass_lower _
  · rw [hmass, hprob, ← hM x (probabilityChoice a (collect (bucket a s.valuations)) x)]
    exact h.mass_upper _
  · rw [hprob] at hx
    rw [hutil]
    apply h.bounded
    have hpos : 0 < P (Function.update x a
        (probabilityChoice a (collect (bucket a s.valuations)) x)) :=
      lt_of_le_of_ne ((collect s.valuations).nonneg _) (Ne.symm hx)
    have hmpos : 0 < refMarg κ R σ (fun _ => 1) x := by
      have := h.mass_upper (Function.update x a
        (probabilityChoice a (collect (bucket a s.valuations)) x))
      rw [hM] at this
      rcases (hM0 x).lt_or_eq with hlt | heq
      · exact hlt
      · rw [← heq, mul_zero] at this
        exact absurd (lt_of_lt_of_le hpos this) (lt_irrefl 0)
    have := h.mass_lower (Function.update x a (f x))
    rw [hM] at this
    exact ne_of_gt (lt_of_lt_of_le (mul_pos hL hmpos) this)
  · rw [hutil, heval, heval]
    exact h.realizes _
  · have hc := decision_marginal κ Rᶜ τ hinj d hn hinfo (τ d) (totalUtility u) x
    simp only [Function.update_eq_self] at hc
    have hlhs : refMarg κ (R.erase a) τ (totalUtility u) x =
        ∑ b, (τ d).kernel x b * refMarg κ R τ (totalUtility u) (Function.update x a b) := by
      unfold refMarg
      rw [compl_erase]
      exact hc
    rw [hlhs, hutil, hmass]
    calc ∑ b, (τ d).kernel x b * refMarg κ R τ (totalUtility u) (Function.update x a b)
        ≤ ∑ b, (τ d).kernel x b * ((W (Function.update x a (f x)) + e) *
            refMarg κ R σ (fun _ => 1) x) := by
          refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hτ d x b)
          refine (h.dominates τ hτ _).trans ?_
          rw [hM]
          exact mul_le_mul_of_nonneg_right (by linarith [hscore x b]) (hM0 x)
      _ = _ := by rw [← Finset.sum_mul, (τ d).normalised x, one_mul]

/-! ## The run -/

/-- The number of chance eliminations of a plan. -/
def Plan.chanceCount : {R : Finset id.V} → Plan id R → ℕ
  | _, .done => 0
  | _, .chance _ _ _ next => next.chanceCount + 1
  | _, .decision _ _ _ next => next.chanceCount

/-- A plan eliminates every chance variable of its set exactly once. -/
theorem Plan.chanceCount_eq {R : Finset id.V} (plan : Plan id R) :
    plan.chanceCount = (R.filter fun v => ∀ d, id.action d ≠ v).card := by
  induction plan with
  | done => rfl
  | @chance R v hv hc next ih =>
    rw [Plan.chanceCount, ih, Finset.filter_erase,
      Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hv, hc⟩)]
    have : 0 < (R.filter fun v => ∀ d, id.action d ≠ v).card :=
      Finset.card_pos.2 ⟨v, Finset.mem_filter.2 ⟨hv, hc⟩⟩
    omega
  | @decision R d hd hi next ih =>
    have hnot : id.action d ∉ R.filter fun v => ∀ d, id.action d ≠ v :=
      fun h => (Finset.mem_filter.1 h).2 d rfl
    rw [Plan.chanceCount, ih, Finset.filter_erase, Finset.erase_eq_of_notMem hnot]

/-- In a closed diagram, the chance variables are the mechanisms' targets. -/
theorem card_chance_eq (hclosed : id.Closed) :
    (Finset.univ.filter fun v => ∀ d, id.action d ≠ v).card = Fintype.card id.M := by
  obtain ⟨hT, -, hdisj, hcover⟩ := id.closed_iff.1 hclosed
  have : (Finset.univ.filter fun v => ∀ d, id.action d ≠ v) = Finset.univ.image id.target := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hv
      rcases hcover v with ⟨m, hm⟩ | ⟨d, hd⟩
      · exact ⟨m, hm⟩
      · exact absurd hd (hv d)
    · rintro ⟨m, rfl⟩ d hd
      exact hdisj m d hd.symm
  rw [this, Finset.card_image_of_injective _ hT, Finset.card_univ]

theorem runRepWith_approx (sel : Selector id) (keep : id.V → Bool) {κ : id.Kernel ℝ}
    (hκ : ∀ m x a, 0 ≤ κ m x a) (hind : Independent κ (fun _ => 1))
    (hinj : Function.Injective id.action) {u : Utility id ℝ} {L H U : ℝ} (hL : 0 < L)
    (hU : 0 ≤ U) {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ)
    (e : ℝ) (h : ApproxInv κ u L H U e s σ) :
    ApproxInv κ u L H U (e + plan.chanceCount * ((H / L - 1) * U))
      (runRepWith sel keep plan s σ).1 (runRepWith sel keep plan s σ).2 := by
  induction plan generalizing σ e with
  | done => simpa [Plan.chanceCount] using h
  | chance v hv hc next ih =>
    have hs : ApproxInv κ u L H U (e + (H / L - 1) * U) (s.chanceKeep keep v) σ := by
      obtain ⟨hp, hw⟩ := chanceStepKeep_collect (keep v) v s.valuations
      refine h.chanceOf hκ hL hU v hv hc _ (fun x => ?_) (fun x => ?_)
      · change (collect (chanceStepKeep (keep v) v s.valuations)).prob x = _
        rw [hp]
        exact chanceStep_prob v s.valuations x
      · change (collect (chanceStepKeep (keep v) v s.valuations)).weight x = _
        rw [hw]
        exact chanceStep_weight v s.valuations x
    have := ih (s.chanceKeep keep v) σ _ hs
    simp only [Plan.chanceCount, Nat.cast_add, Nat.cast_one] at this ⊢
    convert this using 1
    ring
  | decision d hd hi next ih =>
    exact ih (s.decision d) _ e (h.decisionWith hκ hind hinj hL sel d hd hi)

/-- The error after a whole plan: `k (H / L - 1) U` for `k` chance eliminations. -/
def approxGap (k : ℕ) (L H U : ℝ) : ℝ := k * ((H / L - 1) * U)

theorem approxGap_nonneg (k : ℕ) {L H U : ℝ} (hL : 0 < L) (hLH : L ≤ H) (hU : 0 ≤ U) :
    0 ≤ approxGap k L H U := by
  unfold approxGap
  refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ?_ hU)
  rw [sub_nonneg, le_div_iff₀ hL, one_mul]
  exact hLH

/-- **Approximate DVE on an approximately normalised kernel.** The exact representative run
`solveRepPlanWith sel keep` on `κ'` (any maximizing selector, any representative choice, any
plan) returns a deterministic strategy whose expected utility under the normalised reference
kernel `κ` is within `e = approxGap k L H U` of the run's value, and every nonnegative strategy's
reference expected utility is at most the run's value plus `e`. Here the run's joint weight is
within `[L, H]` of the reference joint, `|U x| ≤ U`, and `k` is the plan's number of chance
eliminations. -/
theorem solveRepPlanWith_approx (sel : Selector id) (keep : id.V → Bool) (κ κ' : id.Kernel ℝ)
    (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (hloc' : ∀ m, Local κ' m)
    (hnonneg' : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) (L H U : ℝ) (hL : 0 < L) (hU : 0 ≤ U)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U) :
    let sol := solveRepPlanWith sel keep κ' hloc' hnonneg' u hu plan
    sol.strategy.Deterministic ∧
      |expectedUtility κ sol.strategy u - sol.value| ≤ approxGap plan.chanceCount L H U ∧
      ∀ τ : Strategy id ℝ, τ.Nonneg →
        expectedUtility κ τ u ≤ sol.value + approxGap plan.chanceCount L H U := by
  intro sol
  have hinj := (id.closed_iff.1 hclosed).2.1
  have hind := independent_one κ hclosed ord hloc hnorm
  have h0 := ApproxInv.initial κ κ' hloc' hnonneg' u hu L H U henv hUb
  have hr := runRepWith_approx sel keep hnonneg hind hinj hL hU plan _ _ 0 h0
  rw [zero_add] at hr
  have hone : ∀ σ : Strategy id ℝ, refMarg κ ∅ σ (fun _ => 1) (baseAssignment id) = 1 := by
    intro σ
    rw [refMarg_empty]
    simpa only [mul_one] using sum_joint_instantiate_eq_one κ σ hclosed ord hloc hnorm
  have heu : ∀ σ : Strategy id ℝ,
      refMarg κ ∅ σ (totalUtility u) (baseAssignment id) = expectedUtility κ σ u := by
    intro σ
    rw [refMarg_empty]
    rfl
  refine ⟨runRepWith_deterministic sel keep _ _ _ defaultStrategy_deterministic, ?_, ?_⟩
  · have := hr.realizes (baseAssignment id)
    rw [hone, heu, mul_one, mul_one] at this
    exact this
  · intro τ hτ
    have := hr.dominates τ hτ (baseAssignment id)
    rw [hone, heu, mul_one] at this
    exact this

/-- **Approximate optimality.** Under the hypotheses of `solveRepPlanWith_approx`, with
`e = approxGap k L H U`: the run's strategy is within `2 e` of every nonnegative strategy and
of the optimum under the reference kernel, and the run's value is within `e` of that optimum. -/
theorem solveRepPlanWith_approx_optimal (sel : Selector id) (keep : id.V → Bool)
    (κ κ' : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (hloc' : ∀ m, Local κ' m)
    (hnonneg' : ∀ m x a, 0 ≤ κ' m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) (L H U : ℝ) (hL : 0 < L) (hU : 0 ≤ U)
    (henv : ∀ x, L * (∏ m, κ m x (x (id.target m))) ≤ ∏ m, κ' m x (x (id.target m)) ∧
      ∏ m, κ' m x (x (id.target m)) ≤ H * ∏ m, κ m x (x (id.target m)))
    (hUb : ∀ x, |totalUtility u x| ≤ U) :
    let sol := solveRepPlanWith sel keep κ' hloc' hnonneg' u hu plan
    let e := approxGap plan.chanceCount L H U
    sol.strategy.Deterministic ∧
      (∀ τ : Strategy id ℝ, τ.Nonneg →
        expectedUtility κ τ u ≤ expectedUtility κ sol.strategy u + 2 * e) ∧
      optimalValue κ u - 2 * e ≤ expectedUtility κ sol.strategy u ∧
      expectedUtility κ sol.strategy u ≤ optimalValue κ u ∧
      |sol.value - optimalValue κ u| ≤ e := by
  intro sol e
  obtain ⟨hdet, hre, hdom⟩ := solveRepPlanWith_approx sel keep κ κ' hclosed ord hloc hnorm
    hnonneg hloc' hnonneg' u hu plan L H U hL hU henv hUb
  have hre' := abs_le.1 hre
  have hall : ∀ τ : Strategy id ℝ, τ.Nonneg →
      expectedUtility κ τ u ≤ expectedUtility κ sol.strategy u + 2 * e := by
    intro τ hτ
    have := hdom τ hτ
    change _ ≤ sol.value + e at this
    linarith [hre'.1]
  have hle : expectedUtility κ sol.strategy u ≤ optimalValue κ u :=
    expectedUtility_le_optimalValue κ u _ (deterministic_nonneg _ hdet)
  obtain ⟨σo, _, hσo, hvo⟩ := optimalValue_attained κ u
  refine ⟨hdet, hall, ?_, hle, ?_⟩
  · have := hall σo hσo
    rw [hvo] at this
    linarith
  · have := hdom σo hσo
    rw [hvo] at this
    change _ ≤ sol.value + e at this
    rw [abs_le]
    constructor
    · linarith
    · linarith [hre'.1, hle]

end
end InfluenceDiagramsProofs.DVE
