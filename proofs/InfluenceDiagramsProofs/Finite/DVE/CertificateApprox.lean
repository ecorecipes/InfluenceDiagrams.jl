import InfluenceDiagramsProofs.Finite.DVE.CertificateCheck
import InfluenceDiagramsProofs.Finite.DVE.Approximate

/-!
# Approximate optimality on a certificate whose rows nearly sum to one

`certificate_solve_spec` needs every CPT row of the certificate to sum to exactly one
(`ExactNormalised`). The binary64 words Julia writes almost never do (0 of the 14 binary64
certificates of the cross-check), so this module bounds the loss instead.

**Computable quantities** (all exact rationals, read from the certificate alone):

* `certificateEpsilon c`: the largest `|row sum - 1|` over the certificate's CPT rows, a row
  being a coordinate list of the parents (axes `parents`, extents the certificate's own state
  counts `certDim`) and its sum running over the target's states;
* `certChanceCount c = n`: the number of mechanisms (chance variables); decisions have no rows
  in the certificate, and their policies are normalised by construction (`Policy.normalised`),
  so they enter no factor below;
* `certUmax c`: the sum over utility tables of the largest absolute cell, an upper bound of the
  absolute total utility `|∑ j, u j x|` (`certUtility_total_le`);
* `approxError ε n U = n (((1 + ε) / (1 - ε)) ^ n - 1) U` and
  `certificateBound c = 2 * approxError (certificateEpsilon c) n (certUmax c)`.

**The reference model** is `certNormKernel`: every row divided by its own sum, which is positive
when `certificateEpsilon c < 1`. It is the only normalised model the certificate determines; the
intended model whose decimal CPTs Julia rounded is not known to the certificate. The
certificate's joint weight is the reference joint times `∏ m, rowsum_m x`, which lies in
`[(1 - ε) ^ n, (1 + ε) ^ n]` (`certKernel_envelope`).

**Theorems.**

* `certificate_approx_optimal`: for a matching certificate with nonnegative cells and
  `certificateEpsilon c < 1`, the exact representative DVE run on the certificate's data (any
  maximizing selector, in particular Julia's first-label one `r.selector`, any representative
  choice `keep`, any plan) returns a deterministic strategy `σ*` with, writing `κ̂` for
  `certNormKernel`, `u` for `certUtility` and `e = approxError ε n U`,
  `EU κ̂ τ u ≤ EU κ̂ σ* u + 2 e` for every nonnegative strategy `τ`,
  `optimalValue κ̂ u - 2 e ≤ EU κ̂ σ* u ≤ optimalValue κ̂ u`, and
  `|value - optimalValue κ̂ u| ≤ e`;
* `certificate_solve_approx`: the same for `DVE.solve` scheduled by the certificate's orders,
  the run of `certificate_solve_spec`;
* `certificateEpsilon_eq_zero_iff`: `certificateEpsilon c = 0` exactly when `ExactNormalised r c`;
  then `certNormKernel = certKernel` and `approxError 0 n U = 0`, so the bound is `0` and the
  conclusions are `certificate_solve_spec`'s (`certificate_approx_exact`).

The bound is `2 n (((1 + ε) / (1 - ε)) ^ n - 1) U ≈ 4 n² ε U`, not `2 ((1 + ε) ^ n - 1) U`; see
`Finite/DVE/Approximate.lean` for why the run does not maximise the unnormalised score. This is
about the exact DVE run on the certificate's exact numbers, not about Julia's Float64 solver
run: the version-1 certificate carries no solution.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVECertificate

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram
open BayesianNetworksProofs.Raw InfluenceDiagramsProofs.Records Spec

/-! ## Computable quantities -/

/-- The state count of variable `v` read from the certificate's own state rows. -/
def certDim (c : Certificate) (v : Nat) : Nat :=
  ((c.vars[v]?).map fun e => e.states.length).getD 0

/-- The exact sum of the CPT row `row` of a mechanism, over the target's states. -/
def rowSum (c : Certificate) (e : MechanismEntry) (row : List Nat) : ℚ :=
  ((List.range (certDim c e.target)).map fun a => cellValue e.cpt (row ++ [a])).sum

/-- `|row sum - 1|` for every CPT row of the certificate. -/
def rowDeviations (c : Certificate) : List ℚ :=
  c.mechanisms.flatMap fun e =>
    (lexCoords ((e.parents.map Slot.var).map (certDim c))).map fun row => |rowSum c e row - 1|

/-- **The certificate's normalisation error**: the largest `|row sum - 1|` over its CPT rows. -/
def certificateEpsilon (c : Certificate) : ℚ := (rowDeviations c).foldr max 0

/-- The largest absolute cell of a table. -/
def tableMaxAbs (t : NumTable) : ℚ := (t.entries.map fun x => |x.value.toRat|).foldr max 0

/-- An upper bound of the absolute total utility: the sum of the tables' largest absolute
cells. -/
def certUmax (c : Certificate) : ℚ := (c.utilities.map fun e => tableMaxAbs e.table).sum

/-- The number of chance variables (mechanisms). -/
def certChanceCount (c : Certificate) : ℕ := c.mechanisms.length

/-- The per-run error `n (((1 + ε) / (1 - ε)) ^ n - 1) U`. -/
def approxError (ε : ℚ) (n : ℕ) (U : ℚ) : ℚ := n * (((1 + ε) / (1 - ε)) ^ n - 1) * U

/-- **The certificate's optimality gap** `2 * approxError ε n U`. -/
def certificateBound (c : Certificate) : ℚ :=
  2 * approxError (certificateEpsilon c) (certChanceCount c) (certUmax c)

theorem le_foldr_max {l : List ℚ} {x : ℚ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rcases List.mem_cons.1 hx with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_nonneg (l : List ℚ) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => exact le_refl 0
  | cons y l ih => exact ih.trans (le_max_right _ _)

theorem foldr_max_le {l : List ℚ} {b : ℚ} (hb : 0 ≤ b) (h : ∀ x ∈ l, x ≤ b) :
    l.foldr max 0 ≤ b := by
  induction l with
  | nil => exact hb
  | cons y l ih =>
    exact max_le (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem certificateEpsilon_nonneg (c : Certificate) : 0 ≤ certificateEpsilon c :=
  foldr_max_nonneg _

theorem tableMaxAbs_nonneg (t : NumTable) : 0 ≤ tableMaxAbs t := foldr_max_nonneg _

theorem certUmax_nonneg (c : Certificate) : 0 ≤ certUmax c :=
  List.sum_nonneg fun x hx => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
    exact tableMaxAbs_nonneg _

theorem approxError_zero (n : ℕ) (U : ℚ) : approxError 0 n U = 0 := by
  simp [approxError]

theorem sum_range_list {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem sum_fin_getElem? {α : Type} (l : List α) (f : α → ℚ) (n : ℕ) (hn : l.length = n) :
    ∑ j : Fin n, ((l[j.val]?).map f).getD 0 = (l.map f).sum := by
  subst hn
  induction l with
  | nil => simp
  | cons a l ih =>
    refine (Fin.sum_univ_succ (n := l.length)
      fun j : Fin (l.length + 1) => (((a :: l)[j.val]?).map f).getD 0).trans ?_
    simp

/-! ## The certificate's rows are the model's rows -/

section Rows

variable {r : Diagram} {c : Certificate}

theorem certDim_eq (hm : Matches r c) (v : Nat) : certDim c v = dim r v := by
  unfold certDim dim
  by_cases hv : v < r.nv
  · rw [dif_pos hv]
    have hvo := hm.vars ⟨v, hv⟩
    cases hc : c.vars[v]? with
    | none => rw [hc] at hvo; exact hvo.elim
    | some e =>
      rw [hc] at hvo
      exact hvo.2.2.2.1
  · rw [dif_neg hv]
    have : c.vars[v]? = none := by
      rw [List.getElem?_eq_none_iff, hm.vars_length]
      omega
    rw [this]
    rfl

/-- The exact row sum of the certificate's kernel is the certificate's `rowSum`. -/
theorem rowSum_eq (hm : Matches r c) (m : Fin r.nm) {e : MechanismEntry}
    (hc : c.mechanisms[m.val]? = some e) (row : List Nat) :
    rowSum c e row = ∑ a : Fin (r.stateCount (r.mechanisms m).target),
      cellValue e.cpt (row ++ [a.val]) := by
  have hmo := hm.mechanisms m
  rw [hc] at hmo
  change MechanismOk r c.pool m e at hmo
  have ht : certDim c e.target = r.stateCount (r.mechanisms m).target := by
    rw [certDim_eq hm, hmo.2.1, dim, dif_pos (r.mechanisms m).target.isLt]
  unfold rowSum
  rw [sum_range_list, ht]

theorem rows_eq (hm : Matches r c) (e : MechanismEntry) :
    (e.parents.map Slot.var).map (certDim c) = (e.parents.map Slot.var).map (dim r) :=
  List.map_congr_left fun v _ => certDim_eq hm v

theorem mem_rowDeviations {e : MechanismEntry} (he : e ∈ c.mechanisms) {row : List Nat}
    (hrow : row ∈ lexCoords ((e.parents.map Slot.var).map (certDim c))) :
    |rowSum c e row - 1| ≤ certificateEpsilon c :=
  le_foldr_max (List.mem_flatMap.2 ⟨e, he, List.mem_map.2 ⟨row, hrow, rfl⟩⟩)

/-- **`certificateEpsilon` is zero exactly on exactly normalised certificates.** -/
theorem certificateEpsilon_eq_zero_iff (hm : Matches r c) :
    certificateEpsilon c = 0 ↔ ExactNormalised r c := by
  constructor
  · intro h0 m
    have hmo := hm.mechanisms m
    cases hc : c.mechanisms[m.val]? with
    | none => rw [hc] at hmo; exact hmo.elim
    | some e =>
      intro row hrow
      rw [← rows_eq hm] at hrow
      have := mem_rowDeviations (List.mem_of_getElem? hc) hrow
      rw [h0] at this
      rw [← rowSum_eq hm m hc]
      exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  · intro hex
    refine le_antisymm (foldr_max_le (le_refl 0) fun x hx => ?_) (certificateEpsilon_nonneg c)
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
    have hlen : i < r.nm := hm.mechanisms_length ▸ hi
    have hc : c.mechanisms[(⟨i, hlen⟩ : Fin r.nm).val]? = some e := by
      simp [List.getElem?_eq_getElem hi, hie]
    have hno := hex ⟨i, hlen⟩
    rw [hc] at hno
    rw [rows_eq hm] at hrow
    rw [rowSum_eq hm _ hc, hno row hrow, sub_self, abs_zero]

end Rows

/-! ## The normalised reference kernel -/

section Kernel

variable (r : Diagram) (h : r.Valid) (c : Certificate)

/-- The row sum of the certificate's kernel. -/
noncomputable def certRowSum (m : (r.compile h).M) (x : (r.compile h).Assignment) : ℝ :=
  ∑ b, certKernel r h c m x b

/-- **The reference model**: every certificate row divided by its own sum. -/
noncomputable def certNormKernel : (r.compile h).Kernel ℝ := fun m x a =>
  certKernel r h c m x a / certRowSum r h c m x

variable {r c}

/-- Every row of the certificate's kernel sums to within `certificateEpsilon c` of one. -/
theorem certRowSum_dev (hm : Matches r c) (h : r.Valid) (m : Fin r.nm)
    (x : (r.compile h).Assignment) :
    |certRowSum r h c m x - 1| ≤ (certificateEpsilon c : ℝ) := by
  have hmo := hm.mechanisms m
  unfold certRowSum certKernel
  cases hc : c.mechanisms[m.val]? with
  | none => rw [hc] at hmo; exact hmo.elim
  | some e =>
    rw [hc] at hmo
    change MechanismOk r c.pool m e at hmo
    have hsl := hmo.2.2.2.1
    simp only
    have hrow : coordsOf r h x (e.parents.map Slot.var) ∈
        lexCoords ((e.parents.map Slot.var).map (certDim c)) := by
      rw [rows_eq hm, mem_lexCoords, coordsOf, List.forall₂_map_left_iff,
        List.forall₂_map_right_iff, List.forall₂_same]
      intro v hv
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hv
      obtain ⟨i, -, hvar⟩ := hsl.mem hs
      have hlt : s.var < r.nv := hvar ▸ (r.inputs i).var.isLt
      simp only [dif_pos hlt, dim]
      exact (x ⟨s.var, hlt⟩).isLt
    have hd := mem_rowDeviations (List.mem_of_getElem? hc) hrow
    rw [rowSum_eq hm m hc] at hd
    have hcast : (∑ b : Fin (r.stateCount (r.mechanisms m).target),
        ((cellValue e.cpt (coordsOf r h x (e.parents.map Slot.var) ++ [b.val]) : ℚ) : ℝ)) =
        ((∑ b : Fin (r.stateCount (r.mechanisms m).target),
          cellValue e.cpt (coordsOf r h x (e.parents.map Slot.var) ++ [b.val]) : ℚ) : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    exact_mod_cast hd

theorem certRowSum_pos (hm : Matches r c) (hε : certificateEpsilon c < 1) (h : r.Valid)
    (m : Fin r.nm) (x : (r.compile h).Assignment) : 0 < certRowSum r h c m x := by
  have hd := abs_le.1 (certRowSum_dev hm h m x)
  have : (certificateEpsilon c : ℝ) < 1 := by exact_mod_cast hε
  linarith [hd.1]

theorem certNormKernel_local (hm : Matches r c) (h : r.Valid) (m : Fin r.nm) :
    Local (certNormKernel r h c) m := by
  intro x x' hxx
  have hk := certKernel_local hm h m x x' hxx
  funext a
  unfold certNormKernel certRowSum
  rw [hk]

theorem certNormKernel_nonneg (hn : Nonneg c) (h : r.Valid) (m : Fin r.nm)
    (x : (r.compile h).Assignment) (a : (r.compile h).states ((r.compile h).target m)) :
    0 ≤ certNormKernel r h c m x a :=
  div_nonneg (certKernel_nonneg hn h m x a)
    (Finset.sum_nonneg fun b _ => certKernel_nonneg hn h m x b)

theorem certNormKernel_normalised (hm : Matches r c) (hε : certificateEpsilon c < 1)
    (h : r.Valid) (m : Fin r.nm) : Normalised (certNormKernel r h c) m := by
  intro x
  unfold certNormKernel
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (certRowSum_pos hm hε h m x))

/-- On an exactly normalised certificate the reference model is the certificate's model. -/
theorem certNormKernel_eq_of_exact (hm : Matches r c) (hex : ExactNormalised r c) (h : r.Valid) :
    certNormKernel r h c = certKernel r h c := by
  funext m x a
  unfold certNormKernel certRowSum
  rw [certKernel_normalised hm hex h m x, div_one]

/-- **The joint weight envelope**: the certificate's joint is the reference joint times the
product of the `n` chance row sums, which lies in `[(1 - ε) ^ n, (1 + ε) ^ n]`. -/
theorem certKernel_envelope (hm : Matches r c) (hn : Nonneg c) (hε : certificateEpsilon c < 1)
    (h : r.Valid) (x : (r.compile h).Assignment) :
    (1 - (certificateEpsilon c : ℝ)) ^ certChanceCount c *
        (∏ m, certNormKernel r h c m x (x ((r.compile h).target m))) ≤
      ∏ m, certKernel r h c m x (x ((r.compile h).target m)) ∧
    ∏ m, certKernel r h c m x (x ((r.compile h).target m)) ≤
      (1 + (certificateEpsilon c : ℝ)) ^ certChanceCount c *
        ∏ m, certNormKernel r h c m x (x ((r.compile h).target m)) := by
  have hε1 : (certificateEpsilon c : ℝ) < 1 := by exact_mod_cast hε
  set ε : ℝ := (certificateEpsilon c : ℝ)
  have hfac : ∏ m, certKernel r h c m x (x ((r.compile h).target m)) =
      (∏ m : Fin r.nm, certRowSum r h c m x) *
        ∏ m, certNormKernel r h c m x (x ((r.compile h).target m)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun m _ => ?_
    unfold certNormKernel
    rw [mul_div_cancel₀ _ (ne_of_gt (certRowSum_pos hm hε h m x))]
  have hn' : certChanceCount c = Fintype.card (Fin r.nm) := by
    rw [Fintype.card_fin, certChanceCount, hm.mechanisms_length]
  have hK : 0 ≤ ∏ m, certNormKernel r h c m x (x ((r.compile h).target m)) :=
    Finset.prod_nonneg fun m _ => certNormKernel_nonneg hn h m x _
  have hlo : (1 - ε) ^ certChanceCount c ≤ ∏ m : Fin r.nm, certRowSum r h c m x := by
    rw [hn', ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by linarith)
      fun m _ => by linarith [(abs_le.1 (certRowSum_dev hm h m x)).1]
  have hhi : ∏ m : Fin r.nm, certRowSum r h c m x ≤ (1 + ε) ^ certChanceCount c := by
    rw [hn', ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun m _ => (certRowSum_pos hm hε h m x).le)
      fun m _ => by linarith [(abs_le.1 (certRowSum_dev hm h m x)).2]
  rw [hfac]
  exact ⟨mul_le_mul_of_nonneg_right hlo hK, mul_le_mul_of_nonneg_right hhi hK⟩

/-- The absolute total utility is at most `certUmax c`. -/
theorem certUtility_total_le (hm : Matches r c) (h : r.Valid) (x : (r.compile h).Assignment) :
    |totalUtility (certUtility r h c) x| ≤ (certUmax c : ℝ) := by
  have hcell : ∀ (t : NumTable) (coords : List Nat), |cellValue t coords| ≤ tableMaxAbs t := by
    intro t coords
    unfold cellValue lookup
    cases hf : t.entries.find? (fun e => decide (e.coords = coords)) with
    | none => simpa using tableMaxAbs_nonneg t
    | some e =>
      simp only [Option.map_some, Option.getD_some]
      exact le_foldr_max (List.mem_map.2 ⟨e, List.mem_of_find?_eq_some hf, rfl⟩)
  have hj : ∀ j : Fin r.nu, |certUtility r h c j x| ≤
      ((((c.utilities[j.val]?).map fun e => tableMaxAbs e.table).getD 0 : ℚ) : ℝ) := by
    intro j
    unfold certUtility
    cases c.utilities[j.val]? with
    | none => simp
    | some e =>
      simp only [Option.map_some, Option.getD_some]
      exact_mod_cast hcell e.table _
  have hsum := sum_fin_getElem? c.utilities (fun e => tableMaxAbs e.table) r.nu
    hm.utilities_length
  calc |totalUtility (certUtility r h c) x| ≤ ∑ j, |certUtility r h c j x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin r.nu,
        ((((c.utilities[j.val]?).map fun e => tableMaxAbs e.table).getD 0 : ℚ) : ℝ) :=
        Finset.sum_le_sum fun j _ => hj j
    _ = (certUmax c : ℝ) := by
        rw [certUmax, ← hsum]
        push_cast
        rfl

end Kernel

/-! ## Approximate optimality -/

section Approx

variable (r : Diagram) (h : r.FullValid) (c : Certificate)

theorem approxGap_eq (hm : Matches r c) (hε : certificateEpsilon c < 1)
    (plan : DVE.Plan (r.compile h.valid) Finset.univ) :
    DVE.approxGap plan.chanceCount ((1 - (certificateEpsilon c : ℝ)) ^ certChanceCount c)
        ((1 + (certificateEpsilon c : ℝ)) ^ certChanceCount c) (certUmax c) =
      (approxError (certificateEpsilon c) (certChanceCount c) (certUmax c) : ℝ) := by
  have hk : plan.chanceCount = certChanceCount c := by
    rw [DVE.Plan.chanceCount_eq, DVE.card_chance_eq h.closed, certChanceCount,
      hm.mechanisms_length]
    exact Fintype.card_fin _
  have hε1 : (certificateEpsilon c : ℝ) ≠ 1 := ne_of_lt (by exact_mod_cast hε)
  unfold DVE.approxGap approxError
  rw [hk, ← div_pow]
  push_cast
  ring

/-- **Approximate optimality of the exact DVE run on the certificate's data.** For a matching
certificate with nonnegative cells and `certificateEpsilon c < 1`, the exact representative DVE
run on the certificate's exact numbers (any maximizing selector, any representative choice, any
plan) returns a deterministic strategy `σ*` that is within `2 e` of every nonnegative strategy
and of the optimum of the normalised reference model `certNormKernel`, and whose value is within
`e` of that optimum, where `e = approxError (certificateEpsilon c) (certChanceCount c)
(certUmax c)`. -/
theorem certificate_approx_optimal (hm : certificateMatches r h c) (hn : Nonneg c)
    (hε : certificateEpsilon c < 1) (sel : DVE.Selector (r.compile h.valid))
    (keep : (r.compile h.valid).V → Bool) (plan : DVE.Plan (r.compile h.valid) Finset.univ) :
    let sol := DVE.solveRepPlanWith sel keep (certKernel r h.valid c)
      (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
      (certUtility_local hm h.valid) plan
    let e : ℝ := approxError (certificateEpsilon c) (certChanceCount c) (certUmax c)
    sol.strategy.Deterministic ∧
      (∀ τ : Strategy (r.compile h.valid) ℝ, τ.Nonneg →
        expectedUtility (certNormKernel r h.valid c) τ (certUtility r h.valid c) ≤
          expectedUtility (certNormKernel r h.valid c) sol.strategy (certUtility r h.valid c) +
            2 * e) ∧
      optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) - 2 * e ≤
        expectedUtility (certNormKernel r h.valid c) sol.strategy (certUtility r h.valid c) ∧
      expectedUtility (certNormKernel r h.valid c) sol.strategy (certUtility r h.valid c) ≤
        optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) ∧
      |sol.value - optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c)| ≤ e := by
  intro sol e
  have hε1 : (certificateEpsilon c : ℝ) < 1 := by exact_mod_cast hε
  have hL : 0 < (1 - (certificateEpsilon c : ℝ)) ^ certChanceCount c :=
    pow_pos (by linarith) _
  have hU : (0 : ℝ) ≤ certUmax c := by exact_mod_cast certUmax_nonneg c
  have := DVE.solveRepPlanWith_approx_optimal sel keep (certNormKernel r h.valid c)
    (certKernel r h.valid c) h.closed h.idOrder (certNormKernel_local hm h.valid)
    (certNormKernel_normalised hm hε h.valid) (certNormKernel_nonneg hn h.valid)
    (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
    (certUtility_local hm h.valid) plan _ _ _ hL hU
    (certKernel_envelope hm hn hε h.valid) (certUtility_total_le hm h.valid)
  rw [approxGap_eq r h c hm hε plan] at this
  exact this

/-- The same bound for `DVE.solve` scheduled by the certificate's orders, the run of
`certificate_solve_spec`. -/
theorem certificate_solve_approx (hm : certificateMatches r h c) (hn : Nonneg c)
    (hε : certificateEpsilon c < 1) :
    let sol := DVE.solve (certKernel r h.valid c) (certKernel_local hm h.valid)
      (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid)
      (certOrder hm h) (certNoForgetting hm h)
    let e : ℝ := approxError (certificateEpsilon c) (certChanceCount c) (certUmax c)
    sol.strategy.Deterministic ∧
      (∀ τ : Strategy (r.compile h.valid) ℝ, τ.Nonneg →
        expectedUtility (certNormKernel r h.valid c) τ (certUtility r h.valid c) ≤
          expectedUtility (certNormKernel r h.valid c) sol.strategy (certUtility r h.valid c) +
            2 * e) ∧
      optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) - 2 * e ≤
        expectedUtility (certNormKernel r h.valid c) sol.strategy (certUtility r h.valid c) ∧
      expectedUtility (certNormKernel r h.valid c) sol.strategy (certUtility r h.valid c) ≤
        optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) ∧
      |sol.value - optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c)| ≤ e := by
  have heq : DVE.solve (certKernel r h.valid c) (certKernel_local hm h.valid)
      (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid)
      (certOrder hm h) (certNoForgetting hm h) =
      DVE.solveRepPlanWith (DVE.Selector.classical _) (fun _ => false) (certKernel r h.valid c)
        (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
        (certUtility_local hm h.valid)
        ((certNoForgetting hm h).plan (certOrder hm h).no_self_info) := by
    rw [DVE.solveRepPlanWith_false]
    unfold DVE.solve DVE.solvePlan DVE.solvePlanWith
    rw [DVE.runWith_classical]
  intro sol e
  rw [show sol = _ from heq]
  exact certificate_approx_optimal r h c hm hn hε _ _ _

/-- **The exact case.** On an exactly normalised certificate, `certificateEpsilon c = 0`, the
reference model is the certificate's model and the bound is `0`; the conclusions of
`certificate_solve_approx` are then those of `certificate_solve_spec`. -/
theorem certificate_approx_exact (hm : certificateMatches r h c) (hex : ExactNormalised r c) :
    certificateEpsilon c = 0 ∧ certNormKernel r h.valid c = certKernel r h.valid c ∧
      approxError (certificateEpsilon c) (certChanceCount c) (certUmax c) = 0 ∧
      certificateBound c = 0 := by
  have h0 := (certificateEpsilon_eq_zero_iff hm).2 hex
  refine ⟨h0, certNormKernel_eq_of_exact hm hex h.valid, ?_, ?_⟩
  · rw [h0, approxError_zero]
  · rw [certificateBound, h0, approxError_zero, mul_zero]

end Approx

end InfluenceDiagramsProofs.DVECertificate
