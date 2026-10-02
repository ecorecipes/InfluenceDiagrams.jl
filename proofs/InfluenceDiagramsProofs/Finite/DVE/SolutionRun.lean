import InfluenceDiagramsProofs.Finite.DVE.SolutionJson

/-!
# A computable exact run of the certificate's DVE

`certificate_tables`, `certificate_tables_optimal` and `certificate_approx_optimal` speak about
`DVE.solveRepPlanWith (r.selector h.valid) keep (certKernel r h.valid c) … plan`: the bucket
driver over `ℝ` with Julia's sum-out representative `keep`, on the certificate's exact numbers.
That run is a noncomputable function of real-valued valuations, so it cannot be compared with
Julia's recorded solution as it stands. This module computes it.

* `QVal` is a valuation over `ℚ` (scope, probability and utility functions) that also carries
  `uvars`, the variables of Julia's utility potential `ψ` (`ψ.vars`): `qcombine` takes unions,
  `qsumOut a` keeps `ψ` exactly when `a ∉ uvars` (Julia's `sum_out` branch `x in v.ψ.vars`) and
  otherwise divides, `qmaxOut a` maximizes. `Rel q v` says that the real valuation `v` is `q` read
  in `ℝ`; `rel_combine`, `rel_collect`, `rel_sumOut` and `rel_maxOut` show that every step
  preserves it, `rel_sumOut` for the representative `keep = (a ∉ uvars)`, given `UDep q` (the
  utility function depends only on `uvars`, which every step preserves).
* `TVal` stores a valuation as tables over its scope (`tab`, read back by `view`;
  `view_tab`: reading back gives the function tabulated), so each step is computed once.
* `runT` runs a plan on tables, `scoreT` returns the score row the run maximizes for a decision,
  `valueT` the value, and `keepOfT` the representative choice of every summed variable.
* `planOf` builds a `DVE.Plan` from an elimination order (Julia's `elimination_order`), checking
  that each decision is eliminated when exactly its information set remains.

**Result.** `exactRun_spec`: for a certificate that matches the checked diagram and has
nonnegative cells, and any plan, the real run with `keep := keepOfT plan` has value
`valueT plan` and score rows `scoreT plan` read in `ℝ`. The tables and the value are therefore
computed exactly, as rationals, by this module.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVECertificate

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram
open BayesianNetworksProofs.Raw InfluenceDiagramsProofs.Records Spec

/-! ## Rational valuations -/

/-- A valuation over `ℚ`: its scope, the variables of its utility potential (Julia's
`ψ.vars`), and its probability and utility functions. -/
structure QVal (bn : FinBayesNet) where
  scope : Finset bn.V
  uvars : Finset bn.V
  prob : bn.Assignment → ℚ
  util : bn.Assignment → ℚ

section QVal

variable {bn : FinBayesNet}

def qunit : QVal bn := ⟨∅, ∅, fun _ => 1, fun _ => 0⟩

def qcombine (v w : QVal bn) : QVal bn :=
  ⟨v.scope ∪ w.scope, v.uvars ∪ w.uvars, fun x => v.prob x * w.prob x, fun x => v.util x + w.util x⟩

def qcollect : List (QVal bn) → QVal bn
  | [] => qunit
  | v :: vs => qcombine v (qcollect vs)

/-- `0 / 0 := 0`, as Julia's `_divide`. -/
def ratioQ (n p : ℚ) : ℚ := if p = 0 then 0 else n / p

/-- Julia's `sum_out`: divide when `a` is a variable of the utility potential, keep it
otherwise. -/
def qsumOut (a : bn.V) (v : QVal bn) : QVal bn where
  scope := v.scope.erase a
  uvars := if a ∈ v.uvars then v.scope.erase a else v.uvars
  prob x := ∑ b, v.prob (Function.update x a b)
  util x := if a ∈ v.uvars then
      ratioQ (∑ b, v.prob (Function.update x a b) * v.util (Function.update x a b))
        (∑ b, v.prob (Function.update x a b))
    else v.util x

/-- Julia's `max_out`: the maximum over `a` of each potential. -/
def qmaxOut (a : bn.V) (v : QVal bn) : QVal bn where
  scope := v.scope.erase a
  uvars := v.uvars.erase a
  prob x := Finset.univ.sup' Finset.univ_nonempty fun b => v.prob (Function.update x a b)
  util x := Finset.univ.sup' Finset.univ_nonempty fun b => v.util (Function.update x a b)

/-- `f` reads only the variables of `S`. -/
def DepQ (S : Finset bn.V) (f : bn.Assignment → ℚ) : Prop :=
  ∀ x y : bn.Assignment, (∀ w ∈ S, x w = y w) → f x = f y

/-- The utility function reads only `uvars`. -/
def UDep (q : QVal bn) : Prop := DepQ q.uvars q.util

/-- **The real valuation `v` is `q` read in `ℝ`.** -/
def Rel (q : QVal bn) (v : DVE.Valuation bn) : Prop :=
  q.scope = v.scope ∧ (∀ x, v.prob x = (q.prob x : ℝ)) ∧ ∀ x, v.util x = (q.util x : ℝ)

theorem Rel.depProb {q : QVal bn} {v : DVE.Valuation bn} (h : Rel q v) : DepQ q.scope q.prob :=
  fun x y hxy => by
    have := v.prob_local x y (fun w hw => hxy w (by rw [h.1]; exact hw))
    rw [h.2.1, h.2.1] at this
    exact_mod_cast this

theorem Rel.depUtil {q : QVal bn} {v : DVE.Valuation bn} (h : Rel q v) : DepQ q.scope q.util :=
  fun x y hxy => by
    have := v.util_local x y (fun w hw => hxy w (by rw [h.1]; exact hw))
    rw [h.2.2, h.2.2] at this
    exact_mod_cast this

theorem rel_unit : Rel (qunit : QVal bn) DVE.Valuation.unit :=
  ⟨rfl, fun _ => by simp [qunit, DVE.Valuation.unit], fun _ => by simp [qunit, DVE.Valuation.unit]⟩

theorem rel_combine {q q' : QVal bn} {v v' : DVE.Valuation bn} (h : Rel q v) (h' : Rel q' v') :
    Rel (qcombine q q') (DVE.Valuation.combine v v') := by
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · change q.scope ∪ q'.scope = v.scope ∪ v'.scope
    rw [h.1, h'.1]
  · change v.prob x * v'.prob x = ((q.prob x * q'.prob x : ℚ) : ℝ)
    rw [h.2.1, h'.2.1]
    push_cast
    rfl
  · change v.util x + v'.util x = ((q.util x + q'.util x : ℚ) : ℝ)
    rw [h.2.2, h'.2.2]
    push_cast
    rfl

theorem rel_collect {qs : List (QVal bn)} {vs : List (DVE.Valuation bn)}
    (h : List.Forall₂ Rel qs vs) : Rel (qcollect qs) (DVE.Valuation.collect vs) := by
  induction h with
  | nil => exact rel_unit
  | cons hr _ ih => exact rel_combine hr ih

theorem udep_unit : UDep (qunit : QVal bn) := fun _ _ _ => rfl

theorem udep_combine {q q' : QVal bn} (h : UDep q) (h' : UDep q') : UDep (qcombine q q') :=
  fun x y hxy => by
    change q.util x + q'.util x = q.util y + q'.util y
    rw [h x y (fun w hw => hxy w (Finset.mem_union_left _ hw)),
      h' x y (fun w hw => hxy w (Finset.mem_union_right _ hw))]

theorem udep_collect {qs : List (QVal bn)} (h : ∀ q ∈ qs, UDep q) : UDep (qcollect qs) := by
  induction qs with
  | nil => exact udep_unit
  | cons q qs ih =>
    exact udep_combine (h q List.mem_cons_self) (ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))

theorem ratio_cast (n p : ℚ) : DVE.Valuation.ratio (n : ℝ) (p : ℝ) = ((ratioQ n p : ℚ) : ℝ) := by
  unfold DVE.Valuation.ratio ratioQ
  by_cases hp : p = 0
  · simp [hp]
  · have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    rw [if_neg hp', if_neg hp]
    push_cast
    rfl

theorem update_agree_of_notMem {S : Finset bn.V} {a : bn.V} (ha : a ∉ S) (x : bn.Assignment)
    (b : bn.states a) : ∀ w ∈ S, Function.update x a b w = x w := by
  intro w hw
  exact Function.update_of_ne (fun he => ha (by rw [← he]; exact hw)) _ _

/-- **Julia's `sum_out` is the real step `sumOutKeep (a ∉ uvars)`.** -/
theorem rel_sumOut {q : QVal bn} {v : DVE.Valuation bn} (h : Rel q v) (hu : UDep q) (a : bn.V) :
    Rel (qsumOut a q) (DVE.Valuation.sumOutKeep (decide (a ∉ q.uvars)) a v) := by
  have hprob : ∀ x, (DVE.Valuation.sumOut a v).prob x =
      ((∑ b, q.prob (Function.update x a b) : ℚ) : ℝ) := by
    intro x
    change ∑ b, v.prob (Function.update x a b) = _
    push_cast
    exact Finset.sum_congr rfl fun b _ => h.2.1 _
  refine ⟨?_, fun x => hprob x, fun x => ?_⟩
  · change q.scope.erase a = v.scope.erase a
    rw [h.1]
  · by_cases ha : a ∈ q.uvars
    · have hk : decide (a ∉ q.uvars) = false := by simp [ha]
      change (if decide (a ∉ q.uvars) = true ∧ (DVE.Valuation.sumOut a v).prob x = 0 then
          v.util (Function.update x a (Classical.choice (bn.nonemptyS a)))
        else (DVE.Valuation.sumOut a v).util x) = _
      rw [hk, if_neg (by simp)]
      change DVE.Valuation.ratio (∑ b, v.weight (Function.update x a b))
        (∑ b, v.prob (Function.update x a b)) = ((qsumOut a q).util x : ℝ)
      have hw : ∑ b, v.weight (Function.update x a b) =
          ((∑ b, q.prob (Function.update x a b) * q.util (Function.update x a b) : ℚ) : ℝ) := by
        push_cast
        exact Finset.sum_congr rfl fun b _ => by rw [DVE.Valuation.weight, h.2.1, h.2.2]
      have hp : ∑ b, v.prob (Function.update x a b) =
          ((∑ b, q.prob (Function.update x a b) : ℚ) : ℝ) := hprob x
      rw [hw, hp, ratio_cast]
      simp only [qsumOut, if_pos ha]
    · have hk : decide (a ∉ q.uvars) = true := by simp [ha]
      have hconst : ∀ b, q.util (Function.update x a b) = q.util x := fun b =>
        hu _ _ (update_agree_of_notMem ha x b)
      change (if decide (a ∉ q.uvars) = true ∧ (DVE.Valuation.sumOut a v).prob x = 0 then
          v.util (Function.update x a (Classical.choice (bn.nonemptyS a)))
        else (DVE.Valuation.sumOut a v).util x) = _
      have hq : (qsumOut a q).util x = q.util x := by simp only [qsumOut, if_neg ha]
      rw [hk, hq]
      by_cases hz : (DVE.Valuation.sumOut a v).prob x = 0
      · rw [if_pos ⟨rfl, hz⟩, h.2.2, hconst]
      · rw [if_neg (fun hh => hz hh.2)]
        change DVE.Valuation.ratio (∑ b, v.weight (Function.update x a b))
          (∑ b, v.prob (Function.update x a b)) = _
        have hz' : ∑ b, v.prob (Function.update x a b) ≠ 0 := hz
        have hw : ∑ b, v.weight (Function.update x a b) =
            (∑ b, v.prob (Function.update x a b)) * (q.util x : ℝ) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by rw [DVE.Valuation.weight, h.2.2, hconst]
        rw [hw, DVE.Valuation.ratio, if_neg hz', mul_div_cancel_left₀ _ hz']

theorem udep_sumOut {q : QVal bn} {v : DVE.Valuation bn} (hu : UDep q) (a : bn.V)
    (hr : Rel (qsumOut a q) v) : UDep (qsumOut a q) := by
  by_cases ha : a ∈ q.uvars
  · intro x y hxy
    apply hr.depUtil x y
    intro w hw
    apply hxy
    change w ∈ (if a ∈ q.uvars then q.scope.erase a else q.uvars)
    rw [if_pos ha]
    exact hw
  · intro x y hxy
    have hxy' : ∀ w ∈ q.uvars, x w = y w := by
      intro w hw
      apply hxy
      change w ∈ (if a ∈ q.uvars then q.scope.erase a else q.uvars)
      rw [if_neg ha]
      exact hw
    simp only [qsumOut, if_neg ha]
    exact hu x y hxy'

/-- A real function that is a rational one read in `ℝ` attains the rational maximum at
`argmax`. -/
theorem argmax_cast {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) (g : A → ℚ)
    (hfg : ∀ b, f b = g b) : f (DVE.Valuation.argmax f) =
      ((Finset.univ.sup' Finset.univ_nonempty g : ℚ) : ℝ) := by
  apply le_antisymm
  · rw [hfg]
    exact_mod_cast Finset.le_sup' g (Finset.mem_univ _)
  · obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := A)) g
    rw [hb, ← hfg]
    exact DVE.Valuation.le_argmax f b

/-- **Julia's `max_out` is the real step `maxOut`.** -/
theorem rel_maxOut {q : QVal bn} {v : DVE.Valuation bn} (h : Rel q v) (a : bn.V) :
    Rel (qmaxOut a q) (DVE.Valuation.maxOut a v) := by
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · change q.scope.erase a = v.scope.erase a
    rw [h.1]
  · change (fun b => v.prob (Function.update x a b))
      (DVE.Valuation.argmax fun b => v.prob (Function.update x a b)) = _
    exact argmax_cast _ _ fun b => h.2.1 _
  · change (fun b => v.util (Function.update x a b))
      (DVE.Valuation.argmax fun b => v.util (Function.update x a b)) = _
    exact argmax_cast _ _ fun b => h.2.2 _

theorem udep_maxOut {q : QVal bn} (hu : UDep q) (a : bn.V) : UDep (qmaxOut a q) := by
  intro x y hxy
  show Finset.univ.sup' Finset.univ_nonempty (fun b => q.util (Function.update x a b)) =
    Finset.univ.sup' Finset.univ_nonempty (fun b => q.util (Function.update y a b))
  congr 1
  funext b
  apply hu
  intro w hw
  by_cases hwa : w = a
  · subst hwa
    simp
  · rw [Function.update_of_ne hwa, Function.update_of_ne hwa]
    exact hxy w (Finset.mem_erase.2 ⟨hwa, hw⟩)

end QVal

/-! ## Permutations and filters -/

theorem collect_perm {bn : FinBayesNet} {vs ws : List (DVE.Valuation bn)} (h : vs.Perm ws) :
    DVE.Valuation.collect vs = DVE.Valuation.collect ws := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    change DVE.Valuation.combine x _ = DVE.Valuation.combine x _
    rw [ih]
  | swap x y l =>
    apply DVE.Valuation.ext'
    · change y.scope ∪ (x.scope ∪ _) = x.scope ∪ (y.scope ∪ _)
      exact Finset.union_left_comm _ _ _
    · funext z
      change y.prob z * (x.prob z * _) = x.prob z * (y.prob z * _)
      ring
    · funext z
      change y.util z + (x.util z + _) = x.util z + (y.util z + _)
      ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem forall₂_filter {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (hpq : ∀ a b, R a b → p a = q b) :
    List.Forall₂ R (l₁.filter p) (l₂.filter q) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b l₁ l₂ hr _ ih =>
    rw [List.filter_cons, List.filter_cons, hpq a b hr]
    by_cases hq : q b = true
    · rw [if_pos hq, if_pos hq]
      exact List.Forall₂.cons hr ih
    · rw [if_neg hq, if_neg hq]
      exact ih

/-! ## Tables over a checked diagram -/

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} {d : α} (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- The elements of a finite set of `Fin n`, in increasing order. -/
def finsetList {n : Nat} (F : Finset (Fin n)) : List (Fin n) := (List.finRange n).filter (· ∈ F)

theorem mem_finsetList {n : Nat} {F : Finset (Fin n)} {v : Fin n} : v ∈ finsetList F ↔ v ∈ F := by
  simp [finsetList]

/-- A valuation stored as tables: `keys` lists the coordinates of `vars` (the scope), and
`probT`, `utilT` the values at those coordinates. -/
structure TVal (r : Diagram) where
  scope : Finset (Fin r.nv)
  vars : List (Fin r.nv)
  uvars : Finset (Fin r.nv)
  keys : List (List Nat)
  probT : List ℚ
  utilT : List ℚ

variable (r : Diagram) (h : r.Valid)

/-- The coordinates of an assignment along a list of variables. -/
def keyOf (S : List (Fin r.nv)) (x : (r.compile h).Assignment) : List Nat :=
  S.map fun v => (x v).val

/-- The assignment with the given coordinates along `S` (state `0` elsewhere). -/
def decodeKey (S : List (Fin r.nv)) (k : List Nat) : (r.compile h).Assignment := fun v =>
  if hk : k.getD (S.idxOf v) 0 < r.stateCount v then ⟨_, hk⟩ else ⟨0, h.nonempty_states v⟩

/-- Tabulate a valuation over its scope. -/
def tab (q : QVal (r.compile h).toFinBayesNet) : TVal r :=
  let S := finsetList q.scope
  let keys := lexCoords (S.map r.stateCount)
  ⟨q.scope, S, q.uvars, keys, keys.map fun k => q.prob (decodeKey r h S k),
    keys.map fun k => q.util (decodeKey r h S k)⟩

/-- Read a tabulated valuation back. -/
def view (t : TVal r) : QVal (r.compile h).toFinBayesNet :=
  ⟨t.scope, t.uvars, fun x => t.probT.getD (t.keys.idxOf (keyOf r h t.vars x)) 0,
    fun x => t.utilT.getD (t.keys.idxOf (keyOf r h t.vars x)) 0⟩

theorem decodeKey_keyOf (S : List (Fin r.nv)) (x : (r.compile h).Assignment) :
    ∀ v ∈ S, decodeKey r h S (keyOf r h S x) v = x v := by
  intro v hv
  have hi : S.idxOf v < S.length := List.idxOf_lt_length_of_mem hv
  have hk : (keyOf r h S x).getD (S.idxOf v) 0 = (x v).val := by
    have hlen : S.idxOf v < (keyOf r h S x).length := by simpa [keyOf] using hi
    rw [getD_of_lt hlen]
    simp only [keyOf, List.getElem_map]
    exact congrArg (fun w => (x w).val) (List.getElem_idxOf hi)
  unfold decodeKey
  rw [dif_pos (by rw [hk]; exact (x v).isLt)]
  exact Fin.ext hk

theorem keyOf_mem (S : List (Fin r.nv)) (x : (r.compile h).Assignment) :
    keyOf r h S x ∈ lexCoords (S.map r.stateCount) := by
  rw [mem_lexCoords]
  unfold keyOf
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro v _
  exact (x v).isLt

theorem tab_read {q : QVal (r.compile h).toFinBayesNet} (f : (r.compile h).Assignment → ℚ)
    (hf : DepQ q.scope f) (x : (r.compile h).Assignment) :
    ((lexCoords ((finsetList q.scope).map r.stateCount)).map
        fun k => f (decodeKey r h (finsetList q.scope) k)).getD
      ((lexCoords ((finsetList q.scope).map r.stateCount)).idxOf
        (keyOf r h (finsetList q.scope) x)) 0 = f x := by
  have hmem := keyOf_mem r h (finsetList q.scope) x
  have hlt := List.idxOf_lt_length_of_mem hmem
  rw [getD_of_lt (by simpa using hlt), List.getElem_map, List.getElem_idxOf]
  apply hf
  intro w hw
  exact decodeKey_keyOf r h _ x w (mem_finsetList.2 hw)

/-- **Reading a tabulation back gives the tabulated valuation**, when its functions read only
its scope. -/
theorem view_tab (q : QVal (r.compile h).toFinBayesNet) (hp : DepQ q.scope q.prob)
    (hu : DepQ q.scope q.util) : view r h (tab r h q) = q := by
  cases q with
  | mk scope uvars prob util =>
    simp only [view, tab, QVal.mk.injEq, true_and]
    exact ⟨funext fun x => tab_read r h prob hp x, funext fun x => tab_read r h util hu x⟩

/-! ## The run on tables -/

/-- The bucket of `a`: the tables whose scope contains `a`. -/
def bucketT (a : Fin r.nv) (ts : List (TVal r)) : List (TVal r) :=
  ts.filter fun t => decide (a ∈ t.scope)

def outsideT (a : Fin r.nv) (ts : List (TVal r)) : List (TVal r) :=
  ts.filter fun t => decide (a ∉ t.scope)

/-- The combined bucket of `a`. -/
def bucketQ (a : Fin r.nv) (ts : List (TVal r)) : QVal (r.compile h).toFinBayesNet :=
  qcollect ((bucketT r a ts).map (view r h))

def chanceStepT (a : Fin r.nv) (ts : List (TVal r)) : List (TVal r) :=
  tab r h (qsumOut a (bucketQ r h a ts)) :: outsideT r a ts

def decisionStepT (a : Fin r.nv) (ts : List (TVal r)) : List (TVal r) :=
  tab r h (qmaxOut a (bucketQ r h a ts)) :: outsideT r a ts

/-- **The run on tables.** -/
def runT : {R : Finset (Fin r.nv)} → DVE.Plan (r.compile h) R → List (TVal r) → List (TVal r)
  | _, .done, ts => ts
  | _, .chance v _ _ next, ts => runT next (chanceStepT r h v ts)
  | _, .decision d _ _ next, ts => runT next (decisionStepT r h (r.decisions d).action ts)

/-- **The representative choice of the run**: at the step that sums `v`, keep the utility
potential exactly when `v` is not one of its variables (Julia's `sum_out`). -/
def keepOfT : {R : Finset (Fin r.nv)} → DVE.Plan (r.compile h) R → List (TVal r) →
    Fin r.nv → Bool
  | _, .done, _ => fun _ => false
  | _, .chance v _ _ next, ts =>
    Function.update (keepOfT next (chanceStepT r h v ts)) v
      (decide (v ∉ (bucketQ r h v ts).uvars))
  | _, .decision d _ _ next, ts => keepOfT next (decisionStepT r h (r.decisions d).action ts)

/-- **The score row the run maximizes for `d`**: the bucket utility when `d` is eliminated. -/
def scoreT : {R : Finset (Fin r.nv)} → DVE.Plan (r.compile h) R → List (TVal r) →
    (d : Fin r.nd) → (r.compile h).Assignment →
      Fin (r.stateCount (r.decisions d).action) → ℚ
  | _, .done, _, _ => fun _ _ => 0
  | _, .chance v _ _ next, ts, d => scoreT next (chanceStepT r h v ts) d
  | _, .decision d' _ _ next, ts, d =>
    if d' = d then fun x b =>
      (bucketQ r h (r.decisions d).action ts).util
        (Function.update x (r.decisions d).action b)
    else scoreT next (decisionStepT r h (r.decisions d').action ts) d

/-- A fixed assignment: state `0` everywhere. -/
def zeroAssignment : (r.compile h).Assignment := fun v => ⟨0, h.nonempty_states v⟩

/-- **The value of the run**: the utility of the final valuations. -/
def valueT {R : Finset (Fin r.nv)} (plan : DVE.Plan (r.compile h) R) (ts : List (TVal r)) : ℚ :=
  (qcollect ((runT r h plan ts).map (view r h))).util (zeroAssignment r h)

/-! ## The plan of an elimination order -/

/-- **The plan of an elimination order**: each variable in turn, a decision's action exactly when
the remaining variables are its information set and the action. `none` if the order is not such
a plan. -/
def planOf : List (Fin r.nv) → (R : Finset (Fin r.nv)) → Option (DVE.Plan (r.compile h) R)
  | [], R => if hR : R = ∅ then some (hR ▸ DVE.Plan.done) else none
  | v :: vs, R =>
    if hv : v ∈ R then
      match hd : (List.finRange r.nd).find? (fun d => decide ((r.decisions d).action = v)) with
      | some d =>
        if hi : R.erase (r.decisions d).action = (r.compile h).info d then
          (planOf vs (R.erase (r.decisions d).action)).map fun next =>
            DVE.Plan.decision (id := r.compile h) d
              (by
                have hdv : (r.decisions d).action = v := by
                  simpa using List.find?_some hd
                change (r.decisions d).action ∈ R
                rw [hdv]
                exact hv) hi next
        else none
      | none =>
        (planOf vs (R.erase v)).map fun next =>
          DVE.Plan.chance (id := r.compile h) v hv
            (fun d hdv => by
              have := List.find?_eq_none.1 hd d (List.mem_finRange d)
              simp only [decide_eq_true_eq] at this
              exact this hdv) next
    else none

/-- Zero-based variable indices to `Fin`, if all are in range. -/
def toFinList : List Nat → Option (List (Fin r.nv))
  | [] => some []
  | v :: vs => if hv : v < r.nv then (toFinList vs).map (⟨v, hv⟩ :: ·) else none

/-! ## Simulation -/

/-- **The tables simulate the real valuations**, up to their order. -/
def Sim (ts : List (TVal r)) (vs : List (DVE.Valuation (r.compile h).toFinBayesNet)) : Prop :=
  (∃ ws, ws.Perm vs ∧ List.Forall₂ (fun t v => Rel (view r h t) v) ts ws) ∧
    ∀ t ∈ ts, UDep (view r h t)

theorem Sim.bucket {ts : List (TVal r)} {vs : List (DVE.Valuation (r.compile h).toFinBayesNet)}
    (hs : Sim r h ts vs) (a : Fin r.nv) :
    Rel (bucketQ r h a ts) (DVE.Valuation.collect (DVE.Valuation.bucket a vs)) ∧
      UDep (bucketQ r h a ts) := by
  obtain ⟨⟨ws, hperm, hf⟩, hu⟩ := hs
  have hfB : List.Forall₂ (fun t v => Rel (view r h t) v) (bucketT r a ts)
      (DVE.Valuation.bucket a ws) :=
    forall₂_filter hf fun t v hr => by
      change decide (a ∈ (view r h t).scope) = _
      rw [hr.1]
  have hcp : DVE.Valuation.collect (DVE.Valuation.bucket a ws) =
      DVE.Valuation.collect (DVE.Valuation.bucket a vs) :=
    collect_perm (hperm.filter _)
  refine ⟨?_, ?_⟩
  · rw [← hcp]
    exact rel_collect (List.forall₂_map_left_iff.2 hfB)
  · apply udep_collect
    intro q hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hq
    exact hu t (List.mem_of_mem_filter ht)

theorem Sim.outside {ts : List (TVal r)} {vs : List (DVE.Valuation (r.compile h).toFinBayesNet)}
    (hs : Sim r h ts vs) (a : Fin r.nv) :
    ∃ ws, ws.Perm (DVE.Valuation.outside a vs) ∧
      List.Forall₂ (fun t v => Rel (view r h t) v) (outsideT r a ts) ws := by
  obtain ⟨⟨ws, hperm, hf⟩, -⟩ := hs
  refine ⟨DVE.Valuation.outside a ws, hperm.filter _, forall₂_filter hf fun t v hr => ?_⟩
  change decide (a ∉ (view r h t).scope) = _
  rw [hr.1]

theorem Sim.chance {ts : List (TVal r)} {vs : List (DVE.Valuation (r.compile h).toFinBayesNet)}
    (hs : Sim r h ts vs) (a : Fin r.nv) (k : Bool) (hk : k = decide (a ∉ (bucketQ r h a ts).uvars)) :
    Sim r h (chanceStepT r h a ts) (DVE.Valuation.chanceStepKeep k a vs) := by
  obtain ⟨hrel, hud⟩ := hs.bucket r h a
  have hrs := rel_sumOut hrel hud a
  rw [← hk] at hrs
  have hview := view_tab r h _ hrs.depProb hrs.depUtil
  obtain ⟨ws, hperm, hf⟩ := hs.outside r h a
  refine ⟨⟨_ :: ws, List.Perm.cons _ hperm, List.Forall₂.cons (by rw [hview]; exact hrs) hf⟩, ?_⟩
  intro t ht
  rcases List.mem_cons.1 ht with rfl | ht
  · rw [hview]
    exact udep_sumOut hud a hrs
  · exact hs.2 t (List.mem_of_mem_filter ht)

theorem Sim.decision {ts : List (TVal r)} {vs : List (DVE.Valuation (r.compile h).toFinBayesNet)}
    (hs : Sim r h ts vs) (a : Fin r.nv) :
    Sim r h (decisionStepT r h a ts) (DVE.Valuation.decisionStep a vs) := by
  obtain ⟨hrel, hud⟩ := hs.bucket r h a
  have hrs := rel_maxOut hrel a
  have hview := view_tab r h _ hrs.depProb hrs.depUtil
  obtain ⟨ws, hperm, hf⟩ := hs.outside r h a
  refine ⟨⟨_ :: ws, List.Perm.cons _ hperm, List.Forall₂.cons (by rw [hview]; exact hrs) hf⟩, ?_⟩
  intro t ht
  rcases List.mem_cons.1 ht with rfl | ht
  · rw [hview]
    exact udep_maxOut hud a
  · exact hs.2 t (List.mem_of_mem_filter ht)

/-- **The simulation theorem.** If the tables simulate the real valuations and `keep` is the
run's representative choice on the remaining variables, then after the plan they still do, and
every decision's score row is the rational one read in `ℝ`. -/
theorem sim_runRep {R : Finset (r.compile h).V} (plan : DVE.Plan (r.compile h) R)
    (s : DVE.State (r.compile h) R) (ts : List (TVal r)) (keep : Fin r.nv → Bool)
    (hs : Sim r h ts s.valuations) (hk : ∀ v ∈ R, keep v = keepOfT r h plan ts v) :
    Sim r h (runT r h plan ts) (DVE.runRepState keep plan s).valuations ∧
      ∀ (d : Fin r.nd) x b, DVE.decisionScoreRep keep plan s d x b =
        (scoreT r h plan ts d x b : ℝ) := by
  induction plan generalizing ts with
  | done => exact ⟨hs, fun _ _ _ => by simp [DVE.decisionScoreRep, scoreT]⟩
  | @chance R v hv hc next ih =>
    have hkv : keep v = decide (v ∉ (bucketQ r h v ts).uvars) := by
      rw [hk v hv]
      simp only [keepOfT, Function.update_self]
    have hs' := hs.chance r h v (keep v) hkv
    have hk' : ∀ w ∈ R.erase v, keep w = keepOfT r h next (chanceStepT r h v ts) w := by
      intro w hw
      rw [hk w (Finset.mem_of_mem_erase hw)]
      simp only [keepOfT]
      exact Function.update_of_ne (Finset.ne_of_mem_erase hw) _ _
    refine ih (s.chanceKeep keep v) (chanceStepT r h v ts) ?_ ?_
    · exact hs'
    · exact hk'
  | @decision R d' hd hi next ih =>
    have hs' := hs.decision r h (r.decisions d').action
    have hk' : ∀ w ∈ R.erase ((r.compile h).action d'),
        keep w = keepOfT r h next (decisionStepT r h (r.decisions d').action ts) w := by
      intro w hw
      rw [hk w (Finset.mem_of_mem_erase hw)]
      rfl
    obtain ⟨hrun, hscore⟩ := ih (s.decision d') (decisionStepT r h (r.decisions d').action ts)
      hs' hk'
    refine ⟨hrun, fun d x b => ?_⟩
    simp only [DVE.decisionScoreRep, scoreT]
    by_cases hdd : d' = d
    · subst hdd
      rw [if_pos rfl, if_pos rfl]
      exact (hs.bucket r h _).1.2.2 _
    · rw [if_neg hdd, if_neg hdd]
      exact hscore d x b

/-! ## The certificate's run -/

variable (c : Certificate)

/-- The certificate's kernel over `ℚ`. -/
def certKernelQ (m : Fin r.nm) (x : (r.compile h).Assignment)
    (a : Fin (r.stateCount (r.mechanisms m).target)) : ℚ :=
  match c.mechanisms[m.val]? with
  | some e => cellValue e.cpt (coordsOf r h x (e.parents.map Slot.var) ++ [a.val])
  | none => 0

/-- The certificate's utilities over `ℚ`. -/
def certUtilityQ (j : Fin r.nu) (x : (r.compile h).Assignment) : ℚ :=
  match c.utilities[j.val]? with
  | some e => cellValue e.table (coordsOf r h x (e.inputs.map Slot.var))
  | none => 0

theorem certKernel_eq_cast (m : Fin r.nm) (x : (r.compile h).Assignment)
    (a : Fin (r.stateCount (r.mechanisms m).target)) :
    certKernel r h c m x a = (certKernelQ r h c m x a : ℝ) := by
  unfold certKernel certKernelQ
  cases c.mechanisms[m.val]? with
  | none => simp
  | some e => simp

theorem certUtility_eq_cast (j : Fin r.nu) (x : (r.compile h).Assignment) :
    certUtility r h c j x = (certUtilityQ r h c j x : ℝ) := by
  unfold certUtility certUtilityQ
  cases c.utilities[j.val]? with
  | none => simp
  | some e => simp

/-- The initial valuation of mechanism `m`: `(κ_m, 0)`. -/
def chanceQ (m : Fin r.nm) : QVal (r.compile h).toFinBayesNet :=
  ⟨insert ((r.compile h).target m) ((r.compile h).parents m), ∅,
    fun x => certKernelQ r h c m x (x ((r.compile h).target m)), fun _ => 0⟩

/-- The initial valuation of utility `j`: `(1, u_j)`. -/
def utilityQ (j : Fin r.nu) : QVal (r.compile h).toFinBayesNet :=
  ⟨(r.compile h).uscope j, (r.compile h).uscope j, fun _ => 1, certUtilityQ r h c j⟩

/-- **The initial tables**: the mechanisms, then the utilities, in part order. -/
def initT : List (TVal r) :=
  (List.finRange r.nm).map (fun m => tab r h (chanceQ r h c m)) ++
    (List.finRange r.nu).map (fun j => tab r h (utilityQ r h c j))

theorem finRange_perm_toList (n : Nat) : (List.finRange n).Perm (Finset.univ : Finset (Fin n)).toList :=
  (List.perm_ext_iff_of_nodup (List.nodup_finRange n) (Finset.nodup_toList _)).2 fun a => by simp

theorem sim_initial (hm : Matches r c) (hn : Nonneg c) :
    Sim r h (initT r h c) (DVE.initial (certKernel r h c) (certKernel_local hm h)
      (certKernel_nonneg hn h) (certUtility r h c) (certUtility_local hm h)).valuations := by
  have hrc : ∀ m, Rel (chanceQ r h c m) (DVE.chanceValuation (certKernel r h c)
      (certKernel_local hm h) (certKernel_nonneg hn h) m) := fun m =>
    ⟨rfl, fun x => certKernel_eq_cast r h c m x _, fun x => by simp [chanceQ, DVE.chanceValuation]⟩
  have hru : ∀ j, Rel (utilityQ r h c j) (DVE.utilityValuation (certUtility r h c)
      (certUtility_local hm h) j) := fun j =>
    ⟨rfl, fun x => by simp [utilityQ, DVE.utilityValuation], fun x => certUtility_eq_cast r h c j x⟩
  refine ⟨⟨(List.finRange r.nm).map (DVE.chanceValuation (certKernel r h c) (certKernel_local hm h)
      (certKernel_nonneg hn h)) ++
    (List.finRange r.nu).map (DVE.utilityValuation (certUtility r h c) (certUtility_local hm h)),
    List.Perm.append ((finRange_perm_toList r.nm).map _) ((finRange_perm_toList r.nu).map _),
    ?_⟩, ?_⟩
  · refine List.rel_append ?_ ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro m _
      rw [view_tab r h _ (hrc m).depProb (hrc m).depUtil]
      exact hrc m
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro j _
      rw [view_tab r h _ (hru j).depProb (hru j).depUtil]
      exact hru j
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 ht
      rw [view_tab r h _ (hrc m).depProb (hrc m).depUtil]
      exact fun _ _ _ => rfl
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
      rw [view_tab r h _ (hru j).depProb (hru j).depUtil]
      exact (hru j).depUtil

/-- **The exact run is computed.** For a certificate that matches the checked diagram and has
nonnegative cells, and for any plan, the representative run with `keep := keepOfT plan` (Julia's
`sum_out` branch) and any selector has the value `valueT` and the score rows `scoreT`, read in
`ℝ`. -/
theorem exactRun_spec (hm : Matches r c) (hn : Nonneg c) (sel : DVE.Selector (r.compile h))
    (plan : DVE.Plan (r.compile h) Finset.univ) :
    (DVE.solveRepPlanWith sel (keepOfT r h plan (initT r h c)) (certKernel r h c)
        (certKernel_local hm h) (certKernel_nonneg hn h) (certUtility r h c)
        (certUtility_local hm h) plan).value = (valueT r h plan (initT r h c) : ℝ) ∧
      ∀ (d : Fin r.nd) x b, DVE.solveRepPlanScore (keepOfT r h plan (initT r h c))
          (certKernel r h c) (certKernel_local hm h) (certKernel_nonneg hn h)
          (certUtility r h c) (certUtility_local hm h) plan d x b =
        (scoreT r h plan (initT r h c) d x b : ℝ) := by
  obtain ⟨hsim, hscore⟩ := sim_runRep r h plan _ (initT r h c) (keepOfT r h plan (initT r h c))
    (sim_initial r h c hm hn) (fun _ _ => rfl)
  refine ⟨?_, hscore⟩
  unfold DVE.solveRepPlanWith valueT
  simp only
  rw [DVE.runRepWith_state]
  obtain ⟨⟨ws, hperm, hf⟩, -⟩ := hsim
  have hrel := rel_collect (List.forall₂_map_left_iff.2 hf)
  rw [collect_perm hperm] at hrel
  rw [← hrel.2.2]
  apply DVE.Valuation.util_local
  intro w hw
  have := (DVE.runRepState (keepOfT r h plan (initT r h c)) plan
    (DVE.initial (certKernel r h c) (certKernel_local hm h) (certKernel_nonneg hn h)
      (certUtility r h c) (certUtility_local hm h))).supported hw
  simp at this

end InfluenceDiagramsProofs.DVECertificate
