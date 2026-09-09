import InfluenceDiagramsProofs.Finite.OptimalInformation
import BayesianNetworksProofs.Finite.VariableElimination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Exact probability/utility valuations

Source: `InfluenceDiagrams.jl/src/valuation.jl`, frozen in the second review packet.
Combination multiplies probability potentials and adds divided utilities. Chance elimination
uses a weighted sum divided by its mass, with zero denominator giving zero. Nonnegative
probabilities prove that a zero denominator also has zero weighted numerator.

Scopes are sufficient dependency sets, not array layouts. The decision operation selects a
local utility maximizer and drops the probability axis by its maximum, as in the source.
Global constancy is derived structurally in `Semantics.lean`. The elementary cancellation
lemma below gives bucket constancy on nonzero-outside contexts; `Guard/Complete.lean` now
extends the exact diagnostic to every row, including zero outside mass.
Ties in `argmax` use a fixed classical choice, not the Julia first-label rule.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

noncomputable section

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet

variable {bn : FinBayesNet}

def Depends (S : Finset bn.V) (f : bn.Assignment → ℝ) : Prop :=
  ∀ x y, (∀ v ∈ S, x v = y v) → f x = f y

structure Valuation (bn : FinBayesNet) where
  scope : Finset bn.V
  prob : bn.Assignment → ℝ
  util : bn.Assignment → ℝ
  prob_local : Depends scope prob
  util_local : Depends scope util
  nonneg : ∀ x, 0 ≤ prob x

namespace Valuation

def weight (v : Valuation bn) (x : bn.Assignment) : ℝ := v.prob x * v.util x

def unit : Valuation bn where
  scope := ∅
  prob := fun _ => 1
  util := fun _ => 0
  prob_local := fun _ _ _ => rfl
  util_local := fun _ _ _ => rfl
  nonneg := fun _ => zero_le_one

def combine (v w : Valuation bn) : Valuation bn where
  scope := v.scope ∪ w.scope
  prob x := v.prob x * w.prob x
  util x := v.util x + w.util x
  prob_local x y h := by
    dsimp only
    rw [v.prob_local x y (fun a ha => h a (Finset.mem_union_left _ ha)),
      w.prob_local x y (fun a ha => h a (Finset.mem_union_right _ ha))]
  util_local x y h := by
    dsimp only
    rw [v.util_local x y (fun a ha => h a (Finset.mem_union_left _ ha)),
      w.util_local x y (fun a ha => h a (Finset.mem_union_right _ ha))]
  nonneg x := mul_nonneg (v.nonneg x) (w.nonneg x)

def collect : List (Valuation bn) → Valuation bn
  | [] => unit
  | v :: vs => combine v (collect vs)

def bucket (a : bn.V) (vs : List (Valuation bn)) : List (Valuation bn) :=
  vs.filter (fun v => decide (a ∈ v.scope))

def outside (a : bn.V) (vs : List (Valuation bn)) : List (Valuation bn) :=
  vs.filter (fun v => decide (a ∉ v.scope))

theorem collect_scope (vs : List (Valuation bn)) {v : Valuation bn} (hv : v ∈ vs) :
    v.scope ⊆ (collect vs).scope := by
  induction vs with
  | nil => simp at hv
  | cons w ws ih =>
    rcases List.mem_cons.1 hv with rfl | hv
    · exact Finset.subset_union_left
    · exact (ih hv).trans Finset.subset_union_right

theorem outside_notMem (a : bn.V) (vs : List (Valuation bn)) :
    a ∉ (collect (outside a vs)).scope := by
  induction vs with
  | nil => simp [outside, collect, unit]
  | cons v vs ih =>
    by_cases h : a ∈ v.scope <;> simpa [outside, collect, combine, h] using ih

theorem collect_partition (a : bn.V) (vs : List (Valuation bn)) (x : bn.Assignment) :
    (collect vs).prob x =
        (collect (bucket a vs)).prob x * (collect (outside a vs)).prob x ∧
      (collect vs).util x =
        (collect (bucket a vs)).util x + (collect (outside a vs)).util x := by
  induction vs with
  | nil => simp [bucket, outside, collect, unit]
  | cons v vs ih =>
    by_cases h : a ∈ v.scope <;>
      simp [bucket, outside, collect, combine, h] at * <;>
      rcases ih with ⟨hp, hu⟩ <;> rw [hp, hu] <;> constructor <;> ring

theorem collect_partition_scope (a : bn.V) (vs : List (Valuation bn)) :
    (collect vs).scope =
      (collect (bucket a vs)).scope ∪ (collect (outside a vs)).scope := by
  induction vs with
  | nil => simp [bucket, outside, collect, unit]
  | cons v vs ih =>
    by_cases h : a ∈ v.scope <;>
      simp [bucket, outside, collect, combine, h] at * <;> (rw [ih]; try ac_rfl)

theorem prob_update_of_notMem (v : Valuation bn) {a : bn.V} (ha : a ∉ v.scope)
    (x : bn.Assignment) (b : bn.states a) : v.prob (Function.update x a b) = v.prob x := by
  apply v.prob_local
  intro w hw
  exact Function.update_of_ne (show w ≠ a from fun he => ha (he ▸ hw)) _ _

theorem util_update_of_notMem (v : Valuation bn) {a : bn.V} (ha : a ∉ v.scope)
    (x : bn.Assignment) (b : bn.states a) : v.util (Function.update x a b) = v.util x := by
  apply v.util_local
  intro w hw
  exact Function.update_of_ne (show w ≠ a from fun he => ha (he ▸ hw)) _ _

theorem update_agree {S : Finset bn.V} {a : bn.V} {x y : bn.Assignment}
    (h : ∀ v ∈ S.erase a, x v = y v) (b : bn.states a) :
    ∀ v ∈ S, Function.update x a b v = Function.update y a b v := by
  intro v hv
  by_cases he : v = a
  · subst v
    simp
  · simp only [Function.update_of_ne he]
    exact h v (Finset.mem_erase.2 ⟨he, hv⟩)

def ratio (n p : ℝ) : ℝ := if p = 0 then 0 else n / p

theorem mass_mul_ratio {n p : ℝ} (h : p = 0 → n = 0) : p * ratio n p = n := by
  by_cases hp : p = 0
  · simp [ratio, hp, h hp]
  · simp [ratio, hp, mul_div_cancel₀]

theorem weighted_sum_zero {A : Type} [Fintype A] (p u : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hz : ∑ a, p a = 0) : ∑ a, p a * u a = 0 := by
  have h : ∀ a, p a = 0 := by
    intro a
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hp a)).1 hz a (Finset.mem_univ _)
  simp [h]

def sumOut (a : bn.V) (v : Valuation bn) : Valuation bn where
  scope := v.scope.erase a
  prob x := ∑ b, v.prob (Function.update x a b)
  util x := ratio (∑ b, v.weight (Function.update x a b))
    (∑ b, v.prob (Function.update x a b))
  prob_local x y h := Finset.sum_congr rfl fun b _ => v.prob_local _ _ (update_agree h b)
  util_local x y h := by
    dsimp only
    apply congrArg₂ ratio <;> apply Finset.sum_congr rfl <;> intro b _
    · simp only [weight, v.prob_local _ _ (update_agree h b),
        v.util_local _ _ (update_agree h b)]
    · exact v.prob_local _ _ (update_agree h b)
  nonneg x := Finset.sum_nonneg fun b _ => v.nonneg _

/-- This includes zero-probability rows; no division by a positive number is assumed. -/
theorem sumOut_weight (a : bn.V) (v : Valuation bn) (x : bn.Assignment) :
    (sumOut a v).weight x = ∑ b, v.weight (Function.update x a b) := by
  apply mass_mul_ratio
  exact weighted_sum_zero _ _ (fun b => v.nonneg _)

noncomputable def argmax {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) : A :=
  Classical.choose (Finset.exists_max_image Finset.univ f Finset.univ_nonempty)

theorem le_argmax {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) (a : A) :
    f a ≤ f (argmax f) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ f Finset.univ_nonempty)).2 a
    (Finset.mem_univ a)

noncomputable def choice (a : bn.V) (v : Valuation bn) (x : bn.Assignment) : bn.states a :=
  argmax fun b => v.util (Function.update x a b)

theorem choice_local (a : bn.V) (v : Valuation bn) (x y : bn.Assignment)
    (h : ∀ w ∈ v.scope.erase a, x w = y w) : choice a v x = choice a v y := by
  apply congrArg argmax
  funext b
  exact v.util_local _ _ (update_agree h b)

def probabilityChoice (a : bn.V) (v : Valuation bn) (x : bn.Assignment) : bn.states a :=
  argmax fun b => v.prob (Function.update x a b)

theorem probabilityChoice_local (a : bn.V) (v : Valuation bn) (x y : bn.Assignment)
    (h : ∀ w ∈ v.scope.erase a, x w = y w) :
    probabilityChoice a v x = probabilityChoice a v y := by
  apply congrArg argmax
  funext b
  exact v.prob_local _ _ (update_agree h b)

noncomputable def maxOut (a : bn.V) (v : Valuation bn) : Valuation bn where
  scope := v.scope.erase a
  prob x := v.prob (Function.update x a (probabilityChoice a v x))
  util x := v.util (Function.update x a (choice a v x))
  prob_local x y h := by
    dsimp only
    rw [probabilityChoice_local a v x y h]
    exact v.prob_local _ _ (update_agree h _)
  util_local x y h := by
    dsimp only
    rw [choice_local a v x y h]
    exact v.util_local _ _ (update_agree h _)
  nonneg x := v.nonneg _

def chanceStep (a : bn.V) (vs : List (Valuation bn)) : List (Valuation bn) :=
  sumOut a (collect (bucket a vs)) :: outside a vs

noncomputable def decisionStep (a : bn.V) (vs : List (Valuation bn)) : List (Valuation bn) :=
  maxOut a (collect (bucket a vs)) :: outside a vs

theorem chanceStep_prob (a : bn.V) (vs : List (Valuation bn)) (x : bn.Assignment) :
    (collect (chanceStep a vs)).prob x = ∑ b, (collect vs).prob (Function.update x a b) := by
  change (∑ b, (collect (bucket a vs)).prob (Function.update x a b)) *
    (collect (outside a vs)).prob x = _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [(collect_partition a vs _).1, prob_update_of_notMem _ (outside_notMem a vs)]

/-- Full bucket identity, including the utility contribution of untouched valuations. -/
theorem chanceStep_weight (a : bn.V) (vs : List (Valuation bn)) (x : bn.Assignment) :
    (collect (chanceStep a vs)).weight x =
      ∑ b, (collect vs).weight (Function.update x a b) := by
  let v := collect (bucket a vs)
  let r := collect (outside a vs)
  have hw := sumOut_weight a v x
  change (sumOut a v).prob x * (sumOut a v).util x = _ at hw
  change ((sumOut a v).prob x * r.prob x) * ((sumOut a v).util x + r.util x) = _
  calc
    _ = r.prob x * ((∑ b, v.weight (Function.update x a b)) +
        (∑ b, v.prob (Function.update x a b)) * r.util x) := by
      rw [← hw]
      change (sumOut a v).prob x * r.prob x * ((sumOut a v).util x + r.util x) =
        r.prob x * ((sumOut a v).prob x * (sumOut a v).util x +
          (sumOut a v).prob x * r.util x)
      ring
    _ = _ := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [weight]
      rw [(collect_partition a vs _).1, (collect_partition a vs _).2,
        prob_update_of_notMem _ (outside_notMem a vs),
        util_update_of_notMem _ (outside_notMem a vs)]
      dsimp [v, r, weight]
      ring

theorem decisionStep_eval (a : bn.V) (vs : List (Valuation bn))
    (hp : ∀ x b, (collect vs).prob (Function.update x a b) = (collect vs).prob x)
    (x : bn.Assignment) :
    let y := Function.update x a (choice a (collect (bucket a vs)) x)
    (collect (decisionStep a vs)).prob x = (collect vs).prob y ∧
      (collect (decisionStep a vs)).util x = (collect vs).util y := by
  dsimp only
  constructor
  · have he : (collect (decisionStep a vs)).prob x =
        (collect vs).prob (Function.update x a (probabilityChoice a (collect (bucket a vs)) x)) := by
      rw [(collect_partition a vs _).1, prob_update_of_notMem _ (outside_notMem a vs)]
      rfl
    rw [he, hp, hp]
  · rw [(collect_partition a vs _).2, util_update_of_notMem _ (outside_notMem a vs)]
    rfl

/-- The literal bucket probability guard is justified on every nonzero-outside context.
At zero outside mass, the whole configuration is unreachable and cancellation is invalid. -/
theorem bucket_probability_constant_on_support (a : bn.V) (vs : List (Valuation bn))
    (hp : ∀ x b, (collect vs).prob (Function.update x a b) = (collect vs).prob x)
    (x : bn.Assignment) (hout : (collect (outside a vs)).prob x ≠ 0) (b : bn.states a) :
    (collect (bucket a vs)).prob (Function.update x a b) = (collect (bucket a vs)).prob x := by
  apply mul_right_cancel₀ hout
  have h := hp x b
  rw [(collect_partition a vs _).1, (collect_partition a vs _).1,
    prob_update_of_notMem _ (outside_notMem a vs)] at h
  exact h

/-- The global probability-independence obligation is explicit and not assumed by the driver.
Later modules derive it from the causal order and normalisation. -/
theorem decisionStep_dominates (a : bn.V) (vs : List (Valuation bn))
    (hp : ∀ x b, (collect vs).prob (Function.update x a b) = (collect vs).prob x)
    (x : bn.Assignment) (b : bn.states a) :
    (collect vs).weight (Function.update x a b) ≤ (collect (decisionStep a vs)).weight x := by
  rw [weight, weight, (decisionStep_eval a vs hp x).1, (decisionStep_eval a vs hp x).2, hp, hp]
  apply mul_le_mul_of_nonneg_left _ ((collect vs).nonneg x)
  rw [(collect_partition a vs _).2, (collect_partition a vs _).2,
    util_update_of_notMem _ (outside_notMem a vs),
    util_update_of_notMem _ (outside_notMem a vs)]
  exact add_le_add (le_argmax (fun b => (collect (bucket a vs)).util
    (Function.update x a b)) b) (le_refl _)

theorem filter_scope_subset (p : Valuation bn → Bool) (vs : List (Valuation bn)) :
    (collect (vs.filter p)).scope ⊆ (collect vs).scope := by
  induction vs with
  | nil => exact Finset.Subset.refl _
  | cons v vs ih =>
    by_cases h : p v
    · simp only [List.filter_cons, h, ↓reduceIte, collect, combine]
      exact Finset.union_subset_union (Finset.Subset.refl _) ih
    · simp only [List.filter_cons, h, Bool.false_eq_true, ↓reduceIte, collect, combine]
      exact ih.trans Finset.subset_union_right

theorem step_scope (a : bn.V) (vs : List (Valuation bn))
    (reduce : Valuation bn → Valuation bn) (hr : ∀ v, (reduce v).scope = v.scope.erase a) :
    (collect (reduce (collect (bucket a vs)) :: outside a vs)).scope ⊆
      (collect vs).scope.erase a := by
  change (reduce _).scope ∪ (collect (outside a vs)).scope ⊆ _
  rw [hr]
  apply Finset.union_subset
  · exact Finset.erase_subset_erase a (filter_scope_subset _ vs)
  · intro w hw
    refine Finset.mem_erase.2 ⟨?_, filter_scope_subset _ vs hw⟩
    exact fun he => outside_notMem a vs (he ▸ hw)

theorem step_scope_eq (a : bn.V) (vs : List (Valuation bn))
    (reduce : Valuation bn → Valuation bn) (hr : ∀ v, (reduce v).scope = v.scope.erase a) :
    (collect (reduce (collect (bucket a vs)) :: outside a vs)).scope =
      (collect vs).scope.erase a := by
  change (reduce _).scope ∪ (collect (outside a vs)).scope = _
  rw [hr, collect_partition_scope a vs]
  ext w
  by_cases hw : w = a
  · subst w
    simp [outside_notMem a vs]
  · simp [hw]

end Valuation
end
end InfluenceDiagramsProofs.DVE
