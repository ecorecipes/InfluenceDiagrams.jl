import InfluenceDiagramsProofs.Finite.DVE.Guard.Positive
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Data.List.Forall2

/-!
# Probability-expression provenance

Probability potentials use only original chance kernels, the optional likelihood, one,
finite products, finite sums and finite maxima. Utility divisions and utility argmax choices
do not enter this language. The symbolic bucket trace retains the actual sufficient scopes,
so its partitions are exactly those of the numerical driver.

The maximum *value* is continuous even though a chosen maximizing action need not be.
This distinction is essential for extending the positive-input guard identity to zero rows.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE.Guard

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

variable {id : FinInfluenceDiagram}

inductive Expr (id : FinInfluenceDiagram)
  | one
  | chance (m : id.M)
  | likelihood
  | mul (f g : Expr id)
  | sum (v : id.V) (f : Expr id)
  | max (v : id.V) (f : Expr id)

def Expr.eval (κ : id.Kernel ℝ) (L : id.Assignment → ℝ) :
    Expr id → id.Assignment → ℝ
  | .one, _ => 1
  | .chance m, x => κ m x (x (id.target m))
  | .likelihood, x => L x
  | .mul f g, x => f.eval κ L x * g.eval κ L x
  | .sum v f, x => ∑ a, f.eval κ L (Function.update x v a)
  | .max v f, x => f.eval κ L
      (Function.update x v (argmax fun a => f.eval κ L (Function.update x v a)))

structure Symbolic (id : FinInfluenceDiagram) where
  scope : Finset id.V
  expr : Expr id

namespace Symbolic

def collect : List (Symbolic id) → Symbolic id
  | [] => ⟨∅, .one⟩
  | v :: vs =>
    ⟨v.scope ∪ (collect vs).scope, .mul v.expr (collect vs).expr⟩

def bucket (a : id.V) (vs : List (Symbolic id)) : List (Symbolic id) :=
  vs.filter fun v => decide (a ∈ v.scope)

def outside (a : id.V) (vs : List (Symbolic id)) : List (Symbolic id) :=
  vs.filter fun v => decide (a ∉ v.scope)

def chanceStep (a : id.V) (vs : List (Symbolic id)) : List (Symbolic id) :=
  ⟨(collect (bucket a vs)).scope.erase a, .sum a (collect (bucket a vs)).expr⟩ :: outside a vs

def decisionStep (a : id.V) (vs : List (Symbolic id)) : List (Symbolic id) :=
  ⟨(collect (bucket a vs)).scope.erase a, .max a (collect (bucket a vs)).expr⟩ :: outside a vs

def trace {R : Finset id.V} (plan : Plan id R) (vs : List (Symbolic id)) :
    List (id.V × Expr id) :=
  match plan with
  | .done => []
  | .chance a _ _ next => trace next (chanceStep a vs)
  | .decision d _ _ next =>
    (id.action d, (collect (bucket (id.action d) vs)).expr) :: trace next (decisionStep (id.action d) vs)

def initial (id : FinInfluenceDiagram) : List (Symbolic id) :=
  Finset.univ.toList.map (fun m => ⟨insert (id.target m) (id.parents m), .chance m⟩) ++
    Finset.univ.toList.map (fun u => ⟨id.uscope u, .one⟩)

def initialEvidence (id : FinInfluenceDiagram) (A : Finset id.V) : List (Symbolic id) :=
  ⟨A, .likelihood⟩ :: initial id

end Symbolic

def Represents (κ : id.Kernel ℝ) (L : id.Assignment → ℝ)
    (v : Valuation id.toFinBayesNet) (s : Symbolic id) : Prop :=
  v.scope = s.scope ∧ ∀ x, v.prob x = s.expr.eval κ L x

def RepresentsList (κ : id.Kernel ℝ) (L : id.Assignment → ℝ)
    (vs : List (Valuation id.toFinBayesNet)) (ss : List (Symbolic id)) : Prop :=
  List.Forall₂ (Represents κ L) vs ss

theorem RepresentsList.collect {κ : id.Kernel ℝ} {L : id.Assignment → ℝ}
    {vs : List (Valuation id.toFinBayesNet)} {ss : List (Symbolic id)}
    (h : RepresentsList κ L vs ss) :
    Represents κ L (Valuation.collect vs) (Symbolic.collect ss) := by
  induction h with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | @cons v s vs ss hv hs ih =>
    constructor
    · exact congrArg₂ (fun S T : Finset id.V => S ∪ T) hv.1 ih.1
    · intro x
      change v.prob x * (Valuation.collect vs).prob x =
        s.expr.eval κ L x * (Symbolic.collect ss).expr.eval κ L x
      rw [hv.2, ih.2]

theorem RepresentsList.filter {κ : id.Kernel ℝ} {L : id.Assignment → ℝ}
    {vs : List (Valuation id.toFinBayesNet)} {ss : List (Symbolic id)}
    (h : RepresentsList κ L vs ss) (p : Finset id.V → Bool) :
    RepresentsList κ L (vs.filter fun v => p v.scope) (ss.filter fun s => p s.scope) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons v s vs ss hv hs ih =>
    by_cases hp : p v.scope
    · simpa only [List.filter_cons, ← hv.1, hp, ↓reduceIte] using List.Forall₂.cons hv ih
    · simpa only [List.filter_cons, ← hv.1, hp, Bool.false_eq_true, ↓reduceIte] using ih

theorem RepresentsList.chanceStep {κ : id.Kernel ℝ} {L : id.Assignment → ℝ}
    {vs : List (Valuation id.toFinBayesNet)} {ss : List (Symbolic id)}
    (h : RepresentsList κ L vs ss) (a : id.V) :
    RepresentsList κ L (Valuation.chanceStep a vs) (Symbolic.chanceStep a ss) := by
  have hb : Represents κ L (Valuation.collect (Valuation.bucket a vs))
      (Symbolic.collect (Symbolic.bucket a ss)) := (h.filter (fun S => decide (a ∈ S))).collect
  apply List.Forall₂.cons _ (h.filter (fun S => decide (a ∉ S)))
  constructor
  · exact congrArg (Finset.erase · a) hb.1
  · intro x
    exact Finset.sum_congr rfl fun b _ => hb.2 (Function.update x a b)

theorem RepresentsList.decisionStep {κ : id.Kernel ℝ} {L : id.Assignment → ℝ}
    {vs : List (Valuation id.toFinBayesNet)} {ss : List (Symbolic id)}
    (h : RepresentsList κ L vs ss) (a : id.V) :
    RepresentsList κ L (Valuation.decisionStep a vs) (Symbolic.decisionStep a ss) := by
  have hb : Represents κ L (Valuation.collect (Valuation.bucket a vs))
      (Symbolic.collect (Symbolic.bucket a ss)) := (h.filter (fun S => decide (a ∈ S))).collect
  apply List.Forall₂.cons _ (h.filter (fun S => decide (a ∉ S)))
  constructor
  · exact congrArg (Finset.erase · a) hb.1
  · intro x
    change (Valuation.collect (Valuation.bucket a vs)).prob
      (Function.update x a (argmax fun b => (Valuation.collect (Valuation.bucket a vs)).prob
        (Function.update x a b))) = _
    simp_rw [hb.2]
    rfl

def Expr.guard (κ : id.Kernel ℝ) (L : id.Assignment → ℝ) (p : id.V × Expr id) : Prop :=
  ∀ x a, p.2.eval κ L (Function.update x p.1 a) = p.2.eval κ L x

/-- The symbolic trace records every actual bucket guard, not a guessed or assumed trace. -/
theorem represents_guards_iff {κ : id.Kernel ℝ} {L : id.Assignment → ℝ}
    {R : Finset id.V} (plan : Plan id R)
    {vs : List (Valuation id.toFinBayesNet)} {ss : List (Symbolic id)}
    (h : RepresentsList κ L vs ss) :
    AllGuards plan vs ↔ ∀ p ∈ Symbolic.trace plan ss, Expr.guard κ L p := by
  induction plan generalizing vs ss with
  | done => simp [AllGuards, Symbolic.trace]
  | chance a _ _ next ih => exact ih (h.chanceStep a)
  | decision d _ _ next ih =>
    have hb : Represents κ L (Valuation.collect (Valuation.bucket (id.action d) vs))
        (Symbolic.collect (Symbolic.bucket (id.action d) ss)) :=
      (h.filter (fun S => decide (id.action d ∈ S))).collect
    change (ExactGuard (id.action d) vs ∧ _) ↔ _
    rw [show ExactGuard (id.action d) vs ↔
      Expr.guard κ L (id.action d, (Symbolic.collect (Symbolic.bucket (id.action d) ss)).expr) by
        unfold ExactGuard Expr.guard
        simp_rw [hb.2]]
    rw [ih (h.decisionStep (id.action d))]
    simp only [Symbolic.trace, List.forall_mem_cons]

theorem initial_represents (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (L : id.Assignment → ℝ) :
    RepresentsList κ L (DVE.initial κ hloc hnonneg u hu).valuations (Symbolic.initial id) := by
  apply List.rel_append
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro v hv
    exact ⟨rfl, fun _ => rfl⟩
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro v hv
    exact ⟨rfl, fun _ => rfl⟩

theorem initialEvidence_represents (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) :
    RepresentsList κ e.likelihood (DVE.initialEvidence κ hloc hnonneg u hu e).valuations
      (Symbolic.initialEvidence id e.ancestors) :=
  List.Forall₂.cons ⟨rfl, fun _ => rfl⟩ (initial_represents κ hloc hnonneg u hu _)

theorem argmax_value_eq_sup {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) :
    f (argmax f) = Finset.univ.sup' Finset.univ_nonempty f := by
  apply le_antisymm
  · exact Finset.le_sup' f (Finset.mem_univ _)
  · exact Finset.sup'_le _ _ (fun a _ => le_argmax f a)

/-- Only maximum values, not argmax selectors, are claimed continuous. -/
theorem continuousAt_argmax_value {A : Type} [Fintype A] [Nonempty A]
    (f : ℝ → A → ℝ) {t : ℝ} (h : ∀ a, ContinuousAt (fun z => f z a) t) :
    ContinuousAt (fun z => f z (argmax (f z))) t := by
  simp_rw [argmax_value_eq_sup]
  exact ContinuousAt.finset_sup'_apply _ (fun a _ => h a)

theorem Expr.continuousAt (e : Expr id) (K : ℝ → id.Kernel ℝ)
    (L : ℝ → id.Assignment → ℝ) {t : ℝ}
    (hK : ∀ m x a, ContinuousAt (fun z => K z m x a) t)
    (hL : ∀ x, ContinuousAt (fun z => L z x) t) (x : id.Assignment) :
    ContinuousAt (fun z => e.eval (K z) (L z) x) t := by
  induction e generalizing x with
  | one => exact continuousAt_const
  | chance m => exact hK m x _
  | likelihood => exact hL x
  | mul f g ihf ihg => exact (ihf x).mul (ihg x)
  | sum v f ih => exact tendsto_finsetSum _ (fun a _ => ih (Function.update x v a))
  | max v f ih =>
    exact continuousAt_argmax_value (fun z a => f.eval (K z) (L z) (Function.update x v a))
      (fun a => ih _)

/-- Equality on all positive smoothing parameters extends to zero by continuity. -/
theorem eq_at_zero_of_positive (f g : ℝ → ℝ)
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0) (h : ∀ t, 0 < t → f t = g t) :
    f 0 = g 0 := by
  have hz : f 0 - g 0 = 0 :=
    ((hf.sub hg).continuousWithinAt (s := Set.Ioi 0)).eq_const_of_mem_closure
      (by simp [closure_Ioi]) (fun t ht => sub_eq_zero.mpr (h t ht))
  exact sub_eq_zero.mp hz

end
end InfluenceDiagramsProofs.DVE.Guard
