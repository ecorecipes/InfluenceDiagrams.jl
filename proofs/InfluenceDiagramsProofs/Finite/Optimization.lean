import InfluenceDiagramsProofs.Finite.ExpectedUtility
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum

/-!
# InfluenceDiagramsProofs.Finite.Optimization

**Deterministic global optimality for any finite number of decisions** (SPEC §26–§27,
§32, and the deterministic-search prerequisite of §61 Proposition 7).

A nonnegative strategy is a convex mixture of deterministic policy tables: independently
draw an action for every information configuration of every decision. Finite distributivity
shows that mixing the induced joints recovers exactly the original joint. Expected utility
is therefore a convex combination of the deterministic expected utilities and cannot exceed
their finite maximum.

Perfect recall is not needed for this global existence theorem. The former Roadmap prose
conflated deterministic sufficiency with the correctness of greedy/strong-order decision
elimination. The latter is **not** proved here. This result gives no efficient search
algorithm: the table space can be exponentially large.

All action spaces are nonempty because `FinBayesNet.nonemptyS` is part of the inherited
model. Nonnegativity of the *strategy* is essential for the convex bound; normalisation is
a `Policy` field. Chance kernels need no positivity, locality or normalisation for the
algebraic identity and the optimisation bound. To interpret the joint as a probability law,
the validity, locality, normalisation and positivity hypotheses must be supplied separately.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet

namespace FinInfluenceDiagram

variable {id : FinInfluenceDiagram}

/-- Every policy in the strategy is a deterministic local function. -/
def Strategy.Deterministic (σ : Strategy id ℝ) : Prop :=
  ∀ d, ∃ f hf, σ d = Policy.ofFun f hf

/-- Policy normalisation alone does not prohibit signed entries; this condition does. -/
def Strategy.Nonneg (σ : Strategy id ℝ) : Prop :=
  ∀ d x a, 0 ≤ (σ d).kernel x a

/-- Values of precisely the variables visible to a decision. -/
abbrev InfoAssignment (id : FinInfluenceDiagram) (d : id.D) :=
  (v : {v : id.V // v ∈ id.info d}) → id.states v.val

/-- Restrict a complete assignment to the decision's information variables. -/
def infoAssignment (d : id.D) (x : id.Assignment) : InfoAssignment id d :=
  fun v => x v.val

/-- Complete an information assignment with arbitrary states off the information set.
These states exist by the explicit `nonemptyS` fields of the finite model. -/
noncomputable def extendInfo (d : id.D) (t : InfoAssignment id d) : id.Assignment :=
  fun v => if hv : v ∈ id.info d then t ⟨v, hv⟩ else Classical.choice (id.nonemptyS v)

theorem policy_extendInfo (d : id.D) (p : Policy id ℝ d) (x : id.Assignment) :
    p.kernel (extendInfo d (infoAssignment d x)) = p.kernel x := by
  apply p.localOn
  intro v hv
  simp [extendInfo, infoAssignment, hv]

/-- One action per information row, for every decision. This is a finite, nonempty type. -/
abbrev PolicyTable (id : FinInfluenceDiagram) :=
  (d : id.D) → InfoAssignment id d → id.states (id.action d)

/-- Interpret a complete policy table as a local deterministic strategy. -/
def tableStrategy (t : PolicyTable id) : Strategy id ℝ :=
  fun d => Policy.ofFun (fun x => t d (infoAssignment d x)) (by
    intro x y h
    apply congrArg (t d)
    funext v
    exact h v.val v.property)

theorem tableStrategy_deterministic (t : PolicyTable id) :
    (tableStrategy t).Deterministic := by
  intro d
  exact ⟨_, _, rfl⟩

theorem tableStrategy_nonneg (t : PolicyTable id) : (tableStrategy t).Nonneg := by
  intro d x a
  change 0 ≤ if a = t d (infoAssignment d x) then (1 : ℝ) else 0
  split_ifs
  · exact zero_le_one
  · exact le_refl 0

section FiniteMixture

variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- A product distribution over tables recovers any one of its rows. -/
theorem sum_table_indicator (q : I → A → ℝ) (hq : ∀ i, ∑ a, q i a = 1)
    (i : I) (a : A) :
    (∑ f : I → A, (∏ j, q j (f j)) * (if a = f i then 1 else 0)) = q i a := by
  calc
    _ = ∑ f : I → A, ∏ j, q j (f j) *
        (if j = i then (if a = f j then 1 else 0) else 1) := by
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ j, ∑ b, q j b * (if j = i then (if a = b then 1 else 0) else 1) :=
      (Fintype.prod_sum (fun (j : I) (b : A) =>
        q j b * (if j = i then (if a = b then 1 else 0) else 1))).symm
    _ = q i a := by
      have hs : ∀ j, (∑ b, q j b * (if j = i then (if a = b then 1 else 0) else 1)) =
          if j = i then q j a else 1 := by
        intro j
        by_cases h : j = i
        · simp [h, mul_ite]
        · simp [h, hq]
      simp_rw [hs]
      simp

end FiniteMixture

/-- Probability of drawing one local deterministic policy table from a policy. -/
noncomputable def policyWeight (d : id.D) (p : Policy id ℝ d)
    (t : InfoAssignment id d → id.states (id.action d)) : ℝ :=
  ∏ i, p.kernel (extendInfo d i) (t i)

theorem sum_policyWeight (d : id.D) (p : Policy id ℝ d) :
    ∑ t, policyWeight d p t = 1 := by
  classical
  unfold policyWeight
  rw [← Fintype.prod_sum]
  simp [p.normalised]

theorem policyWeight_indicator (d : id.D) (p : Policy id ℝ d)
    (x : id.Assignment) (a : id.states (id.action d)) :
    (∑ t, policyWeight d p t * (if a = t (infoAssignment d x) then 1 else 0)) =
      p.kernel x a := by
  classical
  unfold policyWeight
  rw [sum_table_indicator _ (fun i => p.normalised (extendInfo d i)),
    policy_extendInfo]

/-- Independent table draws for all decisions. -/
noncomputable def tableWeight (σ : Strategy id ℝ) (t : PolicyTable id) : ℝ :=
  ∏ d, policyWeight d (σ d) (t d)

theorem sum_tableWeight (σ : Strategy id ℝ) : ∑ t, tableWeight σ t = 1 := by
  classical
  unfold tableWeight
  rw [← Fintype.prod_sum]
  simp [sum_policyWeight]

theorem tableWeight_nonneg (σ : Strategy id ℝ) (hσ : σ.Nonneg) (t : PolicyTable id) :
    0 ≤ tableWeight σ t := by
  unfold tableWeight policyWeight
  exact Finset.prod_nonneg fun d _ => Finset.prod_nonneg fun i _ => hσ d _ _

/-- Mixing deterministic-table joints recovers the original joint exactly. -/
theorem joint_table_mixture (κ : id.Kernel ℝ) (σ : Strategy id ℝ) (x : id.Assignment) :
    joint (strategyKernel κ σ) x =
      ∑ t : PolicyTable id, tableWeight σ t * joint (strategyKernel κ (tableStrategy t)) x := by
  classical
  simp_rw [joint_instantiate]
  simp only [tableWeight, tableStrategy, Policy.ofFun_kernel]
  simp_rw [mul_left_comm (∏ d, policyWeight d (σ d) _) (∏ m, κ m x (x (id.target m)))]
  rw [← Finset.mul_sum]
  congr 1
  simp only [← Finset.prod_mul_distrib]
  calc
    _ = ∏ d, ∑ t : InfoAssignment id d → id.states (id.action d),
        policyWeight d (σ d) t *
          (if x (id.action d) = t (infoAssignment d x) then 1 else 0) :=
      Finset.prod_congr rfl fun d _ => (policyWeight_indicator d (σ d) x _).symm
    _ = _ := Fintype.prod_sum (fun d (t : InfoAssignment id d → id.states (id.action d)) =>
      policyWeight d (σ d) t * (if x (id.action d) = t (infoAssignment d x) then 1 else 0))

/-- Expected utility is a convex combination of deterministic-table expected utilities when
the strategy is nonnegative. The identity itself does not need nonnegativity. -/
theorem expectedUtility_table_mixture (κ : id.Kernel ℝ) (σ : Strategy id ℝ)
    (u : Utility id ℝ) :
    expectedUtility κ σ u =
      ∑ t : PolicyTable id, tableWeight σ t * expectedUtility κ (tableStrategy t) u := by
  classical
  unfold expectedUtility
  simp_rw [joint_table_mixture κ σ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => mul_assoc _ _ _

/-- **Global deterministic sufficiency for all finite diagrams, including limited memory.**
This is exhaustive-table optimality, not correctness of decision variable elimination. -/
theorem exists_deterministic_optimal_all (κ : id.Kernel ℝ) (u : Utility id ℝ) :
    ∃ σ' : Strategy id ℝ, σ'.Deterministic ∧ σ'.Nonneg ∧
      ∀ σ : Strategy id ℝ, σ.Nonneg → expectedUtility κ σ u ≤ expectedUtility κ σ' u := by
  classical
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image (Finset.univ : Finset (PolicyTable id))
    (fun t => expectedUtility κ (tableStrategy t) u) Finset.univ_nonempty
  refine ⟨tableStrategy t, tableStrategy_deterministic t, tableStrategy_nonneg t, ?_⟩
  intro σ hσ
  rw [expectedUtility_table_mixture]
  calc
    _ ≤ ∑ s : PolicyTable id, tableWeight σ s * expectedUtility κ (tableStrategy t) u :=
      Finset.sum_le_sum fun s hs =>
        mul_le_mul_of_nonneg_left (ht s hs) (tableWeight_nonneg σ hσ s)
    _ = _ := by rw [← Finset.sum_mul, sum_tableWeight, one_mul]

/-- The original single-decision Roadmap claim, unchanged in semantic strength. Its `Unique`
and nonnegative-chance-kernel premises are sufficient but unnecessary. -/
theorem exists_deterministic_optimal [Unique id.D] (κ : id.Kernel ℝ)
    (_hκ : ∀ m x y, 0 ≤ κ m x y) (u : Utility id ℝ) :
    ∃ σ' : Strategy id ℝ, σ'.Deterministic ∧
      ∀ σ : Strategy id ℝ, σ.Nonneg → expectedUtility κ σ u ≤ expectedUtility κ σ' u := by
  obtain ⟨σ', hd, _, hopt⟩ := exists_deterministic_optimal_all κ u
  exact ⟨σ', hd, hopt⟩

/-- Normalisation without nonnegativity does not give a convex bound: signed weights
`(-1, 2)` sum to one but turn utilities `(0, 1)` into value two. -/
theorem signed_weights_exceed_every_action :
    ∃ (p u : Bool → ℝ), (∑ a, p a = 1) ∧ (∀ a, u a ≤ 1) ∧
      1 < ∑ a, p a * u a := by
  refine ⟨(fun a => if a then 2 else -1), (fun a => if a then 1 else 0), ?_, ?_, ?_⟩
  · norm_num [Fintype.sum_bool]
  · intro a
    cases a <;> norm_num
  · norm_num [Fintype.sum_bool]

end FinInfluenceDiagram

end InfluenceDiagramsProofs
