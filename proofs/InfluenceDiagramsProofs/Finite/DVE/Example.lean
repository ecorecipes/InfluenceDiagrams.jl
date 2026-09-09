import InfluenceDiagramsProofs.Finite.DVE.Evidence
import Mathlib.Tactic.FinCases

/-!
# Nonvacuity: a partially observed two-decision model

There are five Boolean variables: hidden state H, noisy observation O, first action T,
second observation S, and final action A. H is never observed directly. If T is true, S
reveals H; otherwise S is always false, creating unreachable information rows. The final
action earns ten for matching H; testing costs one. The first decision sees O, while the
second remembers O and T and also sees S. This is not a fully observed decision tree.

The generic driver theorem is instantiated with concrete normalized nonnegative CPTs,
local utility, a closed diagram and a complete no-forgetting schedule.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE.Example

noncomputable section

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram

@[reducible] def diagram : FinInfluenceDiagram where
  V := Fin 5
  M := Fin 3
  states _ := Bool
  target m := if m = 0 then 0 else if m = 1 then 1 else 3
  parents m := if m = 0 then ∅ else if m = 1 then {0} else {0, 2}
  D := Bool
  action d := if d then 4 else 2
  info d := if d then {1, 2, 3} else {1}
  U := Unit
  uscope _ := {0, 2, 4}

theorem closed : diagram.Closed := by
  unfold FinInfluenceDiagram.Closed Function.Bijective Function.Injective Function.Surjective
  decide

def order : diagram.IDOrder where
  order := [0, 1, 2, 3, 4]
  nodup := by decide
  complete := by decide
  parents_before := by decide
  info_before_action := by decide
  no_self := by decide
  no_self_info := by decide

def noForgetting : NoForgettingOrder diagram where
  reverseDecisions := [true, false]
  nodup := by decide
  complete := by decide
  remembers := by decide

def kernels : diagram.Kernel ℝ := fun (m : Fin 3) (x : Fin 5 → Bool) (a : Bool) =>
  if m = 0 then 1 / 2 else
  if m = 1 then (if a = x 0 then 3 / 4 else 1 / 4) else
  if x 2 then (if a = x 0 then 1 else 0) else (if a = false then 1 else 0)

theorem local_kernels : ∀ m, Local kernels m := by
  intro m
  fin_cases m
  · intro x y _
    rfl
  · intro x y h
    funext a
    have h0 := h 0 (by decide)
    simp [kernels, h0]
  · intro x y h
    funext a
    have h0 := h 0 (by decide)
    have h2 := h 2 (by decide)
    simp [kernels, h0, h2]

theorem normalised_kernels : ∀ m, Normalised kernels m := by
  intro m x
  change (∑ a : Bool, kernels m x a) = 1
  fin_cases m <;> cases hx : x 0 <;> cases ht : x 2 <;>
    norm_num [kernels, diagram, hx, ht, Fintype.sum_bool]

theorem nonnegative_kernels : ∀ m x a, 0 ≤ kernels m x a := by
  intro m x a
  unfold kernels
  split_ifs <;> norm_num

def utility : Utility diagram ℝ := fun _ x =>
  (if x 4 = x 0 then 10 else 0) - (if x 2 then 1 else 0)

theorem local_utility : ∀ j, Utility.Local utility j := by
  intro j x y h
  have h0 := h 0 (by simp [diagram])
  have h2 := h 2 (by simp [diagram])
  have h4 := h 4 (by simp [diagram])
  simp [utility, h0, h2, h4]

theorem hidden_state_never_observed : ∀ d, (0 : diagram.V) ∉ diagram.info d := by decide

/-- Skipping the test makes S=true impossible, including information rows of decision A. -/
theorem unreachable_row (x : diagram.Assignment) (h : x 2 = false) :
    kernels 2 x true = 0 := by simp [kernels, h]

/-- Concrete multi-decision, partially observed, zero-row instantiation of DVE correctness. -/
theorem checked_solution :
    let sol := solve kernels local_kernels nonnegative_kernels utility local_utility order noForgetting
    sol.strategy.Deterministic ∧ expectedUtility kernels sol.strategy utility = sol.value ∧
      sol.value = optimalValue kernels utility :=
  solve_spec kernels closed order noForgetting local_kernels normalised_kernels
    nonnegative_kernels utility local_utility

end
end InfluenceDiagramsProofs.DVE.Example
