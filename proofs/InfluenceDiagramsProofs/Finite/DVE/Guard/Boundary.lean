import InfluenceDiagramsProofs.Finite.DVE.Guard.Complete
import InfluenceDiagramsProofs.Finite.DVE.Example

/-!
# Exact-guard boundary checks

The no-evidence fixture has a deterministic observed root Z, an action A that observes Z,
and a deterministic child Y of A. Summing Y retains an A-indexed probability factor.
The root factor is outside A's bucket and is zero at Z=true. The complete diagram nevertheless
has mass one and satisfies the exact guard on that unreachable row.

The previous hidden-state two-decision fixture is also checked with an identically zero
supported likelihood. The probability guard still succeeds; only the later evidence-mass
check rejects. These are nonvacuity checks, not substitutes for the general completeness proof.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE.GuardBoundary

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

@[reducible] def diagram : FinInfluenceDiagram where
  V := Fin 3
  M := Bool
  states _ := Bool
  target m := if m then 2 else 0
  parents m := if m then {1} else ∅
  D := Unit
  action _ := 1
  info _ := {0}
  U := Unit
  uscope _ := {1}

theorem closed : diagram.Closed := by
  unfold FinInfluenceDiagram.Closed Function.Bijective Function.Injective Function.Surjective
  decide

def order : diagram.IDOrder where
  order := [0, 1, 2]
  nodup := by decide
  complete := by decide
  parents_before := by decide
  info_before_action := by decide
  no_self := by decide
  no_self_info := by decide

def nf : NoForgettingOrder diagram where
  reverseDecisions := [()]
  nodup := by decide
  complete := by decide
  remembers := by decide

def κ : diagram.Kernel ℝ := fun (m : Bool) (x : Fin 3 → Bool) (a : Bool) =>
  if m then (if a = x 1 then 1 else 0) else (if a = false then 1 else 0)

theorem κ_local : ∀ m, Local κ m := by
  intro m
  cases m with
  | false => intro x y _; rfl
  | true =>
    intro x y h
    funext a
    have he := h 1 (by decide)
    simp [κ, he]

theorem κ_normalised : ∀ m, Normalised κ m := by
  intro m x
  change (∑ a : Bool, κ m x a) = 1
  cases m <;> simp [κ]

theorem κ_nonnegative : ∀ m x a, 0 ≤ κ m x a := by
  intro m x a
  unfold κ
  split_ifs <;> norm_num

def u : Utility diagram ℝ := fun _ x => if x 1 then 1 else 0

theorem u_local : ∀ j, Utility.Local u j := by
  intro j x y h
  have he := h 1 (by simp [diagram])
  simp [u, he]

theorem collect_zero_of_member {vs : List (Valuation diagram.toFinBayesNet)}
    {v : Valuation diagram.toFinBayesNet} (hv : v ∈ vs) (x : diagram.Assignment)
    (hz : v.prob x = 0) : (collect vs).prob x = 0 := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
    change w.prob x * (collect vs).prob x = 0
    rcases List.mem_cons.1 hv with rfl | hv
    · rw [hz, zero_mul]
    · rw [ih hv, mul_zero]

/-- A genuinely zero OUTSIDE probability, without evidence and with a normalized closed model. -/
theorem zero_outside_context :
    (collect (outside (1 : diagram.V)
      (chanceStep (2 : diagram.V) (initial κ κ_local κ_nonnegative u u_local).valuations))).prob
      (fun _ => true) = 0 := by
  let r := chanceValuation κ κ_local κ_nonnegative false
  have hi : r ∈ (initial κ κ_local κ_nonnegative u u_local).valuations := by
    apply List.mem_append_left
    exact List.mem_map.2 ⟨false, Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩
  have hc : r ∈ outside (2 : diagram.V) (initial κ κ_local κ_nonnegative u u_local).valuations :=
    List.mem_filter.2 ⟨hi, by simp [r, chanceValuation, diagram]⟩
  have hd : r ∈ outside (1 : diagram.V)
      (chanceStep (2 : diagram.V) (initial κ κ_local κ_nonnegative u u_local).valuations) :=
    List.mem_filter.2 ⟨List.mem_cons_of_mem _ hc, by simp [r, chanceValuation, diagram]⟩
  apply collect_zero_of_member hd
  simp [r, chanceValuation, κ]

theorem summed_child_retains_action_axis :
    (1 : diagram.V) ∈ (sumOut (2 : diagram.V) (chanceValuation κ κ_local κ_nonnegative true)).scope := by
  decide

theorem checked_zero_outside_model :
    solveGuarded κ κ_local κ_nonnegative u u_local order nf =
      some (solve κ κ_local κ_nonnegative u u_local order nf) :=
  solveGuarded_eq κ closed order nf κ_local κ_normalised κ_nonnegative u u_local

def zeroEvidence : Evidence Example.diagram where
  ancestors := ∅
  closed := fun _ h => False.elim (Finset.notMem_empty _ h)
  no_action := fun _ => Finset.notMem_empty _
  likelihood _ := 0
  localOn := fun _ _ _ => rfl
  nonneg := fun _ => le_refl 0

theorem guard_accepts_zero_evidence :
    checkedRun (Example.noForgetting.plan Example.order.no_self_info)
      (initialEvidence Example.kernels Example.local_kernels Example.nonnegative_kernels
        Example.utility Example.local_utility zeroEvidence) defaultStrategy =
      some (run (Example.noForgetting.plan Example.order.no_self_info)
        (initialEvidence Example.kernels Example.local_kernels Example.nonnegative_kernels
          Example.utility Example.local_utility zeroEvidence) defaultStrategy) :=
  checkedRun_generated_evidence_eq Example.kernels Example.closed Example.order Example.noForgetting
    Example.local_kernels Example.normalised_kernels Example.nonnegative_kernels
    Example.utility Example.local_utility zeroEvidence

theorem mass_check_rejects_zero_evidence :
    solveEvidenceGuarded Example.kernels Example.local_kernels Example.nonnegative_kernels
      Example.utility Example.local_utility Example.order Example.noForgetting zeroEvidence = none := by
  rw [solveEvidenceGuarded_none_iff Example.kernels Example.closed Example.order Example.noForgetting
    Example.local_kernels Example.normalised_kernels Example.nonnegative_kernels
    Example.utility Example.local_utility zeroEvidence]
  simp [evidenceMass, zeroEvidence]

end
end InfluenceDiagramsProofs.DVE.GuardBoundary
