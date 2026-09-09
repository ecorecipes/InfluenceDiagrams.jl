import InfluenceDiagramsProofs.Finite.Optimization
import BayesianNetworksProofs.Finite.NumericalContracts
import Mathlib.Tactic.Linarith

/-!
# Ordered local policies and a quantitative tie-gap contract

The local selector chooses the least maximizing state in a supplied finite linear order.
For the raw-record model, states are `Fin n` in checked state-position order. For another
state representation, the caller must supply that order, not silently use alphabetical labels.

Only local action rows are maximized. The finite information table reconstructs the same
admissible policy. A strict 2ε action gap protects the maximizing label against uniform
score errors ε; ties without a gap are intentionally not claimed stable.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet

noncomputable section

def maximizing {A : Type} [Fintype A] (f : A → ℝ) : Finset A := by
  classical
  exact Finset.univ.filter fun a => ∀ b, f b ≤ f a

theorem maximizing_nonempty {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (maximizing f).Nonempty := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun b => ha b (Finset.mem_univ _)⟩⟩

def firstArgmax {A : Type} [Fintype A] [Nonempty A] [LinearOrder A] (f : A → ℝ) : A :=
  (maximizing f).min' (maximizing_nonempty f)

theorem firstArgmax_maximizes {A : Type} [Fintype A] [Nonempty A] [LinearOrder A]
    (f : A → ℝ) (a : A) : f a ≤ f (firstArgmax f) := by
  have hm := Finset.min'_mem (maximizing f) (maximizing_nonempty f)
  exact (Finset.mem_filter.1 hm).2 a

/-- Exact first-state tie rule: no other maximizing state precedes the selected state. -/
theorem firstArgmax_first {A : Type} [Fintype A] [Nonempty A] [LinearOrder A]
    (f : A → ℝ) (a : A) (ha : ∀ b, f b ≤ f a) : firstArgmax f ≤ a :=
  Finset.min'_le _ a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩)

theorem firstArgmax_stable {A : Type} [Fintype A] [Nonempty A] [LinearOrder A]
    (f g : A → ℝ) (ε : ℝ) (winner : A)
    (herr : ∀ a, |g a - f a| ≤ ε)
    (hgap : ∀ a, a ≠ winner → f a + 2 * ε < f winner) :
    firstArgmax g = winner := by
  by_contra he
  have hg := firstArgmax_maximizes g winner
  have hhi := (abs_le.1 (herr (firstArgmax g))).2
  have hlo := (abs_le.1 (herr winner)).1
  have hstrict := hgap _ he
  linarith

namespace FinInfluenceDiagram

variable {id : FinInfluenceDiagram} {d : id.D}
variable [LinearOrder (id.states (id.action d))]

def Policy.ofOrderedScore (score : id.Assignment → id.states (id.action d) → ℝ)
    (hscore : LocalOn (id.info d) score) : Policy id ℝ d :=
  Policy.ofFun (fun x => firstArgmax (score x))
    (fun x y h => congrArg firstArgmax (hscore x y h))

/-- A finite table on precisely the information variables, not on a fully observed history. -/
def orderedTable (score : id.Assignment → id.states (id.action d) → ℝ) :
    InfoAssignment id d → id.states (id.action d) :=
  fun i => firstArgmax (score (extendInfo d i))

theorem orderedTable_reconstruct (score : id.Assignment → id.states (id.action d) → ℝ)
    (hscore : LocalOn (id.info d) score) (x : id.Assignment) :
    orderedTable score (infoAssignment d x) = firstArgmax (score x) := by
  apply congrArg firstArgmax
  apply hscore
  intro v hv
  simp [extendInfo, infoAssignment, hv]

theorem orderedPolicy_table (score : id.Assignment → id.states (id.action d) → ℝ)
    (hscore : LocalOn (id.info d) score) (x : id.Assignment) (a : id.states (id.action d)) :
    (Policy.ofOrderedScore score hscore).kernel x a =
      if a = orderedTable score (infoAssignment d x) then 1 else 0 := by
  rw [orderedTable_reconstruct score hscore]
  rfl

theorem orderedPolicy_is_local (score : id.Assignment → id.states (id.action d) → ℝ)
    (hscore : LocalOn (id.info d) score) :
    LocalOn (id.info d) (Policy.ofOrderedScore score hscore).kernel :=
  (Policy.ofOrderedScore score hscore).localOn

theorem orderedPolicy_maximizes (score : id.Assignment → id.states (id.action d) → ℝ)
    (hscore : LocalOn (id.info d) score) (x : id.Assignment) (a : id.states (id.action d)) :
    score x a ≤ score x (orderedTable score (infoAssignment d x)) := by
  rw [orderedTable_reconstruct score hscore]
  exact firstArgmax_maximizes _ _

end FinInfluenceDiagram
end
end InfluenceDiagramsProofs
