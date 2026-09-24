import InfluenceDiagramsProofs.Finite.ExpectedUtility

/-!
# SA-Pass shadow module: fixing a decision is a hard intervention

Claim `id.fix-decision`, from `strategyKernel_fix_eq_intervene`.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.FixDecision

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram

/-- `strategyKernel_fix_eq_intervene`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) (R : Type) [CommSemiring R] (κ : id.Kernel R)
      (σ : Strategy id R) (d : id.D) (a : id.states (id.action d)),
    strategyKernel κ (σ.fix d a) = intervene (strategyKernel κ σ) (Sum.inr d) a

/-- "hard intervention on the corresponding mechanism": the decision's mechanism becomes the
point mass at the fixed action, ignoring its information set. -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) (R : Type) [CommSemiring R] (κ : id.Kernel R)
      (σ : Strategy id R) (d : id.D) (a : id.states (id.action d))
      (x : id.Assignment) (y : id.states (id.action d)),
    strategyKernel κ (σ.fix d a) (Sum.inr d) x y = if y = a then 1 else 0

/-- and nothing else changes: every other mechanism of the instantiated network keeps its
kernel, which is what makes this *surgery* rather than a new model. -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) (R : Type) [CommSemiring R] (κ : id.Kernel R)
      (σ : Strategy id R) (d : id.D) (a : id.states (id.action d))
      (m : id.instantiate.M), m ≠ Sum.inr d →
    strategyKernel κ (σ.fix d a) m = strategyKernel κ σ m

theorem forward1 : Candidate → Shadow1 := by
  intro h id R _ κ σ d a x y
  rw [h id R κ σ d a, intervene_self]
  rfl

theorem forward2 : Candidate → Shadow2 := by
  intro h id R _ κ σ d a m hm
  rw [h id R κ σ d a, intervene_of_ne _ hm]

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 id R _ κ σ d a
  funext m
  by_cases hm : m = Sum.inr d
  · subst hm
    funext x y
    rw [h1 id R κ σ d a x y, intervene_self]
    rfl
  · rw [h2 id R κ σ d a m hm, intervene_of_ne _ hm]

end InfluenceDiagramsProofs.Shadows.FixDecision
