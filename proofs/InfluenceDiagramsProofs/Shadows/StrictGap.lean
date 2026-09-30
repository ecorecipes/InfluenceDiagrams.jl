import InfluenceDiagramsProofs.Finite.OrderedPolicies

/-!
# SA-Pass shadow module: label stability under a strict action gap

Claim `id.strict-gap`, from `firstArgmax_stable`: "label stability under a strict `2*epsilon`
action gap when every row score has error at most `epsilon`".
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.StrictGap

open InfluenceDiagramsProofs

/-- `firstArgmax_stable`, restated abstractly: if every perturbed score `g` is within `ε` of the
exact score `f`, and the state `winner` beats every other state of `f` by more than `2ε`, then
the first-maximizing selector applied to `g` chooses `winner`. -/
abbrev Candidate : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] [LinearOrder A] (f g : A → ℝ) (ε : ℝ) (winner : A),
    (∀ a, |g a - f a| ≤ ε) → (∀ a, a ≠ winner → f a + 2 * ε < f winner) →
    firstArgmax g = winner

/-- "label stability": under the error and gap hypotheses, the label selected from the perturbed
scores is the label selected from the exact scores. -/
abbrev Shadow1 : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] [LinearOrder A] (f g : A → ℝ) (ε : ℝ) (winner : A),
    (∀ a, |g a - f a| ≤ ε) → (∀ a, a ≠ winner → f a + 2 * ε < f winner) →
    firstArgmax g = firstArgmax f

-- The error bound forces `ε ≥ 0`, since `A` is nonempty.
theorem eps_nonneg {A : Type} [Nonempty A] (f g : A → ℝ) (ε : ℝ)
    (herr : ∀ a, |g a - f a| ≤ ε) : 0 ≤ ε :=
  (abs_nonneg _).trans (herr (Classical.arbitrary A))

-- With a nonnegative gap, the exact scores select the winner. This holds without the
-- candidate (it is not a shadow: a shadow provable on its own would not discriminate), so
-- the backward checker uses it to recover the winner from the stability shadow.
theorem exact_winner {A : Type} [Fintype A] [Nonempty A] [LinearOrder A] (f : A → ℝ) (ε : ℝ)
    (winner : A) (hε : 0 ≤ ε) (hgap : ∀ a, a ≠ winner → f a + 2 * ε < f winner) :
    firstArgmax f = winner := by
  by_contra hne
  have h := hgap _ hne
  have := firstArgmax_maximizes f winner
  linarith

theorem forward1 : Candidate → Shadow1 := by
  intro h A _ _ _ f g ε winner herr hgap
  -- The exact scores are a perturbation of themselves with error `0 ≤ ε`.
  have hself : ∀ a, |f a - f a| ≤ ε := fun a => by
    simpa using eps_nonneg f g ε herr
  rw [h A f g ε winner herr hgap, h A f f ε winner hself hgap]

theorem backward : Shadow1 → Candidate := by
  intro h1 A _ _ _ f g ε winner herr hgap
  rw [h1 A f g ε winner herr hgap, exact_winner f ε winner (eps_nonneg f g ε herr) hgap]

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated, so a restatement that
drifts from the proved theorem stops compiling. -/
theorem anchor : Candidate := fun _ _ _ _ f g ε winner herr hgap =>
  InfluenceDiagramsProofs.firstArgmax_stable f g ε winner herr hgap

end InfluenceDiagramsProofs.Shadows.StrictGap
