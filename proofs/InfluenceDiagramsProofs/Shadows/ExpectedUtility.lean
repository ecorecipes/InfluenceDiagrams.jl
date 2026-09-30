import InfluenceDiagramsProofs.Finite.ExpectedUtility

/-!
# SA-Pass shadow module: expected utility is an expectation

Claim `id.expected-utility`, from `expectedUtility_eq`. `Shadow1` is the sentence
`EU(σ) = ∑_x P_σ(x) U(x)` read literally; in the Lean development that is the *definition* of
`expectedUtility`, so it holds by `rfl` and is declared `independently_provable`.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.ExpectedUtility

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram

/-- `expectedUtility_eq`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) (R : Type) [CommSemiring R] (κ : id.Kernel R)
      (σ : Strategy id R) (u : Utility id R),
    expectedUtility κ σ u =
      ∑ x, ((∏ m, κ m x (x (id.target m))) * ∏ d, (σ d).kernel x (x (id.action d))) *
        ∑ j, u j x

/-- "EU(σ) = ∑_x P_σ(x) U(x)": the expectation of the total utility under the joint of the
instantiated network. -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) (R : Type) [CommSemiring R] (κ : id.Kernel R)
      (σ : Strategy id R) (u : Utility id R),
    expectedUtility κ σ u = ∑ x, joint (strategyKernel κ σ) x * totalUtility u x

/-- and `P_σ` really is the chance kernels times the policy kernels, with `U` the sum of the
utility nodes: the expectation is over the *instantiated* law, not an unspecified one. -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) (R : Type) [CommSemiring R] (κ : id.Kernel R)
      (σ : Strategy id R) (u : Utility id R),
    expectedUtility κ σ u =
      ∑ x, ((∏ m, κ m x (x (id.target m))) * ∏ d, (σ d).kernel x (x (id.action d))) *
        ∑ j, u j x

theorem forward1 : Candidate → Shadow1 := fun _ _ _ _ _ _ _ => rfl

theorem forward2 : Candidate → Shadow2 := id

theorem backward : Shadow1 → Shadow2 → Candidate := fun _ h2 => h2

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated, so a restatement that
drifts from the proved theorem stops compiling. -/
theorem anchor : Candidate := fun _ _ _ κ σ u =>
  InfluenceDiagramsProofs.FinInfluenceDiagram.expectedUtility_eq κ σ u

end InfluenceDiagramsProofs.Shadows.ExpectedUtility
