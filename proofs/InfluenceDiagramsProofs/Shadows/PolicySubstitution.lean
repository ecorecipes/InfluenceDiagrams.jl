import InfluenceDiagramsProofs.Finite.Instantiate

/-!
# SA-Pass shadow module: policy substitution yields a valid Bayesian network

Claim `id.policy-substitution`, from `closed_instantiate` together with `IDOrder.toTopoOrder`.
"Valid" is more than "closed": the SPEC's validity for a Bayesian network includes acyclicity,
so a second shadow is needed and `closed_instantiate` alone does not bracket the sentence.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.PolicySubstitution

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram

/-- `closed_instantiate` and `IDOrder.toTopoOrder`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram), id.Closed →
    id.instantiate.Closed ∧ ∀ _ : id.IDOrder, Nonempty id.instantiate.TopoOrder

/-- "yields valid BN": every variable of the substituted network has exactly one mechanism. -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram), id.Closed → id.instantiate.Closed

/-- and the substituted network is acyclic, which is the other half of BN validity. -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram), id.Closed →
    ∀ _ : id.IDOrder, Nonempty id.instantiate.TopoOrder

theorem forward1 : Candidate → Shadow1 := fun h id hc => (h id hc).1

theorem forward2 : Candidate → Shadow2 := fun h id hc => (h id hc).2

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 id hc => ⟨h1 id hc, h2 id hc⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated, so a restatement that
drifts from the proved theorem stops compiling. -/
theorem anchor : Candidate := fun _ h =>
  ⟨InfluenceDiagramsProofs.FinInfluenceDiagram.closed_instantiate h, fun ord => ⟨ord.toTopoOrder⟩⟩

end InfluenceDiagramsProofs.Shadows.PolicySubstitution
