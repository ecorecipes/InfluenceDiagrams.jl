import InfluenceDiagramsProofs.Finite.DVE.RecordsValid

/-!
# SA-Pass shadow module: decision precedence in `FullValid`

Claim `id.decision-precedence`, from `Records.Diagram.FullValid.precedence_acyclic`,
`Records.Diagram.informationTables_acyclic_iff` and `Records.Diagram.FullValid.precedence_rank`:
"`FullValid` also checks the `DecisionPrecedence` rows as Julia's `validate` does:
`FullValid.precedence_acyclic` requires Julia's `information_graph` to be acyclic, which by
`informationTables_acyclic_iff` means that one injective rank orders every mechanism input before
its target, every information variable before its action and every precedence row's earlier
action before its later action, and `FullValid.precedence_rank` proves that the precedence rows
alone are then acyclic (a self-loop is rejected); `NamesUnique` is the separate check of
`unique_names = true`."

"Julia's `information_graph` acyclic" is `informationTables.Acyclic`. The shadows pin that a fully
valid diagram has it, the two directions of its unpacking, the decision-only rank, and the
rejection of self-loops. The last clause names a separate predicate and promises no theorem.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.DecisionPrecedence

open InfluenceDiagramsProofs.Records

/-- The unpacked acyclicity: one injective rank with every arc forward. -/
abbrev Ranked (r : Diagram) : Prop :=
  ∃ rank : Fin r.nv → Fin r.nv, Function.Injective rank ∧
    (∀ i, rank (r.inputs i).var < rank (r.mechanisms (r.inputs i).mechanism).target) ∧
    (∀ f, rank (r.information f).var < rank (r.decisions (r.information f).decision).action) ∧
    ∀ p, rank (r.decisions (r.precedence p).earlier).action <
      rank (r.decisions (r.precedence p).later).action

/-- The decision-only rank. -/
abbrev DecisionRanked (r : Diagram) : Prop :=
  ∃ rank : Fin r.nd → ℕ, Function.Injective rank ∧
    ∀ p, rank (r.precedence p).earlier < rank (r.precedence p).later

/-- The three cited results, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ r : Diagram, r.FullValid → r.informationTables.Acyclic) ∧
    (∀ r : Diagram, r.informationTables.Acyclic ↔ Ranked r) ∧
    ∀ r : Diagram, r.FullValid → DecisionRanked r

/-- "`FullValid.precedence_acyclic` requires Julia's `information_graph` to be acyclic". -/
abbrev Shadow1 : Prop := ∀ r : Diagram, r.FullValid → r.informationTables.Acyclic

/-- "which … means that one injective rank orders …": acyclic gives the rank. -/
abbrev Shadow2 : Prop := ∀ r : Diagram, r.informationTables.Acyclic → Ranked r

/-- … and such a rank gives acyclicity. -/
abbrev Shadow3 : Prop := ∀ r : Diagram, Ranked r → r.informationTables.Acyclic

/-- "`FullValid.precedence_rank` proves that the precedence rows alone are then acyclic". -/
abbrev Shadow4 : Prop := ∀ r : Diagram, r.FullValid → DecisionRanked r

/-- "(a self-loop is rejected)". -/
abbrev Shadow5 : Prop :=
  ∀ r : Diagram, r.FullValid → ∀ p, (r.precedence p).earlier ≠ (r.precedence p).later

theorem forward1 : Candidate → Shadow1 := fun h => h.1

theorem forward2 : Candidate → Shadow2 := fun h r => (h.2.1 r).1

theorem forward3 : Candidate → Shadow3 := fun h r => (h.2.1 r).2

theorem forward4 : Candidate → Shadow4 := fun h => h.2.2

theorem forward5 : Candidate → Shadow5 := fun h r hv p he => by
  obtain ⟨rank, -, hp⟩ := h.2.2 r hv
  have := hp p
  rw [he] at this
  exact lt_irrefl _ this

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Shadow5 → Candidate :=
  fun s1 s2 s3 s4 _ => ⟨s1, fun r => ⟨s2 r, s3 r⟩, s4⟩

/-- SA-Pass anchor: the cited results prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ h => h.precedence_acyclic, fun r => r.informationTables_acyclic_iff,
    fun _ h => h.precedence_rank⟩

end InfluenceDiagramsProofs.Shadows.DecisionPrecedence
