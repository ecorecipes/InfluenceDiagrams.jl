import InfluenceDiagramsProofs.Finite.DVE.JsonRecords

/-!
# SA-Pass shadow module: the influence-diagram ACSets JSON decoder

Claim `id.json-decoder`, from `Records.decodeDiagram_eq_ok`, `Records.decodeDiagram_encodeDiagram`
and `Records.decodeDiagramChecked_isSome_iff`:
"`decodeDiagram_eq_ok` proves that decoding a parsed `write_json_influence_diagram` document
succeeds with records `r` exactly when its twelve tables have `r`'s row counts and every column
of every row holds `r`'s value, `decodeDiagram_encodeDiagram` that decoding the encoded records
gives them back, and `decodeDiagramChecked_isSome_iff` that the checked decoder succeeds exactly
when the decoded records satisfy `FullValid`."

"Its twelve tables … every column of every row" is `DiagramBodyMatches` of the `"acset"` body of
an `"influence-diagram-acset"` envelope; "the checked decoder" is `decodeDiagramChecked`. The
shadows split "exactly when" into its directions, pin the body's twelve keys and the row count
of the `InformationInput` table, and state the round trip and the checked iff.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.JsonDecoder

open Lean (Json)
open BayesianNetworksProofs.Raw InfluenceDiagramsProofs.Records

/-- The three cited theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (j : Json) (r : Diagram),
      decodeDiagram j = .ok r ↔ ∃ body, EnvelopeMatches idFormat j body ∧ DiagramBodyMatches body r) ∧
    (∀ r : Diagram, decodeDiagram (encodeDiagram r) = .ok r) ∧
    ∀ j : Json, (decodeDiagramChecked j).isSome ↔ ∃ r, decodeDiagram j = .ok r ∧ r.FullValid

/-- "succeeds with records `r` only when … every column of every row holds `r`'s value". -/
abbrev Shadow1 : Prop :=
  ∀ (j : Json) (r : Diagram), decodeDiagram j = .ok r →
    ∃ body, EnvelopeMatches idFormat j body ∧ DiagramBodyMatches body r

/-- "exactly when": such a document decodes to `r`. -/
abbrev Shadow2 : Prop :=
  ∀ (j : Json) (r : Diagram),
    (∃ body, EnvelopeMatches idFormat j body ∧ DiagramBodyMatches body r) → decodeDiagram j = .ok r

/-- "its twelve tables have `r`'s row counts": twelve keys, and for instance the information
inputs. -/
abbrev Shadow3 : Prop :=
  ∀ (j : Json) (r : Diagram), decodeDiagram j = .ok r →
    ∃ acset : JsonObject, EnvelopeMatches idFormat j (.obj acset) ∧ acset.size = 12 ∧
      rowCount acset "InformationInput" = r.nf

/-- "decoding the encoded records gives them back". -/
abbrev Shadow4 : Prop := ∀ r : Diagram, decodeDiagram (encodeDiagram r) = .ok r

/-- "the checked decoder succeeds exactly when the decoded records satisfy `FullValid`". -/
abbrev Shadow5 : Prop :=
  ∀ j : Json, (decodeDiagramChecked j).isSome ↔ ∃ r, decodeDiagram j = .ok r ∧ r.FullValid

theorem forward1 : Candidate → Shadow1 := fun h j r => (h.1 j r).1

theorem forward2 : Candidate → Shadow2 := fun h j r => (h.1 j r).2

theorem forward3 : Candidate → Shadow3 := fun h j r hd => by
  obtain ⟨body, henv, acset, rfl, hs, -, -, -, -, -, -, -, -, hF, -, -, -⟩ := (h.1 j r).1 hd
  exact ⟨acset, henv, hs, rowCount_of_tableMatches hF⟩

theorem forward4 : Candidate → Shadow4 := fun h => h.2.1

theorem forward5 : Candidate → Shadow5 := fun h => h.2.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Shadow5 → Candidate :=
  fun s1 s2 _ s4 s5 => ⟨fun j r => ⟨s1 j r, s2 j r⟩, s4, s5⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ => decodeDiagram_eq_ok, decodeDiagram_encodeDiagram,
    fun _ => decodeDiagramChecked_isSome_iff⟩

end InfluenceDiagramsProofs.Shadows.JsonDecoder
