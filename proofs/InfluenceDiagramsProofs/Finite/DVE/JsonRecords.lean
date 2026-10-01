import InfluenceDiagramsProofs.Finite.DVE.RecordsValid

/-!
# Decoding the ACSets JSON of a `SchInfluenceDiagram` diagram into checked records

`write_json_influence_diagram` (InfluenceDiagrams.jl, `src/serialization.jl`) writes the envelope
`{"format": "influence-diagram-acset", "schema_version": "0.1", "acset": body}` with ACSets'
`generate_json_acset` of the diagram as the body: the four `SchBayesNet` tables (decoded by the
row decoders of BayesianNetworks' `Finite/JsonRecords.lean`), five more object tables and the
three empty attribute-variable tables, twelve keys in all:

* `"Decision"`: `_id`, `decision_variable` (hom to `Variable`), `decision_name` (label);
* `"InformationInput"`: `_id`, `information_decision` (hom to `Decision`), `information_variable`
  (hom to `Variable`), `information_position` (one-based position);
* `"Utility"`: `_id`, `utility_name` (label), `utility_ref` (`KernelRef` object);
* `"UtilityInput"`: `_id`, `utility_node` (hom to `Utility`), `utility_variable` (hom to
  `Variable`), `utility_position` (one-based position);
* `"DecisionPrecedence"`: `_id`, `earlier`, `later` (homs to `Decision`);
* `"Label"`, `"Position"`, `"Ref"`: empty.

The conventions and the strictness are those of the BN decoder: one-based IDs through
`decodeId`, one-based positions stored zero-based, exact key sets, errors naming the table, row
and column.

Results: `decodeDiagram_eq_ok` (decoding succeeds with `r` exactly when the document has `r`'s
rows, `DiagramBodyMatches`), the round trip `decodeDiagram_encodeDiagram`, the shape theorem
`decodeDiagramBody_shape` with its failure corollaries (a missing table or column, a hom out of
range, a non-integer or non-string value), and the checked decoder
`decodeDiagramChecked : Json → Option (Σ' r : Diagram, r.FullValid)` with
`decodeDiagramChecked_isSome_iff` and `decodeDiagramChecked_encode` (`FullValid` includes the
decision-precedence checks of Julia's `validate`), and its variant for `unique_names = true`,
`decodeDiagramCheckedNames` with `decodeDiagramCheckedNames_isSome_iff` (`FullValid` and
`NamesUnique`). `decodeDiagramChecked_policyAxes`
states what a successful decode guarantees for the policy tables of the DVE label-order
theorems: the information inputs of each decision in `information_position` order, and each
action's labels in `state_position` order, read off the document.

Trusted, not proved: `Lean.Json.parse`, Julia's JSON3 writer and ACSets' `generate_json_acset`.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Records

open Lean (Json)
open BayesianNetworksProofs.Raw

/-! ## Rows of the influence-diagram tables -/

def decodeDecisionRow (nv : Nat) (k : Nat) (j : Json) : Except String (DecisionRow nv) := do
  let o ← object (rowLabel "Decision" k) 3 j
  checkId (rowLabel "Decision" k) o k
  let v ← homField (rowLabel "Decision" k) o "decision_variable" nv
  let name ← strField (rowLabel "Decision" k) o "decision_name"
  pure ⟨v, name⟩

def decodeInformationRow (nv nd : Nat) (k : Nat) (j : Json) :
    Except String (InformationRow nv nd) := do
  let o ← object (rowLabel "InformationInput" k) 4 j
  checkId (rowLabel "InformationInput" k) o k
  let d ← homField (rowLabel "InformationInput" k) o "information_decision" nd
  let v ← homField (rowLabel "InformationInput" k) o "information_variable" nv
  let p ← posField (rowLabel "InformationInput" k) o "information_position"
  pure ⟨d, v, p⟩

def decodeUtilityRow (k : Nat) (j : Json) : Except String UtilityRow := do
  let o ← object (rowLabel "Utility" k) 3 j
  checkId (rowLabel "Utility" k) o k
  let name ← strField (rowLabel "Utility" k) o "utility_name"
  let rj ← field (rowLabel "Utility" k) o "utility_ref"
  let ref ← decodeRef (rowLabel "Utility" k) rj
  pure ⟨name, ref⟩

def decodeUtilityInputRow (nv nu : Nat) (k : Nat) (j : Json) :
    Except String (UtilityInputRow nv nu) := do
  let o ← object (rowLabel "UtilityInput" k) 4 j
  checkId (rowLabel "UtilityInput" k) o k
  let q ← homField (rowLabel "UtilityInput" k) o "utility_node" nu
  let v ← homField (rowLabel "UtilityInput" k) o "utility_variable" nv
  let p ← posField (rowLabel "UtilityInput" k) o "utility_position"
  pure ⟨q, v, p⟩

def decodePrecedenceRow (nd : Nat) (k : Nat) (j : Json) : Except String (PrecedenceRow nd) := do
  let o ← object (rowLabel "DecisionPrecedence" k) 3 j
  checkId (rowLabel "DecisionPrecedence" k) o k
  let e ← homField (rowLabel "DecisionPrecedence" k) o "earlier" nd
  let l ← homField (rowLabel "DecisionPrecedence" k) o "later" nd
  pure ⟨e, l⟩

def encodeDecisionRow {nv : Nat} (k : Nat) (r : DecisionRow nv) : Json :=
  Json.mkObj [("_id", natJson (k + 1)), ("decision_variable", natJson (r.action.val + 1)),
    ("decision_name", .str r.name)]

def encodeInformationRow {nv nd : Nat} (k : Nat) (r : InformationRow nv nd) : Json :=
  Json.mkObj [("_id", natJson (k + 1)), ("information_decision", natJson (r.decision.val + 1)),
    ("information_variable", natJson (r.var.val + 1)),
    ("information_position", natJson (r.position + 1))]

def encodeUtilityRow (k : Nat) (r : UtilityRow) : Json :=
  Json.mkObj [("_id", natJson (k + 1)), ("utility_name", .str r.name),
    ("utility_ref", encodeRef r.ref)]

def encodeUtilityInputRow {nv nu : Nat} (k : Nat) (r : UtilityInputRow nv nu) : Json :=
  Json.mkObj [("_id", natJson (k + 1)), ("utility_node", natJson (r.utility.val + 1)),
    ("utility_variable", natJson (r.var.val + 1)), ("utility_position", natJson (r.position + 1))]

def encodePrecedenceRow {nd : Nat} (k : Nat) (r : PrecedenceRow nd) : Json :=
  Json.mkObj [("_id", natJson (k + 1)), ("earlier", natJson (r.earlier.val + 1)),
    ("later", natJson (r.later.val + 1))]

def DecisionRowMatches {nv : Nat} (k : Nat) (j : Json) (r : DecisionRow nv) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 3 ∧ o["_id"]? = some (natJson (k + 1)) ∧
    o["decision_variable"]? = some (natJson (r.action.val + 1)) ∧
    o["decision_name"]? = some (.str r.name)

def InformationRowMatches {nv nd : Nat} (k : Nat) (j : Json) (r : InformationRow nv nd) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 4 ∧ o["_id"]? = some (natJson (k + 1)) ∧
    o["information_decision"]? = some (natJson (r.decision.val + 1)) ∧
    o["information_variable"]? = some (natJson (r.var.val + 1)) ∧
    o["information_position"]? = some (natJson (r.position + 1))

def UtilityRowMatches (k : Nat) (j : Json) (r : UtilityRow) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 3 ∧ o["_id"]? = some (natJson (k + 1)) ∧
    o["utility_name"]? = some (.str r.name) ∧
    ∃ rj, o["utility_ref"]? = some rj ∧ RefMatches rj r.ref

def UtilityInputRowMatches {nv nu : Nat} (k : Nat) (j : Json) (r : UtilityInputRow nv nu) :
    Prop :=
  ∃ o, j = .obj o ∧ o.size = 4 ∧ o["_id"]? = some (natJson (k + 1)) ∧
    o["utility_node"]? = some (natJson (r.utility.val + 1)) ∧
    o["utility_variable"]? = some (natJson (r.var.val + 1)) ∧
    o["utility_position"]? = some (natJson (r.position + 1))

def PrecedenceRowMatches {nd : Nat} (k : Nat) (j : Json) (r : PrecedenceRow nd) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 3 ∧ o["_id"]? = some (natJson (k + 1)) ∧
    o["earlier"]? = some (natJson (r.earlier.val + 1)) ∧
    o["later"]? = some (natJson (r.later.val + 1))

theorem decodeDecisionRow_eq_ok {nv k : Nat} {j : Json} {r : DecisionRow nv} :
    decodeDecisionRow nv k j = .ok r ↔ DecisionRowMatches k j r := by
  unfold decodeDecisionRow DecisionRowMatches
  simp only [bind_eq_ok, object_eq_ok, checkId_eq_ok, strField_eq_ok, homField_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hid, v, hv, n, hn, rfl⟩
    exact ⟨o, rfl, hs, hid, hv, hn⟩
  · rintro ⟨o, rfl, hs, hid, hv, hn⟩
    exact ⟨o, ⟨rfl, hs⟩, (), hid, _, hv, _, hn, rfl⟩

theorem decodeInformationRow_eq_ok {nv nd k : Nat} {j : Json} {r : InformationRow nv nd} :
    decodeInformationRow nv nd k j = .ok r ↔ InformationRowMatches k j r := by
  unfold decodeInformationRow InformationRowMatches
  simp only [bind_eq_ok, object_eq_ok, checkId_eq_ok, homField_eq_ok, posField_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hid, d, hd, v, hv, p, hp, rfl⟩
    exact ⟨o, rfl, hs, hid, hd, hv, hp⟩
  · rintro ⟨o, rfl, hs, hid, hd, hv, hp⟩
    exact ⟨o, ⟨rfl, hs⟩, (), hid, _, hd, _, hv, _, hp, rfl⟩

theorem decodeUtilityRow_eq_ok {k : Nat} {j : Json} {r : UtilityRow} :
    decodeUtilityRow k j = .ok r ↔ UtilityRowMatches k j r := by
  unfold decodeUtilityRow UtilityRowMatches
  simp only [bind_eq_ok, object_eq_ok, checkId_eq_ok, strField_eq_ok, field_eq_ok,
    decodeRef_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hid, n, hn, rj, hrj, ref, href, rfl⟩
    exact ⟨o, rfl, hs, hid, hn, rj, hrj, href⟩
  · rintro ⟨o, rfl, hs, hid, hn, rj, hrj, href⟩
    exact ⟨o, ⟨rfl, hs⟩, (), hid, _, hn, rj, hrj, _, href, rfl⟩

theorem decodeUtilityInputRow_eq_ok {nv nu k : Nat} {j : Json} {r : UtilityInputRow nv nu} :
    decodeUtilityInputRow nv nu k j = .ok r ↔ UtilityInputRowMatches k j r := by
  unfold decodeUtilityInputRow UtilityInputRowMatches
  simp only [bind_eq_ok, object_eq_ok, checkId_eq_ok, homField_eq_ok, posField_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hid, q, hq, v, hv, p, hp, rfl⟩
    exact ⟨o, rfl, hs, hid, hq, hv, hp⟩
  · rintro ⟨o, rfl, hs, hid, hq, hv, hp⟩
    exact ⟨o, ⟨rfl, hs⟩, (), hid, _, hq, _, hv, _, hp, rfl⟩

theorem decodePrecedenceRow_eq_ok {nd k : Nat} {j : Json} {r : PrecedenceRow nd} :
    decodePrecedenceRow nd k j = .ok r ↔ PrecedenceRowMatches k j r := by
  unfold decodePrecedenceRow PrecedenceRowMatches
  simp only [bind_eq_ok, object_eq_ok, checkId_eq_ok, homField_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hid, e, he, l, hl, rfl⟩
    exact ⟨o, rfl, hs, hid, he, hl⟩
  · rintro ⟨o, rfl, hs, hid, he, hl⟩
    exact ⟨o, ⟨rfl, hs⟩, (), hid, _, he, _, hl, rfl⟩

theorem decisionRowMatches_encode {nv : Nat} (k : Nat) (r : DecisionRow nv) :
    DecisionRowMatches k (encodeDecisionRow k r) r :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp)⟩

theorem informationRowMatches_encode {nv nd : Nat} (k : Nat) (r : InformationRow nv nd) :
    InformationRowMatches k (encodeInformationRow k r) r :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp)⟩

theorem utilityRowMatches_encode (k : Nat) (r : UtilityRow) :
    UtilityRowMatches k (encodeUtilityRow k r) r :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), _, mkObj_getElem? (by simp) (by simp),
    refMatches_encodeRef _⟩

theorem utilityInputRowMatches_encode {nv nu : Nat} (k : Nat) (r : UtilityInputRow nv nu) :
    UtilityInputRowMatches k (encodeUtilityInputRow k r) r :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp)⟩

theorem precedenceRowMatches_encode {nd : Nat} (k : Nat) (r : PrecedenceRow nd) :
    PrecedenceRowMatches k (encodePrecedenceRow k r) r :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp)⟩

/-! ## The diagram body and the envelope -/

/-- The object tables of `SchInfluenceDiagram`. -/
def idObjectTables : List String :=
  ["Variable", "State", "Mechanism", "Input", "Decision", "InformationInput", "Utility",
    "UtilityInput", "DecisionPrecedence"]

/-- The columns of each object table of `SchInfluenceDiagram`. -/
def idColumns : String → List (String × ColumnKind)
  | "Variable" => [("_id", .id), ("variable_name", .label), ("space_ref", .ref)]
  | "State" => [("_id", .id), ("state_variable", .hom "Variable"), ("state_name", .label),
      ("state_position", .position)]
  | "Mechanism" => [("_id", .id), ("target", .hom "Variable"), ("mechanism_name", .label),
      ("kernel_ref", .ref)]
  | "Input" => [("_id", .id), ("input_mechanism", .hom "Mechanism"),
      ("input_variable", .hom "Variable"), ("input_position", .position)]
  | "Decision" => [("_id", .id), ("decision_variable", .hom "Variable"),
      ("decision_name", .label)]
  | "InformationInput" => [("_id", .id), ("information_decision", .hom "Decision"),
      ("information_variable", .hom "Variable"), ("information_position", .position)]
  | "Utility" => [("_id", .id), ("utility_name", .label), ("utility_ref", .ref)]
  | "UtilityInput" => [("_id", .id), ("utility_node", .hom "Utility"),
      ("utility_variable", .hom "Variable"), ("utility_position", .position)]
  | "DecisionPrecedence" => [("_id", .id), ("earlier", .hom "Decision"),
      ("later", .hom "Decision")]
  | _ => []

def decodeDiagramBody (j : Json) : Except String Diagram := do
  let body ← object "acset" 12 j
  emptyTable body "Label"
  emptyTable body "Position"
  emptyTable body "Ref"
  let V ← decodeTable body "Variable" decodeVariableRow
  let S ← decodeTable body "State" (decodeStateRow V.1)
  let M ← decodeTable body "Mechanism" (decodeMechanismRow V.1)
  let I ← decodeTable body "Input" (decodeInputRow V.1 M.1)
  let D ← decodeTable body "Decision" (decodeDecisionRow V.1)
  let F ← decodeTable body "InformationInput" (decodeInformationRow V.1 D.1)
  let U ← decodeTable body "Utility" decodeUtilityRow
  let Q ← decodeTable body "UtilityInput" (decodeUtilityInputRow V.1 U.1)
  let P ← decodeTable body "DecisionPrecedence" (decodePrecedenceRow D.1)
  pure ⟨V.1, S.1, M.1, I.1, D.1, F.1, U.1, Q.1, P.1, V.2, S.2, M.2, I.2, D.2, F.2, U.2, Q.2, P.2⟩

/-- The body is the ACSet JSON of `r`: exactly the twelve tables, the attribute tables empty, and
each object table matching `r` row for row. -/
def DiagramBodyMatches (j : Json) (r : Diagram) : Prop :=
  ∃ body, j = .obj body ∧ body.size = 12 ∧
    body["Label"]? = some (.arr #[]) ∧ body["Position"]? = some (.arr #[]) ∧
    body["Ref"]? = some (.arr #[]) ∧
    TableMatches body "Variable" VariableRowMatches r.nv r.vars ∧
    TableMatches body "State" StateRowMatches r.ns r.states ∧
    TableMatches body "Mechanism" MechanismRowMatches r.nm r.mechanisms ∧
    TableMatches body "Input" InputRowMatches r.ni r.inputs ∧
    TableMatches body "Decision" DecisionRowMatches r.nd r.decisions ∧
    TableMatches body "InformationInput" InformationRowMatches r.nf r.information ∧
    TableMatches body "Utility" UtilityRowMatches r.nu r.utilities ∧
    TableMatches body "UtilityInput" UtilityInputRowMatches r.nq r.utilityInputs ∧
    TableMatches body "DecisionPrecedence" PrecedenceRowMatches r.np r.precedence

theorem decodeDiagramBody_eq_ok {j : Json} {r : Diagram} :
    decodeDiagramBody j = .ok r ↔ DiagramBodyMatches j r := by
  unfold decodeDiagramBody DiagramBodyMatches
  simp only [bind_eq_ok, object_eq_ok, emptyTable_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨body, ⟨rfl, hs⟩, _, hL, _, hP, _, hR, ⟨nv, vars⟩, hV, ⟨ns, states⟩, hS,
      ⟨nm, mechs⟩, hM, ⟨ni, inputs⟩, hI, ⟨nd, decs⟩, hD, ⟨nf, info⟩, hF, ⟨nu, utils⟩, hU,
      ⟨nq, uinputs⟩, hQ, ⟨np, prec⟩, hPr, rfl⟩
    exact ⟨body, rfl, hs, hL, hP, hR,
      (decodeTable_eq_ok fun _ _ _ => decodeVariableRow_eq_ok).1 hV,
      (decodeTable_eq_ok fun _ _ _ => decodeStateRow_eq_ok).1 hS,
      (decodeTable_eq_ok fun _ _ _ => decodeMechanismRow_eq_ok).1 hM,
      (decodeTable_eq_ok fun _ _ _ => decodeInputRow_eq_ok).1 hI,
      (decodeTable_eq_ok fun _ _ _ => decodeDecisionRow_eq_ok).1 hD,
      (decodeTable_eq_ok fun _ _ _ => decodeInformationRow_eq_ok).1 hF,
      (decodeTable_eq_ok fun _ _ _ => decodeUtilityRow_eq_ok).1 hU,
      (decodeTable_eq_ok fun _ _ _ => decodeUtilityInputRow_eq_ok).1 hQ,
      (decodeTable_eq_ok fun _ _ _ => decodePrecedenceRow_eq_ok).1 hPr⟩
  · rintro ⟨body, rfl, hs, hL, hP, hR, hV, hS, hM, hI, hD, hF, hU, hQ, hPr⟩
    exact ⟨body, ⟨rfl, hs⟩, (), hL, (), hP, (), hR,
      ⟨r.nv, r.vars⟩, (decodeTable_eq_ok fun _ _ _ => decodeVariableRow_eq_ok).2 hV,
      ⟨r.ns, r.states⟩, (decodeTable_eq_ok fun _ _ _ => decodeStateRow_eq_ok).2 hS,
      ⟨r.nm, r.mechanisms⟩, (decodeTable_eq_ok fun _ _ _ => decodeMechanismRow_eq_ok).2 hM,
      ⟨r.ni, r.inputs⟩, (decodeTable_eq_ok fun _ _ _ => decodeInputRow_eq_ok).2 hI,
      ⟨r.nd, r.decisions⟩, (decodeTable_eq_ok fun _ _ _ => decodeDecisionRow_eq_ok).2 hD,
      ⟨r.nf, r.information⟩, (decodeTable_eq_ok fun _ _ _ => decodeInformationRow_eq_ok).2 hF,
      ⟨r.nu, r.utilities⟩, (decodeTable_eq_ok fun _ _ _ => decodeUtilityRow_eq_ok).2 hU,
      ⟨r.nq, r.utilityInputs⟩,
      (decodeTable_eq_ok fun _ _ _ => decodeUtilityInputRow_eq_ok).2 hQ,
      ⟨r.np, r.precedence⟩, (decodeTable_eq_ok fun _ _ _ => decodePrecedenceRow_eq_ok).2 hPr,
      rfl⟩

def encodeDiagramBody (r : Diagram) : Json :=
  Json.mkObj [("Variable", encodeTable encodeVariableRow r.vars),
    ("State", encodeTable encodeStateRow r.states),
    ("Mechanism", encodeTable encodeMechanismRow r.mechanisms),
    ("Input", encodeTable encodeInputRow r.inputs),
    ("Decision", encodeTable encodeDecisionRow r.decisions),
    ("InformationInput", encodeTable encodeInformationRow r.information),
    ("Utility", encodeTable encodeUtilityRow r.utilities),
    ("UtilityInput", encodeTable encodeUtilityInputRow r.utilityInputs),
    ("DecisionPrecedence", encodeTable encodePrecedenceRow r.precedence),
    ("Label", .arr #[]), ("Position", .arr #[]), ("Ref", .arr #[])]

theorem diagramBodyMatches_encode (r : Diagram) : DiagramBodyMatches (encodeDiagramBody r) r :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp),
    tableMatches_encode (mkObj_getElem? (by simp) (by simp)) variableRowMatches_encode,
    tableMatches_encode (mkObj_getElem? (by simp) (by simp)) stateRowMatches_encode,
    tableMatches_encode (mkObj_getElem? (by simp) (by simp)) mechanismRowMatches_encode,
    tableMatches_encode (mkObj_getElem? (by simp) (by simp)) inputRowMatches_encode,
    tableMatches_encode (mkObj_getElem? (by simp) (by simp)) decisionRowMatches_encode,
    tableMatches_encode (mkObj_getElem? (by simp) (by simp)) informationRowMatches_encode,
    tableMatches_encode (mkObj_getElem? (by simp) (by simp)) utilityRowMatches_encode,
    tableMatches_encode (mkObj_getElem? (by simp) (by simp)) utilityInputRowMatches_encode,
    tableMatches_encode (mkObj_getElem? (by simp) (by simp)) precedenceRowMatches_encode⟩

/-- The format name `write_json_influence_diagram` writes. -/
def idFormat : String := "influence-diagram-acset"

/-- **The decoder.** A parsed `write_json_influence_diagram` document to its rows. -/
def decodeDiagram (j : Json) : Except String Diagram := do
  let body ← decodeEnvelope idFormat j
  decodeDiagramBody body

/-- **The encoder**, the layout `write_json_influence_diagram` writes (up to key order and
whitespace). -/
def encodeDiagram (r : Diagram) : Json := encodeEnvelope idFormat (encodeDiagramBody r)

/-- **Faithfulness.** Decoding succeeds with `r` exactly when the document is an
`"influence-diagram-acset"` envelope whose body has `r`'s row counts and, row by row and column
by column, `r`'s values. -/
theorem decodeDiagram_eq_ok {j : Json} {r : Diagram} :
    decodeDiagram j = .ok r ↔ ∃ body, EnvelopeMatches idFormat j body ∧ DiagramBodyMatches body r := by
  unfold decodeDiagram
  simp only [bind_eq_ok, decodeEnvelope_eq_ok, decodeDiagramBody_eq_ok]

/-- **Round trip.** -/
theorem decodeDiagram_encodeDiagram (r : Diagram) : decodeDiagram (encodeDiagram r) = .ok r :=
  decodeDiagram_eq_ok.2 ⟨_, envelopeMatches_encode _ _, diagramBodyMatches_encode r⟩

/-- With a well-formed envelope, the document decodes exactly as its body. -/
theorem decodeDiagram_of_envelope {j body : Json} (h : EnvelopeMatches idFormat j body) :
    decodeDiagram j = decodeDiagramBody body := by
  unfold decodeDiagram
  rw [decodeEnvelope_eq_ok.2 h]
  rfl

/-! ## Shape and failures -/

/-- A decoded body has the shape of `SchInfluenceDiagram`. -/
theorem DiagramBodyMatches.shape {j : Json} {r : Diagram} (h : DiagramBodyMatches j r) :
    ∃ body, j = .obj body ∧ Shape idObjectTables idColumns body := by
  obtain ⟨body, rfl, -, -, -, -, hV, hS, hM, hI, hD, hF, hU, hQ, hP⟩ := h
  refine ⟨body, rfl, ?_⟩
  have cV := rowCount_of_tableMatches hV
  have cM := rowCount_of_tableMatches hM
  have cD := rowCount_of_tableMatches hD
  have cU := rowCount_of_tableMatches hU
  intro T hT
  simp only [idObjectTables, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, ha, -, -⟩ := id hV
    refine ⟨a, ha, fun k hk => ?_⟩
    obtain ⟨i, -, o, ho, hs, hid, hn, rj, hrj, href⟩ := hV.row ha k hk
    refine ⟨o, ho, hs, fun c κ hc => ?_⟩
    simp only [idColumns, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hid, rfl⟩
    · exact ⟨_, hn, _, rfl⟩
    · exact ⟨_, hrj, _, href⟩
  · obtain ⟨a, ha, -, -⟩ := id hS
    refine ⟨a, ha, fun k hk => ?_⟩
    obtain ⟨i, -, o, ho, hs, hid, hv, hn, hp⟩ := hS.row ha k hk
    refine ⟨o, ho, hs, fun c κ hc => ?_⟩
    simp only [idColumns, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hid, rfl⟩
    · exact ⟨_, hv, _, rfl, by rw [cV]; exact natJson_le⟩
    · exact ⟨_, hn, _, rfl⟩
    · exact ⟨_, hp, _, rfl, Nat.le_add_left 1 _⟩
  · obtain ⟨a, ha, -, -⟩ := id hM
    refine ⟨a, ha, fun k hk => ?_⟩
    obtain ⟨i, -, o, ho, hs, hid, hv, hn, rj, hrj, href⟩ := hM.row ha k hk
    refine ⟨o, ho, hs, fun c κ hc => ?_⟩
    simp only [idColumns, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hid, rfl⟩
    · exact ⟨_, hv, _, rfl, by rw [cV]; exact natJson_le⟩
    · exact ⟨_, hn, _, rfl⟩
    · exact ⟨_, hrj, _, href⟩
  · obtain ⟨a, ha, -, -⟩ := id hI
    refine ⟨a, ha, fun k hk => ?_⟩
    obtain ⟨i, -, o, ho, hs, hid, hm, hv, hp⟩ := hI.row ha k hk
    refine ⟨o, ho, hs, fun c κ hc => ?_⟩
    simp only [idColumns, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hid, rfl⟩
    · exact ⟨_, hm, _, rfl, by rw [cM]; exact natJson_le⟩
    · exact ⟨_, hv, _, rfl, by rw [cV]; exact natJson_le⟩
    · exact ⟨_, hp, _, rfl, Nat.le_add_left 1 _⟩
  · obtain ⟨a, ha, -, -⟩ := id hD
    refine ⟨a, ha, fun k hk => ?_⟩
    obtain ⟨i, -, o, ho, hs, hid, hv, hn⟩ := hD.row ha k hk
    refine ⟨o, ho, hs, fun c κ hc => ?_⟩
    simp only [idColumns, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hid, rfl⟩
    · exact ⟨_, hv, _, rfl, by rw [cV]; exact natJson_le⟩
    · exact ⟨_, hn, _, rfl⟩
  · obtain ⟨a, ha, -, -⟩ := id hF
    refine ⟨a, ha, fun k hk => ?_⟩
    obtain ⟨i, -, o, ho, hs, hid, hd, hv, hp⟩ := hF.row ha k hk
    refine ⟨o, ho, hs, fun c κ hc => ?_⟩
    simp only [idColumns, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hid, rfl⟩
    · exact ⟨_, hd, _, rfl, by rw [cD]; exact natJson_le⟩
    · exact ⟨_, hv, _, rfl, by rw [cV]; exact natJson_le⟩
    · exact ⟨_, hp, _, rfl, Nat.le_add_left 1 _⟩
  · obtain ⟨a, ha, -, -⟩ := id hU
    refine ⟨a, ha, fun k hk => ?_⟩
    obtain ⟨i, -, o, ho, hs, hid, hn, rj, hrj, href⟩ := hU.row ha k hk
    refine ⟨o, ho, hs, fun c κ hc => ?_⟩
    simp only [idColumns, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hid, rfl⟩
    · exact ⟨_, hn, _, rfl⟩
    · exact ⟨_, hrj, _, href⟩
  · obtain ⟨a, ha, -, -⟩ := id hQ
    refine ⟨a, ha, fun k hk => ?_⟩
    obtain ⟨i, -, o, ho, hs, hid, hq, hv, hp⟩ := hQ.row ha k hk
    refine ⟨o, ho, hs, fun c κ hc => ?_⟩
    simp only [idColumns, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hid, rfl⟩
    · exact ⟨_, hq, _, rfl, by rw [cU]; exact natJson_le⟩
    · exact ⟨_, hv, _, rfl, by rw [cV]; exact natJson_le⟩
    · exact ⟨_, hp, _, rfl, Nat.le_add_left 1 _⟩
  · obtain ⟨a, ha, -, -⟩ := id hP
    refine ⟨a, ha, fun k hk => ?_⟩
    obtain ⟨i, -, o, ho, hs, hid, he, hl⟩ := hP.row ha k hk
    refine ⟨o, ho, hs, fun c κ hc => ?_⟩
    simp only [idColumns, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hid, rfl⟩
    · exact ⟨_, he, _, rfl, by rw [cD]; exact natJson_le⟩
    · exact ⟨_, hl, _, rfl, by rw [cD]; exact natJson_le⟩

theorem decodeDiagramBody_shape {acset : JsonObject} {r : Diagram}
    (h : decodeDiagramBody (.obj acset) = .ok r) : Shape idObjectTables idColumns acset := by
  obtain ⟨body, hb, hs⟩ := (decodeDiagramBody_eq_ok.1 h).shape
  cases hb
  exact hs

/-- **Failure: a missing object table.** -/
theorem decodeDiagramBody_error_of_missing_table {acset : JsonObject} {T : String}
    (hT : T ∈ idObjectTables) (h : acset[T]? = none) (r : Diagram) :
    decodeDiagramBody (.obj acset) ≠ .ok r := fun hd => by
  obtain ⟨a, ha⟩ := (decodeDiagramBody_shape hd).table hT
  rw [h] at ha
  cases ha

/-- **Failure: a row that is not an object, or has missing or extra columns.** -/
theorem decodeDiagramBody_error_of_bad_row {acset : JsonObject} {T : String} {a : Array Json}
    {k : Nat} {row : Json} (hT : T ∈ idObjectTables) (ha : acset[T]? = some (.arr a))
    (hk : a[k]? = some row)
    (hrow : ∀ ro : JsonObject, row = .obj ro → ro.size ≠ (idColumns T).length) (r : Diagram) :
    decodeDiagramBody (.obj acset) ≠ .ok r := fun hd => by
  obtain ⟨ro, hro, hs⟩ := (decodeDiagramBody_shape hd).row hT ha hk
  exact hrow ro hro hs

/-- **Failure: a missing or ill-formed column** (wrong JSON type, hom out of range, position `0`,
wrong `"_id"`, malformed `KernelRef`). -/
theorem decodeDiagramBody_error_of_bad_column {acset : JsonObject} {T : String} {a : Array Json}
    {k : Nat} {ro : JsonObject} {c : String} {κ : ColumnKind} (hT : T ∈ idObjectTables)
    (ha : acset[T]? = some (.arr a)) (hk : a[k]? = some (.obj ro)) (hc : (c, κ) ∈ idColumns T)
    (hbad : ∀ v, ro[c]? = some v → ¬ ColumnOk acset k v κ) (r : Diagram) :
    decodeDiagramBody (.obj acset) ≠ .ok r := fun hd => by
  obtain ⟨v, hv, hok⟩ := (decodeDiagramBody_shape hd).column hT ha hk hc
  exact hbad v hv hok

/-- **Failure: a hom ID out of range.** -/
theorem decodeDiagramBody_error_of_hom_out_of_range {acset : JsonObject} {T T' : String}
    {a : Array Json} {k e : Nat} {ro : JsonObject} {c : String} (hT : T ∈ idObjectTables)
    (ha : acset[T]? = some (.arr a)) (hk : a[k]? = some (.obj ro))
    (hc : (c, ColumnKind.hom T') ∈ idColumns T) (hv : ro[c]? = some (natJson e))
    (hout : e = 0 ∨ rowCount acset T' < e) (r : Diagram) :
    decodeDiagramBody (.obj acset) ≠ .ok r := by
  refine decodeDiagramBody_error_of_bad_column hT ha hk hc (fun v hv' hok => ?_) r
  rw [hv, Option.some.injEq] at hv'
  subst hv'
  have := hok.hom_range
  omega

/-- **Failure: an ID, hom or position column that is not a nonnegative JSON integer.** -/
theorem decodeDiagramBody_error_of_not_integer {acset : JsonObject} {T : String}
    {a : Array Json} {k : Nat} {ro : JsonObject} {c : String} {κ : ColumnKind} {v : Json}
    (hT : T ∈ idObjectTables) (ha : acset[T]? = some (.arr a)) (hk : a[k]? = some (.obj ro))
    (hc : (c, κ) ∈ idColumns T) (hκ : κ = .id ∨ κ = .position ∨ ∃ T', κ = .hom T')
    (hv : ro[c]? = some v) (hnot : jsonNat? v = none) (r : Diagram) :
    decodeDiagramBody (.obj acset) ≠ .ok r := by
  refine decodeDiagramBody_error_of_bad_column hT ha hk hc (fun v' hv' hok => ?_) r
  rw [hv, Option.some.injEq] at hv'
  subst hv'
  have := hok.isNat hκ
  rw [hnot] at this
  cases this

/-- **Failure: a `Label` column that is not a JSON string.** -/
theorem decodeDiagramBody_error_of_not_string {acset : JsonObject} {T : String}
    {a : Array Json} {k : Nat} {ro : JsonObject} {c : String} {v : Json}
    (hT : T ∈ idObjectTables) (ha : acset[T]? = some (.arr a)) (hk : a[k]? = some (.obj ro))
    (hc : (c, ColumnKind.label) ∈ idColumns T) (hv : ro[c]? = some v) (hnot : ∀ s, v ≠ .str s)
    (r : Diagram) : decodeDiagramBody (.obj acset) ≠ .ok r := by
  refine decodeDiagramBody_error_of_bad_column hT ha hk hc (fun v' hv' hok => ?_) r
  rw [hv, Option.some.injEq] at hv'
  subst hv'
  obtain ⟨s, rfl⟩ := hok
  exact hnot s rfl

/-! ## The checked decoder -/

/-- **The checked decoder**: decode and run `Diagram.fullCheck`. -/
def decodeDiagramChecked (j : Json) : Option (Σ' r : Diagram, r.FullValid) :=
  match decodeDiagram j with
  | .ok r => if h : r.fullCheck = true then some ⟨r, (Diagram.fullCheck_iff r).1 h⟩ else none
  | .error _ => none

theorem decodeDiagramChecked_eq_some {j : Json} {r : Diagram} {h : r.FullValid} :
    decodeDiagramChecked j = some ⟨r, h⟩ ↔ decodeDiagram j = .ok r := by
  unfold decodeDiagramChecked
  constructor
  · intro hd
    split at hd
    · rename_i r' hr'
      split_ifs at hd
      simp only [Option.some.injEq, PSigma.mk.injEq] at hd
      obtain ⟨rfl, -⟩ := hd
      exact hr'
    · cases hd
  · intro hd
    rw [hd]
    simp only
    rw [dif_pos ((Diagram.fullCheck_iff r).2 h)]

/-- **Exactly the fully valid documents decode.** -/
theorem decodeDiagramChecked_isSome_iff {j : Json} :
    (decodeDiagramChecked j).isSome ↔ ∃ r, decodeDiagram j = .ok r ∧ r.FullValid := by
  constructor
  · intro hs
    obtain ⟨⟨r, h⟩, hr⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨r, decodeDiagramChecked_eq_some.1 hr, h⟩
  · rintro ⟨r, hr, h⟩
    rw [decodeDiagramChecked_eq_some (h := h) |>.2 hr]
    rfl

/-- **Completeness on encoded diagrams**: every fully valid diagram is recovered exactly. -/
theorem decodeDiagramChecked_encode {r : Diagram} (h : r.FullValid) :
    decodeDiagramChecked (encodeDiagram r) = some ⟨r, h⟩ :=
  decodeDiagramChecked_eq_some.2 (decodeDiagram_encodeDiagram r)

/-- **The checked decoder for `validate(...; unique_names = true)`**: decode, then run
`Diagram.fullCheck` and `Diagram.namesCheck`. -/
def decodeDiagramCheckedNames (j : Json) : Option (Σ' r : Diagram, r.FullValid ∧ r.NamesUnique) :=
  match decodeDiagram j with
  | .ok r =>
    if h : r.fullCheck = true ∧ r.namesCheck = true then
      some ⟨r, (Diagram.fullCheck_iff r).1 h.1, (Diagram.namesCheck_iff r).1 h.2⟩
    else none
  | .error _ => none

/-- **Exactly the fully valid documents with unique names decode.** -/
theorem decodeDiagramCheckedNames_isSome_iff {j : Json} :
    (decodeDiagramCheckedNames j).isSome ↔
      ∃ r, decodeDiagram j = .ok r ∧ r.FullValid ∧ r.NamesUnique := by
  unfold decodeDiagramCheckedNames
  constructor
  · intro hs
    split at hs
    · rename_i r hr
      split_ifs at hs with h
      · exact ⟨r, hr, (Diagram.fullCheck_iff r).1 h.1, (Diagram.namesCheck_iff r).1 h.2⟩
      · simp at hs
    · simp at hs
  · rintro ⟨r, hr, hv, hn⟩
    rw [hr]
    simp only
    rw [dif_pos ⟨(Diagram.fullCheck_iff r).2 hv, (Diagram.namesCheck_iff r).2 hn⟩]
    rfl

/-- **The policy-table axes in the document.** After a successful checked decode, for every
decision `d` and every slot `j` of its policy mechanism in the instantiated chance part, the
document's `"InformationInput"` table has a row with `information_decision = d + 1`,
`information_position = j + 1` and `information_variable` the slot's variable plus one; and for
every state `a` of `d`'s action, the `"State"` table has a row with `state_variable` the action
plus one, `state_position = a + 1` and `state_name` the label `stateLabel a`, which orders the
action axis that `solveRepRecords_table_of_fullValid` reads. -/
theorem decodeDiagramChecked_policyAxes {j : Json} {r : Diagram} {h : r.FullValid}
    (hd : decodeDiagramChecked j = some ⟨r, h⟩) (rank : Fin r.nv → Fin r.nv)
    (hrank : (r.chance.withRank rank).Valid) (d : Fin r.nd) :
    (∀ slot : Fin ((r.chance.withRank rank).inputCount (Fin.natAdd r.nm d)),
      ∃ (acset : JsonObject) (arr : Array Json), EnvelopeMatches idFormat j (.obj acset) ∧
        acset["InformationInput"]? = some (.arr arr) ∧
        ∃ (k : Nat) (ro : JsonObject), arr[k]? = some (.obj ro) ∧
          ro["information_decision"]? = some (natJson (d.val + 1)) ∧
          ro["information_position"]? = some (natJson (slot.val + 1)) ∧
          ro["information_variable"]? =
            some (natJson (((r.chance.withRank rank).slotVariable hrank _ slot).val + 1))) ∧
    ∀ a : Fin (r.stateCount (r.decisions d).action),
      ∃ (acset : JsonObject) (arr : Array Json), EnvelopeMatches idFormat j (.obj acset) ∧
        acset["State"]? = some (.arr arr) ∧
        ∃ (k : Nat) (ro : JsonObject), arr[k]? = some (.obj ro) ∧
          ro["state_variable"]? = some (natJson ((r.decisions d).action.val + 1)) ∧
          ro["state_position"]? = some (natJson (a.val + 1)) ∧
          ro["state_name"]? = some (.str (r.stateLabel h.valid _ a)) := by
  obtain ⟨body, henv, acset, rfl, -, -, -, -, -, hS, -, -, -, hF, -, -, -⟩ :=
    decodeDiagram_eq_ok.1 (decodeDiagramChecked_eq_some.1 hd)
  constructor
  · intro slot
    obtain ⟨arr, harr, -, hrows⟩ := hF
    set i := ((r.chance.withRank rank).inputOrder hrank _).symm slot
    have hown : (r.chance.inputs i.val).mechanism = Fin.natAdd r.nm d := i.property
    have hpos : (r.chance.inputs i.val).position = slot.val :=
      (r.chance.withRank rank).slot_position hrank _ slot
    have hslot : (r.chance.withRank rank).slotVariable hrank _ slot =
        (r.chance.inputs i.val).var := rfl
    have key : ∀ k : Fin (r.ni + r.nf), (r.chance.inputs k).mechanism = Fin.natAdd r.nm d →
        ∃ f, k = Fin.natAdd r.ni f := by
      intro k
      refine Fin.addCases (fun ci => ?_) (fun f => ?_) k
      · intro hk
        rw [Diagram.chance_input_left] at hk
        exact absurd hk (castAdd_ne_natAdd _ _)
      · intro _
        exact ⟨f, rfl⟩
    obtain ⟨f, hf⟩ := key i.val hown
    rw [hf, Diagram.chance_input_right] at hown hpos hslot
    have hdec : (r.information f).decision = d := Fin.natAdd_injective _ _ hown
    obtain ⟨x, hx, ro, rfl, -, -, hdj, hvj, hpj⟩ := hrows f
    refine ⟨acset, arr, henv, harr, f.val, ro, hx, ?_, ?_, ?_⟩
    · rw [hdj, hdec]
    · rw [hpj]
      exact congrArg (fun p => some (natJson (p + 1))) hpos
    · rw [hvj, hslot]
  · intro a
    obtain ⟨arr, harr, -, hrows⟩ := hS
    set s := r.stateRecord h.valid _ a
    obtain ⟨x, hx, ro, rfl, -, -, hvar, hname, hpos⟩ := hrows s
    refine ⟨acset, arr, henv, harr, s.val, ro, hx, ?_, ?_, hname⟩
    · rw [hvar, r.stateRecord_var h.valid _ a]
    · rw [hpos, r.stateRecord_position h.valid _ a]

end InfluenceDiagramsProofs.Records
