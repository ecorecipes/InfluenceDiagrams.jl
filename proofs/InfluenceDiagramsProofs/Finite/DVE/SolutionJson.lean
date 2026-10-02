import InfluenceDiagramsProofs.Finite.DVE.CertificateApprox

/-!
# Decoding the version-2 DVE certificate: Julia's recorded solution

`export_dve_certificate(m; solution = true)` (InfluenceDiagrams.jl, `src/certificates.jl`) writes
a version-2 certificate: the fourteen version-1 keys, with `"version": 2`, and one more key,
`"solution"`, holding the output of one Julia DVE run on the certificate's own cells. This module
decodes it. The version-1 decoder `decodeCertificate` and its theorems are unchanged; version 1
still decodes exactly as before.

**The layout of `"solution"`** (nine keys; confirmed on the umbrella, oil-wildcatter and grazing
certificates and on `docs/src/dve-certificate-v2.schema.json`):

* `"backend"`: `{name, order, stable, atol_f64, constancy_atol_f64}`, `name` the string
  `"DecisionVariableElimination"`, `order` a string, `stable` a boolean, `atol_f64` `null` or a
  binary64 word, `constancy_atol_f64` a word;
* `"arithmetic"`: `"binary64"` or `"exact_rational"`; `"data"`: `"f64"` or `"q"`;
  `"exact_fallback"`: a boolean; `"conditioned_on"`: the string `"evidence.hard"`;
  `"julia_version"`: a string;
* `"elimination_order"`: variable IDs; `"value"`: a solution number, `{"f64"}` or `{"q", "f64"}`;
* `"policies"`: one row per decision, in the order of `"decisions"`, each
  `{decision, action, axes, scope, entries}`: the decision ID, its action variable ID, the
  information variables in `information_position` order, the variables the run's table depends on,
  and `entries`, rows `{at, action, score}`: zero-based coordinates, the chosen action's state ID
  and the row's score.

**Checked while decoding.** Every variable reference is in range; policy `k` is decision `k`, its
`action` is that decision's action and its `axes` are that decision's information slots; every
entry's action is a state ID of the action variable; and the `at` lists are exactly
`lexCoords` of the axes' state counts, so they enumerate every configuration once,
lexicographically with the rightmost coordinate fastest (`decodeSolution_coverage`,
`lexCoords_nodup`, `lexCoords_pairwise_lex`).

**Results.** `decodeSolution_eq_ok` (faithfulness, key for key), `decodeCertificateV2_eq_ok`
(the fifteen keys: the version-1 fields, read by the same row decoders as `decodeCertificate`, and
the solution), `decodeCertificateV2_encode` (round trip), `decodeSolution_wellFormed` (references
in range, coverage), `decodeSolution_shape` with its corollaries
`decodeSolution_error_of_missing_key` / `decodeSolution_error_of_ill_typed`, and for the
dispatching decoder `decodeAnyCertificate`: `decodeAnyCertificate_v1` /
`decodeAnyCertificate_v2` and the exclusions `decodeAnyCertificate_error_of_v2_with_v1_keys` /
`decodeAnyCertificate_error_of_v1_with_v2_keys` (version 2 is not accepted with fourteen keys, nor
version 1 with fifteen).

Trusted, not proved: `Lean.Json.parse`, Julia's `export_dve_certificate` and `JSON3.write`.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVECertificate

open Lean (Json)
open BayesianNetworksProofs.Raw

/-! ## Leaves -/

/-- `null` or a binary64 word. -/
def optWordOf : Json → Except String (Option Nat)
  | .null => .ok none
  | .str s => do
    let w ← wordOf (.str s)
    pure (some w)
  | _ => .error "expected null or a binary64 word"

def OptWordMatches (j : Json) : Option Nat → Prop
  | none => j = .null
  | some w => j = .str (hexWord w) ∧ w < 2 ^ 64

theorem optWordOf_eq_ok {j : Json} {o : Option Nat} : optWordOf j = .ok o ↔ OptWordMatches j o := by
  cases o with
  | none =>
    cases j with
    | str s =>
      simp only [optWordOf, OptWordMatches, bind_eq_ok, pure_eq_ok]
      constructor
      · rintro ⟨w, -, h⟩
        exact absurd h (by simp)
      · intro h
        exact absurd h (by simp)
    | _ => simp [optWordOf, OptWordMatches]
  | some w =>
    cases j with
    | str s =>
      simp only [optWordOf, OptWordMatches, bind_eq_ok, wordOf_eq_ok, pure_eq_ok,
        Option.some.injEq]
      constructor
      · rintro ⟨w', ⟨h1, h2⟩, rfl⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨w, ⟨h1, h2⟩, rfl⟩
    | _ => simp [optWordOf, OptWordMatches]

def encodeOptWord : Option Nat → Json
  | none => .null
  | some w => .str (hexWord w)

/-- `"arithmetic"`: the arithmetic of Julia's run. -/
inductive Arithmetic where
  | binary64
  | exactRational
  deriving DecidableEq

def arithmeticString : Arithmetic → String
  | .binary64 => "binary64"
  | .exactRational => "exact_rational"

def arithmeticOf (j : Json) : Except String Arithmetic := do
  let s ← strOf j
  if s = "binary64" then pure .binary64
  else if s = "exact_rational" then pure .exactRational
  else throw s!"\"{s}\" is not \"binary64\" or \"exact_rational\""

theorem arithmeticOf_eq_ok {j : Json} {a : Arithmetic} :
    arithmeticOf j = .ok a ↔ j = .str (arithmeticString a) := by
  unfold arithmeticOf
  rw [bind_eq_ok]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [strOf_eq_ok] at hs
    subst hs
    split_ifs at h with h1 h2
    · subst h1
      rw [pure_eq_ok] at h
      subst h
      rfl
    · subst h2
      rw [pure_eq_ok] at h
      subst h
      rfl
  · rintro rfl
    refine ⟨_, strOf_eq_ok.2 rfl, ?_⟩
    cases a <;> simp [arithmeticString] <;> rfl

/-- `"data"`: which cells Julia's run read, the binary64 words or the rationals. -/
inductive DataKind where
  | f64
  | q
  deriving DecidableEq

def dataString : DataKind → String
  | .f64 => "f64"
  | .q => "q"

def dataOf (j : Json) : Except String DataKind := do
  let s ← strOf j
  if s = "f64" then pure .f64
  else if s = "q" then pure .q
  else throw s!"\"{s}\" is not \"f64\" or \"q\""

theorem dataOf_eq_ok {j : Json} {a : DataKind} : dataOf j = .ok a ↔ j = .str (dataString a) := by
  unfold dataOf
  rw [bind_eq_ok]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [strOf_eq_ok] at hs
    subst hs
    split_ifs at h with h1 h2
    · subst h1
      rw [pure_eq_ok] at h
      subst h
      rfl
    · subst h2
      rw [pure_eq_ok] at h
      subst h
      rfl
  · rintro rfl
    refine ⟨_, strOf_eq_ok.2 rfl, ?_⟩
    cases a <;> simp [dataString] <;> rfl

/-- A solution number: `{"f64"}` or `{"q", "f64"}`, never `{"q"}` alone. -/
def Value.IsSolutionNumber : Value → Prop
  | .q _ _ => False
  | _ => True

instance (x : Value) : Decidable x.IsSolutionNumber := by
  cases x <;> unfold Value.IsSolutionNumber <;> infer_instance

def solNumberOf (j : Json) : Except String Value := do
  let x ← decodeValue j
  require x.IsSolutionNumber "a solution number has the key \"f64\""
  pure x

theorem solNumberOf_eq_ok {j : Json} {x : Value} :
    solNumberOf j = .ok x ↔ ValueMatches j x ∧ x.IsSolutionNumber := by
  unfold solNumberOf
  simp only [bind_eq_ok, decodeValue_eq_ok, require_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨x', hx, _, hs, rfl⟩
    exact ⟨hx, hs⟩
  · rintro ⟨hx, hs⟩
    exact ⟨x, hx, (), hs, rfl⟩

/-! ## `"backend"` -/

/-- `"backend"`: the DVE backend Julia ran. -/
structure Backend where
  name : String
  order : String
  stable : Bool
  atol : Option Nat
  constancy : Nat
  deriving DecidableEq

/-- The backend name the profile records. -/
def backendName : String := "DecisionVariableElimination"

def decodeBackend (j : Json) : Except String Backend := do
  let o ← object "backend" 5 j
  let n ← get o "name" strOf
  require (n = backendName) s!"the backend is \"{n}\", expected \"{backendName}\""
  let ord ← get o "order" strOf
  let st ← get o "stable" boolOf
  let a ← get o "atol_f64" optWordOf
  let k ← get o "constancy_atol_f64" wordOf
  pure ⟨n, ord, st, a, k⟩

def BackendMatches (j : Json) (b : Backend) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 5 ∧ o["name"]? = some (.str b.name) ∧ b.name = backendName ∧
    o["order"]? = some (.str b.order) ∧ o["stable"]? = some (.bool b.stable) ∧
    (∃ v, o["atol_f64"]? = some v ∧ OptWordMatches v b.atol) ∧
    o["constancy_atol_f64"]? = some (.str (hexWord b.constancy)) ∧ b.constancy < 2 ^ 64

theorem decodeBackend_eq_ok {j : Json} {b : Backend} :
    decodeBackend j = .ok b ↔ BackendMatches j b := by
  unfold decodeBackend BackendMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok, require_eq_ok,
    get_eq_ok fun _ _ => boolOf_eq_ok, get_eq_ok fun _ _ => optWordOf_eq_ok,
    get_eq_ok fun _ _ => wordOf_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, n, ⟨_, hn, rfl⟩, _, hname, ord, ⟨_, hord, rfl⟩, st, ⟨_, hst, rfl⟩,
      a, ha, k, ⟨_, hk, rfl, hkl⟩, rfl⟩
    exact ⟨o, rfl, hs, hn, hname, hord, hst, ha, hk, hkl⟩
  · rintro ⟨o, rfl, hs, hn, hname, hord, hst, ha, hk, hkl⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hn, rfl⟩, (), hname, _, ⟨_, hord, rfl⟩, _, ⟨_, hst, rfl⟩, _, ha,
      _, ⟨_, hk, rfl, hkl⟩, rfl⟩

/-! ## Policies -/

/-- The state IDs of variable `v`, in `state_position` order (`[]` out of range). -/
def stateIds (c : Certificate) (v : Nat) : List Nat :=
  ((c.vars[v]?).map fun e => e.states.map StateEntry.id).getD []

/-- One recorded policy entry: zero-based coordinates along the axes, the chosen action's state
ID (as written) and the row's score. -/
structure PolicyEntry where
  coords : List Nat
  action : Nat
  score : Value
  deriving DecidableEq

def decodePolicyEntry (states : List Nat) (j : Json) : Except String PolicyEntry := do
  let o ← object "policy entry" 3 j
  let at_ ← getArr o "at" (fun _ => natOf)
  let a ← get o "action" idOf
  require (a ∈ states) s!"the action state {a} is not a state of the action variable"
  let s ← get o "score" solNumberOf
  pure ⟨at_, a, s⟩

def PolicyEntryMatches (states : List Nat) (j : Json) (e : PolicyEntry) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 3 ∧
    (∃ v, o["at"]? = some v ∧ ArrayMatches (fun _ x c => x = natJson c) v e.coords) ∧
    o["action"]? = some (.str (toString e.action)) ∧ 1 ≤ e.action ∧ e.action ∈ states ∧
    ∃ v, o["score"]? = some v ∧ ValueMatches v e.score ∧ e.score.IsSolutionNumber

theorem decodePolicyEntry_eq_ok {states : List Nat} {j : Json} {e : PolicyEntry} :
    decodePolicyEntry states j = .ok e ↔ PolicyEntryMatches states j e := by
  unfold decodePolicyEntry PolicyEntryMatches
  simp only [bind_eq_ok, object_eq_ok, getArr_eq_ok fun _ _ _ => natOf_eq_ok,
    get_eq_ok fun _ _ => idOf_eq_ok, require_eq_ok, get_eq_ok fun _ _ => solNumberOf_eq_ok,
    pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, c, hc, a, ⟨_, ha, rfl, h1⟩, _, hmem, s, hsc, rfl⟩
    exact ⟨o, rfl, hs, hc, ha, h1, hmem, hsc⟩
  · rintro ⟨o, rfl, hs, hc, ha, h1, hmem, hsc⟩
    exact ⟨o, ⟨rfl, hs⟩, _, hc, _, ⟨_, ha, rfl, h1⟩, (), hmem, _, hsc, rfl⟩

/-- One recorded policy: the zero-based decision and action-variable indices, the axes and the
scope (zero-based variable indices) and the entries. -/
structure PolicyRecord where
  decision : Nat
  action : Nat
  axes : List Nat
  scope : List Nat
  entries : List PolicyEntry
  deriving DecidableEq

/-- The information slots of decision `k`, as variable indices. -/
def infoVars (c : Certificate) (k : Nat) : Option (List Nat) :=
  (c.decisions[k]?).map fun e => e.information.map Slot.var

/-- Row `k` of `"policies"`: decision `k`, its action, its information slots as axes, and entries
covering the axes' configurations in lexicographic order. -/
def decodePolicy (c : Certificate) (k : Nat) (j : Json) : Except String PolicyRecord := do
  let o ← object "policy" 5 j
  let d ← get o "decision" (refOf c.decisions.length)
  require (d = k) s!"the policy of row {k} is for decision {d + 1}"
  let a ← get o "action" (refOf c.vars.length)
  require ((c.decisions[k]?).map DecisionEntry.action = some a)
    s!"variable {a + 1} is not the action of decision {k + 1}"
  let ax ← getArr o "axes" (fun _ => refOf c.vars.length)
  require (infoVars c k = some ax) s!"the axes are not the information slots of decision {k + 1}"
  let sc ← getArr o "scope" (fun _ => refOf c.vars.length)
  let es ← getArr o "entries" (fun _ => decodePolicyEntry (stateIds c a))
  require (es.map PolicyEntry.coords = lexCoords (ax.map (certDim c)))
    "the entries do not list every configuration once, lexicographically"
  pure ⟨d, a, ax, sc, es⟩

/-- A variable reference: the one-based ID string of an in-range index. -/
def VarRef (nv : Nat) (x : Json) (i : Nat) : Prop := x = .str (toString (i + 1)) ∧ i < nv

def PolicyMatches (c : Certificate) (k : Nat) (j : Json) (p : PolicyRecord) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 5 ∧
    o["decision"]? = some (.str (toString (p.decision + 1))) ∧ p.decision < c.decisions.length ∧
    p.decision = k ∧
    o["action"]? = some (.str (toString (p.action + 1))) ∧ p.action < c.vars.length ∧
    (c.decisions[k]?).map DecisionEntry.action = some p.action ∧
    (∃ v, o["axes"]? = some v ∧ ArrayMatches (fun _ => VarRef c.vars.length) v p.axes) ∧
    infoVars c k = some p.axes ∧
    (∃ v, o["scope"]? = some v ∧ ArrayMatches (fun _ => VarRef c.vars.length) v p.scope) ∧
    (∃ v, o["entries"]? = some v ∧
      ArrayMatches (fun _ => PolicyEntryMatches (stateIds c p.action)) v p.entries) ∧
    p.entries.map PolicyEntry.coords = lexCoords (p.axes.map (certDim c))

theorem decodePolicy_eq_ok {c : Certificate} {k : Nat} {j : Json} {p : PolicyRecord} :
    decodePolicy c k j = .ok p ↔ PolicyMatches c k j p := by
  unfold decodePolicy PolicyMatches VarRef
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => refOf_eq_ok, require_eq_ok,
    getArr_eq_ok fun _ _ _ => refOf_eq_ok, getArr_eq_ok fun _ _ _ => decodePolicyEntry_eq_ok,
    pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, d, ⟨_, hd, rfl, hdl⟩, _, hdk, a, ⟨_, ha, rfl, hal⟩, _, hact, ax, hax,
      _, hinfo, sc, hsc, es, hes, _, hcov, rfl⟩
    exact ⟨o, rfl, hs, hd, hdl, hdk, ha, hal, hact, hax, hinfo, hsc, hes, hcov⟩
  · rintro ⟨o, rfl, hs, hd, hdl, hdk, ha, hal, hact, hax, hinfo, hsc, hes, hcov⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hd, rfl, hdl⟩, (), hdk, _, ⟨_, ha, rfl, hal⟩, (), hact, _, hax,
      (), hinfo, _, hsc, _, hes, (), hcov, rfl⟩

/-! ## `"solution"` -/

/-- **Julia's recorded solution**, as `export_dve_certificate(m; solution = …)` writes it.
Variable references are zero-based indices. -/
structure Solution where
  backend : Backend
  arithmetic : Arithmetic
  data : DataKind
  exactFallback : Bool
  conditionedOn : String
  juliaVersion : String
  eliminationOrder : List Nat
  value : Value
  policies : List PolicyRecord
  deriving DecidableEq

/-- The evidence the run conditions on. -/
def conditionedOnHard : String := "evidence.hard"

/-- The nine keys of `"solution"`. -/
def solutionKeys : List String :=
  ["backend", "arithmetic", "data", "exact_fallback", "conditioned_on", "julia_version",
    "elimination_order", "value", "policies"]

/-- **The solution decoder**, in the context of the decoded version-1 fields `c`. -/
def decodeSolution (c : Certificate) (j : Json) : Except String Solution := do
  let o ← object "solution" 9 j
  let b ← get o "backend" decodeBackend
  let ar ← get o "arithmetic" arithmeticOf
  let da ← get o "data" dataOf
  let ef ← get o "exact_fallback" boolOf
  let co ← get o "conditioned_on" strOf
  require (co = conditionedOnHard) s!"conditioned_on is \"{co}\", expected \"{conditionedOnHard}\""
  let jv ← get o "julia_version" strOf
  let eo ← getArr o "elimination_order" (fun _ => refOf c.vars.length)
  let v ← get o "value" solNumberOf
  let ps ← getArr o "policies" (decodePolicy c)
  require (ps.length = c.decisions.length) "there is not one policy per decision"
  pure ⟨b, ar, da, ef, co, jv, eo, v, ps⟩

/-- **The document is the solution `s`** of the certificate `c`, key for key. -/
def SolutionMatches (c : Certificate) (j : Json) (s : Solution) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 9 ∧
    (∃ v, o["backend"]? = some v ∧ BackendMatches v s.backend) ∧
    o["arithmetic"]? = some (.str (arithmeticString s.arithmetic)) ∧
    o["data"]? = some (.str (dataString s.data)) ∧
    o["exact_fallback"]? = some (.bool s.exactFallback) ∧
    o["conditioned_on"]? = some (.str s.conditionedOn) ∧ s.conditionedOn = conditionedOnHard ∧
    o["julia_version"]? = some (.str s.juliaVersion) ∧
    (∃ v, o["elimination_order"]? = some v ∧
      ArrayMatches (fun _ => VarRef c.vars.length) v s.eliminationOrder) ∧
    (∃ v, o["value"]? = some v ∧ ValueMatches v s.value ∧ s.value.IsSolutionNumber) ∧
    (∃ v, o["policies"]? = some v ∧ ArrayMatches (PolicyMatches c) v s.policies) ∧
    s.policies.length = c.decisions.length

/-- **Faithfulness of the solution decoder.** -/
theorem decodeSolution_eq_ok {c : Certificate} {j : Json} {s : Solution} :
    decodeSolution c j = .ok s ↔ SolutionMatches c j s := by
  unfold decodeSolution SolutionMatches VarRef
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => decodeBackend_eq_ok,
    get_eq_ok fun _ _ => arithmeticOf_eq_ok, get_eq_ok fun _ _ => dataOf_eq_ok,
    get_eq_ok fun _ _ => boolOf_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok, require_eq_ok,
    getArr_eq_ok fun _ _ _ => refOf_eq_ok, get_eq_ok fun _ _ => solNumberOf_eq_ok,
    getArr_eq_ok fun _ _ _ => decodePolicy_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, b, hb, ar, ⟨_, har, rfl⟩, da, ⟨_, hda, rfl⟩, ef, ⟨_, hef, rfl⟩,
      co, ⟨_, hco, rfl⟩, _, hcoe, jv, ⟨_, hjv, rfl⟩, eo, heo, v, hv, ps, hps, _, hlen, rfl⟩
    exact ⟨o, rfl, hs, hb, har, hda, hef, hco, hcoe, hjv, heo, hv, hps, hlen⟩
  · rintro ⟨o, rfl, hs, hb, har, hda, hef, hco, hcoe, hjv, heo, hv, hps, hlen⟩
    exact ⟨o, ⟨rfl, hs⟩, _, hb, _, ⟨_, har, rfl⟩, _, ⟨_, hda, rfl⟩, _, ⟨_, hef, rfl⟩,
      _, ⟨_, hco, rfl⟩, (), hcoe, _, ⟨_, hjv, rfl⟩, _, heo, _, hv, _, hps, (), hlen, rfl⟩

/-! ## The version-2 certificate -/

/-- The twelve version-1 fields other than `"format"` and `"version"`, read by the decoders of
`decodeCertificate`. -/
def decodeBody (o : JsonObject) : Except String Certificate := do
  let prov ← get o "provenance" decodeProvenance
  let num ← get o "numeric" decodeNumeric
  let tol ← get o "runtime_tolerances" decodeTolerances
  let pool ← getArr o "reference_pool" decodePoolEntry
  let vars ← getArr o "variables" (decodeVariable pool.length)
  let decs ← getArr o "decisions" (decodeDecision vars.length)
  let topo ← getArr o "topological_order" (fun _ => refOf vars.length)
  let dord ← getArr o "decision_order" (fun _ => refOf decs.length)
  let mechs ← getArr o "mechanisms" (decodeMechanism vars.length pool.length)
  let prec ← getArr o "precedence" (decodePrecedence decs.length)
  let us ← getArr o "utilities" (decodeUtility vars.length pool.length)
  let hard ← get o "evidence" (decodeEvidence vars.length)
  pure ⟨prov, num, tol, pool, vars, topo, dord, mechs, decs, prec, us, hard⟩

/-- The twelve version-1 fields of `o` hold `c`'s values, as in `CertificateMatches`. -/
def BodyMatches (o : JsonObject) (c : Certificate) : Prop :=
  (∃ v, o["provenance"]? = some v ∧ ProvenanceMatches v c.provenance) ∧
    (∃ v, o["numeric"]? = some v ∧ NumericMatches v c.numeric) ∧
    (∃ v, o["runtime_tolerances"]? = some v ∧ TolerancesMatches v c.tolerances) ∧
    (∃ v, o["reference_pool"]? = some v ∧ ArrayMatches PoolMatches v c.pool) ∧
    (∃ v, o["variables"]? = some v ∧
      ArrayMatches (VariableMatches c.pool.length) v c.vars) ∧
    (∃ v, o["decisions"]? = some v ∧
      ArrayMatches (DecisionMatches c.vars.length) v c.decisions) ∧
    (∃ v, o["topological_order"]? = some v ∧
      ArrayMatches (fun _ x i => x = .str (toString (i + 1)) ∧ i < c.vars.length) v
        c.topological) ∧
    (∃ v, o["decision_order"]? = some v ∧
      ArrayMatches (fun _ x i => x = .str (toString (i + 1)) ∧ i < c.decisions.length) v
        c.decisionOrder) ∧
    (∃ v, o["mechanisms"]? = some v ∧
      ArrayMatches (MechanismMatches c.vars.length c.pool.length) v c.mechanisms) ∧
    (∃ v, o["precedence"]? = some v ∧
      ArrayMatches (PrecedenceMatches c.decisions.length) v c.precedence) ∧
    (∃ v, o["utilities"]? = some v ∧
      ArrayMatches (UtilityMatches c.vars.length c.pool.length) v c.utilities) ∧
    ∃ v, o["evidence"]? = some v ∧ EvidenceMatches c.vars.length v c.hard

theorem decodeBody_eq_ok {o : JsonObject} {c : Certificate} :
    decodeBody o = .ok c ↔ BodyMatches o c := by
  unfold decodeBody BodyMatches
  simp only [bind_eq_ok,
    get_eq_ok fun _ _ => decodeProvenance_eq_ok, get_eq_ok fun _ _ => decodeNumeric_eq_ok,
    get_eq_ok fun _ _ => decodeTolerances_eq_ok,
    getArr_eq_ok fun _ _ _ => decodePoolEntry_eq_ok,
    getArr_eq_ok fun _ _ _ => decodeVariable_eq_ok,
    getArr_eq_ok fun _ _ _ => decodeDecision_eq_ok,
    getArr_eq_ok fun _ _ _ => refOf_eq_ok,
    getArr_eq_ok fun _ _ _ => decodeMechanism_eq_ok,
    getArr_eq_ok fun _ _ _ => decodePrecedence_eq_ok,
    getArr_eq_ok fun _ _ _ => decodeUtility_eq_ok,
    get_eq_ok fun _ _ => decodeEvidence_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨prov, hprov, num, hnum, tol, htol, pool, hpool, vars, hvars, decs, hdecs, topo, htopo,
      dord, hdord, mechs, hmechs, prec, hprec, us, hus, hard, hhard, rfl⟩
    exact ⟨hprov, hnum, htol, hpool, hvars, hdecs, htopo, hdord, hmechs, hprec, hus, hhard⟩
  · rintro ⟨hprov, hnum, htol, hpool, hvars, hdecs, htopo, hdord, hmechs, hprec, hus, hhard⟩
    exact ⟨_, hprov, _, hnum, _, htol, _, hpool, _, hvars, _, hdecs, _, htopo, _, hdord, _, hmechs,
      _, hprec, _, hus, _, hhard, rfl⟩

/-- **The version-1 layout is the envelope plus `BodyMatches`.** -/
theorem certificateMatches_iff_body {j : Json} {c : Certificate} :
    CertificateMatches j c ↔ ∃ o, j = .obj o ∧ o.size = 14 ∧
      o["format"]? = some (.str certFormat) ∧ o["version"]? = some (natJson 1) ∧
      BodyMatches o c := by
  unfold CertificateMatches BodyMatches
  rfl

/-- The fifteen top-level keys of version 2. -/
def certKeysV2 : List String := certKeys ++ ["solution"]

/-- **The version-2 decoder**: exactly fifteen keys, the format, `"version": 2`, the twelve
version-1 fields (`decodeBody`) and the solution. -/
def decodeCertificateV2 (j : Json) : Except String (Certificate × Solution) := do
  let o ← object "certificate" 15 j
  let fmt ← get o "format" strOf
  require (fmt = certFormat) s!"format is \"{fmt}\", expected \"{certFormat}\""
  let ver ← get o "version" natOf
  require (ver = 2) s!"version is {ver}, expected 2"
  let c ← decodeBody o
  let s ← get o "solution" (decodeSolution c)
  pure (c, s)

/-- **The document is the version-2 certificate `(c, s)`.** -/
def CertificateV2Matches (j : Json) (c : Certificate) (s : Solution) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 15 ∧ o["format"]? = some (.str certFormat) ∧
    o["version"]? = some (natJson 2) ∧ BodyMatches o c ∧
    ∃ v, o["solution"]? = some v ∧ SolutionMatches c v s

/-- **Faithfulness of the version-2 decoder.** -/
theorem decodeCertificateV2_eq_ok {j : Json} {c : Certificate} {s : Solution} :
    decodeCertificateV2 j = .ok (c, s) ↔ CertificateV2Matches j c s := by
  unfold decodeCertificateV2 CertificateV2Matches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok,
    get_eq_ok fun _ _ => natOf_eq_ok, require_eq_ok, decodeBody_eq_ok,
    get_eq_ok fun _ _ => decodeSolution_eq_ok, pure_eq_ok, Prod.mk.injEq]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, fmt, ⟨_, hfmt, rfl⟩, _, rfl, ver, ⟨_, hver, rfl⟩, _, rfl, c', hb, s',
      hsol, rfl, rfl⟩
    exact ⟨o, rfl, hs, hfmt, hver, hb, hsol⟩
  · rintro ⟨o, rfl, hs, hfmt, hver, hb, hsol⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hfmt, rfl⟩, (), rfl, _, ⟨_, hver, rfl⟩, (), rfl, _, hb, _, hsol,
      rfl, rfl⟩

/-! ## One decoder for both versions -/

/-- **Both versions**: version 1 decodes with `decodeCertificate` and no solution, version 2 with
`decodeCertificateV2`; any other version is an error. -/
def decodeAnyCertificate (j : Json) : Except String (Certificate × Option Solution) := do
  let o ← anyObject "certificate" j
  let ver ← get o "version" natOf
  if ver = 1 then do
    let c ← decodeCertificate j
    pure (c, none)
  else if ver = 2 then do
    let cs ← decodeCertificateV2 j
    pure (cs.1, some cs.2)
  else throw s!"version is {ver}, expected 1 or 2"

theorem decodeCertificate_version {o : JsonObject} {c : Certificate}
    (h : decodeCertificate (.obj o) = .ok c) :
    o.size = 14 ∧ o["version"]? = some (natJson 1) := by
  obtain ⟨o', ho, hs, -, hv, -⟩ := decodeCertificate_eq_ok.1 h
  cases ho
  exact ⟨hs, hv⟩

theorem decodeCertificateV2_version {o : JsonObject} {c : Certificate} {s : Solution}
    (h : decodeCertificateV2 (.obj o) = .ok (c, s)) :
    o.size = 15 ∧ o["version"]? = some (natJson 2) := by
  obtain ⟨o', ho, hs, -, hv, -⟩ := decodeCertificateV2_eq_ok.1 h
  cases ho
  exact ⟨hs, hv⟩

theorem natJson_injective {m n : Nat} (h : natJson m = natJson n) : m = n := by
  unfold natJson at h
  simp only [Json.num.injEq, Lean.JsonNumber.mk.injEq, Nat.cast_inj, and_true] at h
  exact h

/-- **Version 1 decodes exactly as before**, with no solution. -/
theorem decodeAnyCertificate_v1 {j : Json} {c : Certificate} :
    decodeAnyCertificate j = .ok (c, none) ↔ decodeCertificate j = .ok c := by
  constructor
  · intro h
    unfold decodeAnyCertificate at h
    rw [bind_eq_ok] at h
    obtain ⟨o, ho, h⟩ := h
    rw [anyObject_eq_ok] at ho
    subst ho
    rw [bind_eq_ok] at h
    obtain ⟨ver, -, h⟩ := h
    split_ifs at h with h1 h2
    · rw [bind_eq_ok] at h
      obtain ⟨c', hc, h⟩ := h
      rw [pure_eq_ok, Prod.mk.injEq] at h
      rw [hc, h.1]
    · rw [bind_eq_ok] at h
      obtain ⟨cs, -, h⟩ := h
      rw [pure_eq_ok, Prod.mk.injEq] at h
      exact absurd h.2 (by simp)
  · intro h
    obtain ⟨o, ho, -, -, hv, -⟩ := decodeCertificate_eq_ok.1 h
    subst ho
    unfold decodeAnyCertificate
    rw [bind_eq_ok]
    refine ⟨o, anyObject_eq_ok.2 rfl, ?_⟩
    rw [bind_eq_ok]
    refine ⟨1, (get_eq_ok fun _ _ => natOf_eq_ok).2 ⟨_, hv, rfl⟩, ?_⟩
    rw [if_pos rfl, bind_eq_ok]
    exact ⟨c, h, rfl⟩

/-- **Version 2 decodes with its solution.** -/
theorem decodeAnyCertificate_v2 {j : Json} {c : Certificate} {s : Solution} :
    decodeAnyCertificate j = .ok (c, some s) ↔ decodeCertificateV2 j = .ok (c, s) := by
  constructor
  · intro h
    unfold decodeAnyCertificate at h
    rw [bind_eq_ok] at h
    obtain ⟨o, ho, h⟩ := h
    rw [anyObject_eq_ok] at ho
    subst ho
    rw [bind_eq_ok] at h
    obtain ⟨ver, -, h⟩ := h
    split_ifs at h with h1 h2
    · rw [bind_eq_ok] at h
      obtain ⟨c', -, h⟩ := h
      rw [pure_eq_ok, Prod.mk.injEq] at h
      exact absurd h.2 (by simp)
    · rw [bind_eq_ok] at h
      obtain ⟨cs, hcs, h⟩ := h
      rw [pure_eq_ok, Prod.mk.injEq, Option.some.injEq] at h
      rw [hcs, ← h.1, ← h.2]
  · intro h
    obtain ⟨o, ho, -, -, hv, -⟩ := decodeCertificateV2_eq_ok.1 h
    subst ho
    unfold decodeAnyCertificate
    rw [bind_eq_ok]
    refine ⟨o, anyObject_eq_ok.2 rfl, ?_⟩
    rw [bind_eq_ok]
    refine ⟨2, (get_eq_ok fun _ _ => natOf_eq_ok).2 ⟨_, hv, rfl⟩, ?_⟩
    rw [if_neg (by decide), if_pos rfl, bind_eq_ok]
    exact ⟨(c, s), h, rfl⟩

/-- Every successful decode is one of the two versions. -/
theorem decodeAnyCertificate_cases {j : Json} {c : Certificate} {s : Option Solution}
    (h : decodeAnyCertificate j = .ok (c, s)) :
    (s = none ∧ decodeCertificate j = .ok c) ∨
      ∃ s', s = some s' ∧ decodeCertificateV2 j = .ok (c, s') := by
  cases s with
  | none => exact Or.inl ⟨rfl, decodeAnyCertificate_v1.1 h⟩
  | some s' => exact Or.inr ⟨s', rfl, decodeAnyCertificate_v2.1 h⟩

/-- **Version 2 is not accepted with the version-1 key count.** -/
theorem decodeAnyCertificate_error_of_v2_with_v1_keys {o : JsonObject}
    (hv : o["version"]? = some (natJson 2)) (hs : o.size = 14) (c : Certificate)
    (s : Option Solution) : decodeAnyCertificate (.obj o) ≠ .ok (c, s) := fun h => by
  rcases decodeAnyCertificate_cases h with ⟨-, h1⟩ | ⟨s', -, h2⟩
  · have := (decodeCertificate_version h1).2
    rw [hv] at this
    exact absurd (natJson_injective (Option.some.inj this)) (by decide)
  · have := (decodeCertificateV2_version h2).1
    omega

/-- **Version 1 is not accepted with the version-2 key count.** -/
theorem decodeAnyCertificate_error_of_v1_with_v2_keys {o : JsonObject}
    (hv : o["version"]? = some (natJson 1)) (hs : o.size = 15) (c : Certificate)
    (s : Option Solution) : decodeAnyCertificate (.obj o) ≠ .ok (c, s) := fun h => by
  rcases decodeAnyCertificate_cases h with ⟨-, h1⟩ | ⟨s', -, h2⟩
  · have := (decodeCertificate_version h1).1
    omega
  · have := (decodeCertificateV2_version h2).2
    rw [hv] at this
    exact absurd (natJson_injective (Option.some.inj this)) (by decide)

/-! ## Well-formedness: references in range and coverage -/

/-- **A well-formed policy** of row `k`: the conditions the decoder checks. -/
structure PolicyRecord.WellFormed (c : Certificate) (k : Nat) (p : PolicyRecord) : Prop where
  decision : p.decision = k ∧ p.decision < c.decisions.length
  action : p.action < c.vars.length ∧
    (c.decisions[k]?).map DecisionEntry.action = some p.action
  axes : (∀ v ∈ p.axes, v < c.vars.length) ∧ infoVars c k = some p.axes
  scope : ∀ v ∈ p.scope, v < c.vars.length
  states : ∀ e ∈ p.entries, 1 ≤ e.action ∧ e.action ∈ stateIds c p.action
  scores : ∀ e ∈ p.entries, e.score.InRange ∧ e.score.IsSolutionNumber
  coverage : p.entries.map PolicyEntry.coords = lexCoords (p.axes.map (certDim c))

/-- **A well-formed solution** of the certificate `c`. -/
structure Solution.WellFormed (c : Certificate) (s : Solution) : Prop where
  backend : (∀ w, s.backend.atol = some w → w < 2 ^ 64) ∧ s.backend.constancy < 2 ^ 64 ∧
    s.backend.name = backendName
  conditioned : s.conditionedOn = conditionedOnHard
  order : ∀ v ∈ s.eliminationOrder, v < c.vars.length
  value : s.value.InRange ∧ s.value.IsSolutionNumber
  length : s.policies.length = c.decisions.length
  policies : ∀ (k : Nat) (hk : k < s.policies.length), s.policies[k].WellFormed c k

theorem PolicyMatches.wellFormed {c : Certificate} {k : Nat} {j : Json} {p : PolicyRecord}
    (h : PolicyMatches c k j p) : p.WellFormed c k := by
  obtain ⟨o, -, -, -, hdl, hdk, -, hal, hact, ⟨_, -, hax⟩, hinfo, ⟨_, -, hsc⟩, ⟨_, -, hes⟩,
    hcov⟩ := h
  refine ⟨⟨hdk, hdl⟩, ⟨hal, hact⟩, ⟨hax.forall fun _ _ _ hm => hm.2, hinfo⟩,
    hsc.forall fun _ _ _ hm => hm.2, ?_, ?_, hcov⟩
  · exact hes.forall fun _ _ _ hm => by
      obtain ⟨_, -, -, -, -, h1, hmem, -⟩ := hm
      exact ⟨h1, hmem⟩
  · exact hes.forall fun _ _ _ hm => by
      obtain ⟨_, -, -, -, -, -, -, _, -, hv, hn⟩ := hm
      exact ⟨hv.inRange, hn⟩

/-- **References in range.** A decoded solution names existing decisions, action variables and
action states; its axes are the decision's information slots; its elimination order names
existing variables. -/
theorem decodeSolution_wellFormed {c : Certificate} {j : Json} {s : Solution}
    (h : decodeSolution c j = .ok s) : s.WellFormed c := by
  obtain ⟨o, -, -, ⟨_, -, hb⟩, -, -, -, -, hcoe, -, ⟨_, -, heo⟩, ⟨_, -, hv, hvn⟩,
    ⟨_, -, hps⟩, hlen⟩ := decodeSolution_eq_ok.1 h
  obtain ⟨_, -, -, -, hname, -, -, ⟨_, -, hatol⟩, -, hk⟩ := hb
  refine ⟨⟨fun w hw => ?_, hk, hname⟩, hcoe, heo.forall fun _ _ _ hm => hm.2, ⟨hv.inRange, hvn⟩,
    hlen, fun k hk => ?_⟩
  · rw [hw] at hatol
    exact hatol.2
  · obtain ⟨_, -, -, hrows⟩ := hps
    obtain ⟨_, -, hm⟩ := hrows k hk
    exact hm.wellFormed

/-- The version-1 fields of a version-2 document have every reference in range (the proof of
`decodeCertificate_inRange`, from `BodyMatches`). -/
theorem BodyMatches.inRange {o : JsonObject} {c : Certificate} (hb : BodyMatches o c) :
    c.InRange := by
  obtain ⟨-, -, ⟨_, -, htol⟩, -, ⟨_, -, hvars⟩, ⟨_, -, hdecs⟩, ⟨_, -, htopo⟩,
    ⟨_, -, hdord⟩, ⟨_, -, hmechs⟩, ⟨_, -, hprec⟩, ⟨_, -, hus⟩, ⟨_, -, hev⟩⟩ := hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨_, -, -, -, h1, -, h2⟩ := htol
    exact ⟨h1, h2⟩
  · exact hvars.forall fun _ _ _ hm => by
      obtain ⟨_, -, -, -, -, -, -, hsr, ⟨_, -, hst⟩⟩ := hm
      exact ⟨hsr, hst.forall fun _ _ _ hs => by
        obtain ⟨_, -, -, -, h1, -⟩ := hs
        exact h1⟩
  · exact htopo.forall fun _ _ _ hm => hm.2
  · exact hdord.forall fun _ _ _ hm => hm.2
  · exact hmechs.forall fun _ _ _ hm => by
      obtain ⟨_, -, -, -, -, -, ht, -, hk, ⟨_, -, hp⟩, ⟨_, -, hcpt⟩, ⟨_, -, hf⟩⟩ := hm
      exact ⟨ht, hk, hp.forall fun _ _ _ hs => hs.inRange, hcpt.inRange, hf.inRange⟩
  · exact hdecs.forall fun _ _ _ hm => by
      obtain ⟨_, -, -, -, -, -, ha, ⟨_, -, hi⟩⟩ := hm
      exact ⟨ha, hi.forall fun _ _ _ hs => hs.inRange⟩
  · exact hprec.forall fun _ _ _ hm => by
      obtain ⟨_, -, -, -, -, he, -, hl⟩ := hm
      exact ⟨he, hl⟩
  · exact hus.forall fun _ _ _ hm => by
      obtain ⟨_, -, -, -, -, -, hu, ⟨_, -, hi⟩, ⟨_, -, ht⟩⟩ := hm
      exact ⟨hu, hi.forall fun _ _ _ hs => hs.inRange, ht.inRange⟩
  · obtain ⟨_, -, -, -, ⟨_, -, hh⟩⟩ := hev
    exact hh.forall fun _ _ _ hm => by
      obtain ⟨_, -, -, -, h1, -⟩ := hm
      exact h1

/-- **A decoded version-2 certificate** has every version-1 reference in range and a well-formed
solution. -/
theorem decodeCertificateV2_wellFormed {j : Json} {c : Certificate} {s : Solution}
    (h : decodeCertificateV2 j = .ok (c, s)) : c.InRange ∧ s.WellFormed c := by
  obtain ⟨o, -, -, -, -, hb, v, -, hsol⟩ := decodeCertificateV2_eq_ok.1 h
  exact ⟨hb.inRange, decodeSolution_wellFormed (decodeSolution_eq_ok.2 hsol)⟩

/-- `lexCoords` lists coordinate tuples in strictly increasing lexicographic order. -/
theorem lexCoords_pairwise_lex : ∀ ds : List Nat,
    (lexCoords ds).Pairwise (List.Lex (· < ·))
  | [] => by simp [lexCoords]
  | n :: ns => by
    simp only [lexCoords]
    rw [List.pairwise_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (lexCoords_pairwise_lex ns).imp fun h => List.Lex.cons h
    · refine List.Pairwise.imp ?_ (List.pairwise_lt_range (n := n))
      intro i j hij x hx y hy
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
      exact List.Lex.rel hij

theorem lex_lt_ne {a b : List Nat} (h : List.Lex (· < ·) a b) : a ≠ b := by
  rintro rfl
  exact List.lex_irrefl (fun x => Nat.lt_irrefl x) _ h

/-- `lexCoords` has no repeated tuple. -/
theorem lexCoords_nodup (ds : List Nat) : (lexCoords ds).Nodup :=
  (lexCoords_pairwise_lex ds).imp lex_lt_ne

/-- **Coverage.** The `at` lists of a decoded policy enumerate every configuration of the axes'
state counts exactly once, in lexicographic order with the rightmost coordinate fastest: they are
`lexCoords` of the extents, which lists exactly the in-range tuples (`mem_lexCoords`), without
repetition (`lexCoords_nodup`) and in strictly increasing lexicographic order
(`lexCoords_pairwise_lex`). -/
theorem decodeSolution_coverage {c : Certificate} {j : Json} {s : Solution}
    (h : decodeSolution c j = .ok s) (k : Nat) (hk : k < s.policies.length) :
    let p := s.policies[k]
    (∀ l, l ∈ p.entries.map PolicyEntry.coords ↔
        List.Forall₂ (· < ·) l (p.axes.map (certDim c))) ∧
      (p.entries.map PolicyEntry.coords).Nodup ∧
      (p.entries.map PolicyEntry.coords).Pairwise (List.Lex (· < ·)) := by
  intro p
  have hcov := ((decodeSolution_wellFormed h).policies k hk).coverage
  refine ⟨fun l => ?_, ?_, ?_⟩
  · rw [hcov, mem_lexCoords]
  · rw [hcov]
    exact lexCoords_nodup _
  · rw [hcov]
    exact lexCoords_pairwise_lex _

/-! ## Shapes and failures -/

/-- The JSON type each solution key must have. -/
def SolutionKeyShape : String → Json → Prop
  | "backend", v => ∃ o, v = .obj o
  | "value", v => ∃ o, v = .obj o
  | "exact_fallback", v => ∃ b, v = .bool b
  | "elimination_order", v => ∃ a, v = .arr a
  | "policies", v => ∃ a, v = .arr a
  | _, v => ∃ s, v = .str s

theorem ValueMatches.isObject {j : Json} {x : Value} (h : ValueMatches j x) : ∃ o, j = .obj o := by
  cases x with
  | f64 w =>
    obtain ⟨o, rfl, -⟩ := h
    exact ⟨o, rfl⟩
  | q n d =>
    obtain ⟨o, rfl, -⟩ := h
    exact ⟨o, rfl⟩
  | qf64 n d w =>
    obtain ⟨o, rfl, -⟩ := h
    exact ⟨o, rfl⟩

/-- A decoded solution object has every key, each of its JSON type. -/
theorem decodeSolution_shape {c : Certificate} {o : JsonObject} {s : Solution}
    (h : decodeSolution c (.obj o) = .ok s) :
    ∀ k ∈ solutionKeys, ∃ v, o[k]? = some v ∧ SolutionKeyShape k v := by
  obtain ⟨o', ho, -, ⟨vb, hb, hbm⟩, har, hda, hef, hco, -, hjv, ⟨ve, he, hem⟩, ⟨vv, hv, hvm, -⟩,
    ⟨vp, hp, hpm⟩, -⟩ := decodeSolution_eq_ok.1 h
  cases ho
  intro k hk
  simp only [solutionKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨ob, rfl, -⟩ := hbm
    exact ⟨_, hb, ob, rfl⟩
  · exact ⟨_, har, _, rfl⟩
  · exact ⟨_, hda, _, rfl⟩
  · exact ⟨_, hef, _, rfl⟩
  · exact ⟨_, hco, _, rfl⟩
  · exact ⟨_, hjv, _, rfl⟩
  · obtain ⟨a, rfl, -⟩ := hem
    exact ⟨_, he, a, rfl⟩
  · exact ⟨_, hv, hvm.isObject⟩
  · obtain ⟨a, rfl, -⟩ := hpm
    exact ⟨_, hp, a, rfl⟩

/-- **Failure: a missing solution key.** -/
theorem decodeSolution_error_of_missing_key {c : Certificate} {o : JsonObject} {k : String}
    (hk : k ∈ solutionKeys) (h : o[k]? = none) (s : Solution) :
    decodeSolution c (.obj o) ≠ .ok s := fun hd => by
  obtain ⟨v, hv, -⟩ := decodeSolution_shape hd k hk
  rw [h] at hv
  cases hv

/-- **Failure: an ill-typed solution key.** -/
theorem decodeSolution_error_of_ill_typed {c : Certificate} {o : JsonObject} {k : String}
    {v : Json} (hk : k ∈ solutionKeys) (h : o[k]? = some v) (hty : ¬ SolutionKeyShape k v)
    (s : Solution) : decodeSolution c (.obj o) ≠ .ok s := fun hd => by
  obtain ⟨v', hv', hs⟩ := decodeSolution_shape hd k hk
  rw [h, Option.some.injEq] at hv'
  subst hv'
  exact hty hs

/-- **Failure: a document whose solution is not an object.** -/
theorem decodeSolution_error_of_not_object {c : Certificate} {j : Json} (h : ∀ o, j ≠ .obj o)
    (s : Solution) : decodeSolution c j ≠ .ok s := fun hd => by
  obtain ⟨o, ho, -⟩ := decodeSolution_eq_ok.1 hd
  exact h o ho

/-- **Failure: a missing top-level key of version 2**, `"solution"` included. -/
theorem decodeCertificateV2_error_of_missing_key {o : JsonObject} {k : String}
    (hk : k ∈ certKeysV2) (h : o[k]? = none) (c : Certificate) (s : Solution) :
    decodeCertificateV2 (.obj o) ≠ .ok (c, s) := fun hd => by
  obtain ⟨o', ho, -, hf, hv, ⟨⟨_, hp, -⟩, ⟨_, hn, -⟩, ⟨_, ht, -⟩, ⟨_, hpool, -⟩, ⟨_, hvars, -⟩,
    ⟨_, hdecs, -⟩, ⟨_, htopo, -⟩, ⟨_, hdord, -⟩, ⟨_, hmechs, -⟩, ⟨_, hprec, -⟩, ⟨_, hus, -⟩,
    ⟨_, hev, -⟩⟩, ⟨_, hsol, -⟩⟩ := decodeCertificateV2_eq_ok.1 hd
  cases ho
  simp only [certKeysV2, certKeys, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> simp_all

/-! ## Encoding and the round trip -/

def encodeBackend (b : Backend) : Json :=
  Json.mkObj [("name", .str b.name), ("order", .str b.order), ("stable", .bool b.stable),
    ("atol_f64", encodeOptWord b.atol), ("constancy_atol_f64", .str (hexWord b.constancy))]

def encodePolicyEntry (e : PolicyEntry) : Json :=
  Json.mkObj [("at", encodeArray (fun _ c => natJson c) e.coords),
    ("action", .str (toString e.action)), ("score", encodeValue e.score)]

def encodePolicy (p : PolicyRecord) : Json :=
  Json.mkObj [("decision", .str (toString (p.decision + 1))),
    ("action", .str (toString (p.action + 1))),
    ("axes", encodeArray (fun _ i => .str (toString (i + 1))) p.axes),
    ("scope", encodeArray (fun _ i => .str (toString (i + 1))) p.scope),
    ("entries", encodeArray (fun _ => encodePolicyEntry) p.entries)]

/-- **The solution encoder.** -/
def encodeSolution (s : Solution) : Json :=
  Json.mkObj [("backend", encodeBackend s.backend),
    ("arithmetic", .str (arithmeticString s.arithmetic)), ("data", .str (dataString s.data)),
    ("exact_fallback", .bool s.exactFallback), ("conditioned_on", .str s.conditionedOn),
    ("julia_version", .str s.juliaVersion),
    ("elimination_order", encodeArray (fun _ i => .str (toString (i + 1))) s.eliminationOrder),
    ("value", encodeValue s.value),
    ("policies", encodeArray (fun _ => encodePolicy) s.policies)]

/-- **The version-2 encoder**: the version-1 fields of `encodeCertificate`, `"version": 2` and
the solution. -/
def encodeCertificateV2 (c : Certificate) (s : Solution) : Json :=
  Json.mkObj [("format", .str certFormat), ("version", natJson 2),
    ("provenance", encodeProvenance c.provenance), ("numeric", encodeNumeric c.numeric),
    ("runtime_tolerances", encodeTolerances c.tolerances),
    ("reference_pool", encodeArray encodePoolEntry c.pool),
    ("variables", encodeArray encodeVariable c.vars),
    ("topological_order", encodeArray (fun _ i => .str (toString (i + 1))) c.topological),
    ("decision_order", encodeArray (fun _ i => .str (toString (i + 1))) c.decisionOrder),
    ("mechanisms", encodeArray encodeMechanism c.mechanisms),
    ("decisions", encodeArray encodeDecision c.decisions),
    ("precedence", encodeArray encodePrecedence c.precedence),
    ("utilities", encodeArray encodeUtility c.utilities),
    ("evidence", encodeEvidence c.hard),
    ("solution", encodeSolution s)]

theorem optWordMatches_encode (a : Option Nat) (ha : ∀ w, a = some w → w < 2 ^ 64) :
    OptWordMatches (encodeOptWord a) a := by
  cases a with
  | none => rfl
  | some w => exact ⟨rfl, ha w rfl⟩

theorem backendMatches_encode (b : Backend) (hb : (∀ w, b.atol = some w → w < 2 ^ 64) ∧
    b.constancy < 2 ^ 64 ∧ b.name = backendName) : BackendMatches (encodeBackend b) b :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp), hb.2.2,
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp),
    ⟨_, mkObj_getElem? (by simp) (by simp), optWordMatches_encode _ hb.1⟩,
    mkObj_getElem? (by simp) (by simp), hb.2.1⟩

theorem policyEntryMatches_encode {states : List Nat} (e : PolicyEntry)
    (he : 1 ≤ e.action ∧ e.action ∈ states) (hs : e.score.InRange ∧ e.score.IsSolutionNumber) :
    PolicyEntryMatches states (encodePolicyEntry e) e :=
  ⟨_, rfl, mkObj_size (by simp),
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := fun _ c => natJson c) fun _ _ => rfl⟩,
    mkObj_getElem? (by simp) (by simp), he.1, he.2,
    ⟨_, mkObj_getElem? (by simp) (by simp), valueMatches_encode _ hs.1, hs.2⟩⟩

theorem varRefs_encode {nv : Nat} (l : List Nat) (hl : ∀ v ∈ l, v < nv) :
    ArrayMatches (fun _ => VarRef nv) (encodeArray (fun _ i => .str (toString (i + 1))) l) l :=
  arrayMatches_encode (enc := fun _ i => .str (toString (i + 1))) fun _ hk =>
    ⟨rfl, hl _ (getElem_mem' hk)⟩

theorem policyMatches_encode {c : Certificate} {k : Nat} (p : PolicyRecord)
    (hp : p.WellFormed c k) : PolicyMatches c k (encodePolicy p) p :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp), hp.decision.2,
    hp.decision.1, mkObj_getElem? (by simp) (by simp), hp.action.1, hp.action.2,
    ⟨_, mkObj_getElem? (by simp) (by simp), varRefs_encode _ hp.axes.1⟩, hp.axes.2,
    ⟨_, mkObj_getElem? (by simp) (by simp), varRefs_encode _ hp.scope⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := fun _ => encodePolicyEntry) fun _ hk =>
        policyEntryMatches_encode _ (hp.states _ (getElem_mem' hk))
          (hp.scores _ (getElem_mem' hk))⟩,
    hp.coverage⟩

theorem solutionMatches_encode {c : Certificate} (s : Solution) (hs : s.WellFormed c) :
    SolutionMatches c (encodeSolution s) s :=
  ⟨_, rfl, mkObj_size (by simp),
    ⟨_, mkObj_getElem? (by simp) (by simp), backendMatches_encode _ hs.backend⟩,
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp), hs.conditioned,
    mkObj_getElem? (by simp) (by simp),
    ⟨_, mkObj_getElem? (by simp) (by simp), varRefs_encode _ hs.order⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp), valueMatches_encode _ hs.value.1, hs.value.2⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := fun _ => encodePolicy) fun k hk =>
        policyMatches_encode _ (hs.policies k hk)⟩,
    hs.length⟩

/-- **Round trip of the solution.** -/
theorem decodeSolution_encode {c : Certificate} (s : Solution) (hs : s.WellFormed c) :
    decodeSolution c (encodeSolution s) = .ok s :=
  decodeSolution_eq_ok.2 (solutionMatches_encode s hs)

/-- **Round trip of the version-2 certificate.** -/
theorem decodeCertificateV2_encode (c : Certificate) (s : Solution) (hc : c.InRange)
    (hs : s.WellFormed c) : decodeCertificateV2 (encodeCertificateV2 c s) = .ok (c, s) :=
  decodeCertificateV2_eq_ok.2 ⟨_, rfl, mkObj_size (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp),
    ⟨⟨_, mkObj_getElem? (by simp) (by simp), provenanceMatches_encode _⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp), numericMatches_encode _⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp), tolerancesMatches_encode _ hc.tolerances⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := encodePoolEntry) fun k _ => poolMatches_encode k _⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := encodeVariable) fun k hk =>
        variableMatches_encode k _ (hc.vars _ (getElem_mem' hk))⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := encodeDecision) fun k hk =>
        decisionMatches_encode k _ (hc.decisions _ (getElem_mem' hk))⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := fun _ i => .str (toString (i + 1))) fun k hk =>
        ⟨rfl, hc.topological _ (getElem_mem' hk)⟩⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := fun _ i => .str (toString (i + 1))) fun k hk =>
        ⟨rfl, hc.decisionOrder _ (getElem_mem' hk)⟩⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := encodeMechanism) fun k hk =>
        mechanismMatches_encode k _ (hc.mechanisms _ (getElem_mem' hk))⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := encodePrecedence) fun k hk =>
        precedenceMatches_encode k _ (hc.precedence _ (getElem_mem' hk))⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := encodeUtility) fun k hk =>
        utilityMatches_encode k _ (hc.utilities _ (getElem_mem' hk))⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp), evidenceMatches_encode _ hc.hard⟩⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp), solutionMatches_encode _ hs⟩⟩

end InfluenceDiagramsProofs.DVECertificate
