import InfluenceDiagramsProofs.Finite.DVE.JsonRecords
import BayesianNetworksProofs.Numeric.Binary64

/-!
# Decoding the DVE model certificate

`export_dve_certificate` (InfluenceDiagrams.jl, `src/certificates.jl`) returns a dictionary that
`JSON3.write` serializes as one JSON object with fourteen keys. This module defines Lean records
for exactly that layout, a decoder from a parsed `Lean.Json` tree and an encoder, and proves the
decoder faithful.

**The layout** (confirmed on the certificates Julia writes for the umbrella, oil-wildcatter and
grazing models):

* `"format"`: the string `"ecorecipes.dve-certificate"`; `"version"`: the integer `1`;
* `"provenance"`: five strings (`implementation_manifest_sha256`, `model_name`, `exporter`,
  `origin`, `exact_source`); `"numeric"`: `mode` (string), `runtime_bits` (boolean),
  `normalization` (string); `"runtime_tolerances"`: two binary64 words
  (`kernel_normalization_f64`, `decision_probability_f64`);
* `"reference_pool"`: rows `{code, reference}` with `code` the zero-based row number and
  `reference` a `KernelRef` object;
* `"variables"`: rows `{id, name, kind, space_ref, states}`, `kind` `"chance"` or `"decision"`,
  `space_ref` a pool code, `states` rows `{id, position, label}` in `state_position` order;
* `"topological_order"`, `"decision_order"`: arrays of variable and decision IDs;
* `"mechanisms"`: rows `{id, name, target, kernel_ref, parents, cpt, factor}`; `parents` are
  slots `{id, position, variable}` in `input_position` order; `cpt` and `factor` are tables
  `{axes, entries}`, `axes` variable IDs, `entries` rows `{at, value}` with zero-based
  coordinates;
* `"decisions"`: rows `{id, name, action, information}` (information slots);
  `"precedence"`: rows `{id, earlier, later}`;
* `"utilities"`: rows `{id, name, utility_ref, inputs, table}`;
* `"evidence"`: `{hard, likelihood}`, `hard` rows `{variable, state_index}`, `likelihood` `null`.

Part IDs are decimal strings. A value is `{"f64": word}` (mode `binary64_exact`), or
`{"q": {"num", "den"}, "f64": word}` / `{"q": …}` (mode `rational_exact` with or without the
runtime bits); a word is the 16-digit lowercase hexadecimal string of a `UInt64`, and a rational
is the decimal strings of Julia's `numerator` and `denominator`.

**Conventions.** The `id` of a row of `variables`, `mechanisms`, `decisions`, `precedence` and
`utilities` must be its one-based row number, as for an ACSet part (Julia sorts the parts by ID);
it is checked and not stored. A reference to a variable or decision is decoded to its zero-based
index and must be in range; a pool code must be below the pool size. State and slot IDs (global
part IDs) are stored as written and must be positive. Coordinates and positions are stored as
written. Decimal strings must be canonical (`toString n`, so no sign or leading zero), words
exactly sixteen lowercase hexadecimal digits.

**Results.** `decodeCertificate_eq_ok`: decoding succeeds with `c` exactly when the document is
`c`'s layout key for key and row for row (`CertificateMatches`); `decodeCertificate_encode`: the
encoded certificate decodes back (for in-range records); `decodeCertificate_inRange`: every
reference of a decoded certificate is in range, so a document with a reference out of range fails
to decode; `decodeCertificate_error_of_missing_key`: a missing top-level key fails. Never a
default: every stored field is read from the document (`CertificateMatches`).

Trusted, not proved: `Lean.Json.parse`, Julia's `export_dve_certificate` and `JSON3.write`.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVECertificate

open Lean (Json)
open BayesianNetworksProofs.Raw

/-! ## Decimal, integer and hexadecimal strings -/

/-- The value of a string of decimal digits. -/
def digitsValue (s : String) : Nat := Nat.ofDigitChars 10 s.toList 0

theorem digitsValue_toString (n : Nat) : digitsValue (toString n) = n := by
  simp [digitsValue]

/-- A canonical decimal string, `toString n`. -/
def parseNat? (s : String) : Option Nat :=
  if toString (digitsValue s) = s then some (digitsValue s) else none

theorem parseNat?_eq_some {s : String} {n : Nat} : parseNat? s = some n ↔ s = toString n := by
  unfold parseNat?
  constructor
  · intro h
    by_cases hs : toString (digitsValue s) = s
    · rw [if_pos hs, Option.some.injEq] at h
      subst h
      exact hs.symm
    · rw [if_neg hs] at h
      cases h
  · rintro rfl
    rw [digitsValue_toString, if_pos rfl]

/-- Julia's `string` of an integer (`Int.repr`): digits, after a minus sign when negative. -/
def intString : Int → String
  | .ofNat n => toString n
  | .negSucc n => "-" ++ toString (n + 1)

/-- The integer a decimal string with an optional leading minus sign denotes. -/
def intCandidate (s : String) : Int :=
  match s.toList with
  | '-' :: cs => -((Nat.ofDigitChars 10 cs 0 : Nat) : Int)
  | _ => (digitsValue s : Int)

theorem intCandidate_intString (i : Int) : intCandidate (intString i) = i := by
  cases i with
  | ofNat n =>
    have hl : (toString n).toList = Nat.toDigits 10 n := by simp
    obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (b := 10) (n := n))
    have hdig : c.isDigit = true :=
      Nat.isDigit_of_mem_toDigits (by decide) (by decide) (hc ▸ List.mem_cons_self ..)
    have hne : c ≠ '-' := by
      rintro rfl
      exact absurd hdig (by decide)
    unfold intCandidate intString
    rw [hl, hc]
    split
    · rename_i cs' h
      exact absurd (List.cons.inj h).1 hne
    · simp [digitsValue]
  | negSucc n =>
    have hl : ("-" ++ toString (n + 1)).toList = '-' :: Nat.toDigits 10 (n + 1) := by simp
    unfold intCandidate intString
    rw [hl]
    simp only [Nat.ofDigitChars_ten_toDigits]
    omega

/-- A canonical integer string, `intString i`. -/
def parseInt? (s : String) : Option Int :=
  if intString (intCandidate s) = s then some (intCandidate s) else none

theorem parseInt?_eq_some {s : String} {i : Int} : parseInt? s = some i ↔ s = intString i := by
  unfold parseInt?
  constructor
  · intro h
    by_cases hs : intString (intCandidate s) = s
    · rw [if_pos hs, Option.some.injEq] at h
      subst h
      exact hs.symm
    · rw [if_neg hs] at h
      cases h
  · rintro rfl
    rw [intCandidate_intString, if_pos rfl]

/-- The lowercase hexadecimal digit of `d < 16`. -/
def hexChar (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- The value of a hexadecimal digit (meaningful on `0-9`, `a-f`). -/
def hexVal (c : Char) : Nat := if c.toNat < 58 then c.toNat - 48 else c.toNat - 87

theorem hexVal_hexChar (d : Nat) (hd : d < 16) : hexVal (hexChar d) = d := by
  have h : ∀ e : Fin 16, hexVal (hexChar e.val) = e.val := by decide
  exact h ⟨d, hd⟩

/-- The last `k` hexadecimal digits of `w`, most significant first. -/
def hexDigits : Nat → Nat → List Char
  | 0, _ => []
  | k + 1, w => hexDigits k (w / 16) ++ [hexChar (w % 16)]

/-- The value of a list of hexadecimal digits. -/
def hexValue (l : List Char) : Nat := l.foldl (fun acc c => 16 * acc + hexVal c) 0

theorem hexValue_hexDigits (k w : Nat) : hexValue (hexDigits k w) = w % 16 ^ k := by
  induction k generalizing w with
  | zero => simp [hexDigits, hexValue, Nat.mod_one]
  | succ k ih =>
    have ih' := ih (w / 16)
    simp only [hexValue] at ih' ⊢
    simp only [hexDigits, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih', hexVal_hexChar _ (Nat.mod_lt _ (by decide)), Nat.pow_succ', Nat.mod_mul,
      Nat.add_comm]

/-- Julia's `string(word; base = 16, pad = 16)`: sixteen lowercase hexadecimal digits. -/
def hexWord (w : Nat) : String := String.ofList (hexDigits 16 w)

/-- A binary64 word: exactly `hexWord w` for some `w < 2 ^ 64`. -/
def parseWord? (s : String) : Option Nat :=
  if hexValue s.toList < 2 ^ 64 ∧ hexWord (hexValue s.toList) = s then some (hexValue s.toList)
  else none

theorem parseWord?_eq_some {s : String} {w : Nat} :
    parseWord? s = some w ↔ s = hexWord w ∧ w < 2 ^ 64 := by
  unfold parseWord?
  constructor
  · intro h
    by_cases hs : hexValue s.toList < 2 ^ 64 ∧ hexWord (hexValue s.toList) = s
    · rw [if_pos hs, Option.some.injEq] at h
      subst h
      exact ⟨hs.2.symm, hs.1⟩
    · rw [if_neg hs] at h
      cases h
  · rintro ⟨rfl, hw⟩
    have hv : hexValue (hexWord w).toList = w := by
      rw [hexWord, String.toList_ofList, hexValue_hexDigits, Nat.mod_eq_of_lt]
      calc w < 2 ^ 64 := hw
        _ = 16 ^ 16 := by norm_num
    rw [hv, if_pos ⟨hw, rfl⟩]

/-! ## Leaf decoders -/

theorem withError_ne_ok {α : Type} {e : String} {b : α} : (Except.error e : Except String α) ≠ .ok b :=
  fun h => by cases h

/-- Prefix an error message with its location. -/
def withCtx {α : Type} (ctx : String) : Except String α → Except String α
  | .ok x => .ok x
  | .error e => .error s!"{ctx} > {e}"

@[simp] theorem withCtx_eq_ok {α : Type} {ctx : String} {x : Except String α} {a : α} :
    withCtx ctx x = .ok a ↔ x = .ok a := by
  cases x <;> simp [withCtx]

def strOf : Json → Except String String
  | .str s => .ok s
  | _ => .error "expected a string"

theorem strOf_eq_ok {j : Json} {s : String} : strOf j = .ok s ↔ j = .str s := by
  cases j <;> simp [strOf]

def natOf (j : Json) : Except String Nat :=
  match jsonNat? j with
  | some n => .ok n
  | none => .error "expected a nonnegative integer"

theorem natOf_eq_ok {j : Json} {n : Nat} : natOf j = .ok n ↔ j = natJson n := by
  unfold natOf
  constructor
  · intro h
    split at h
    · rename_i m hm
      cases h
      exact jsonNat?_eq_some.1 hm
    · cases h
  · rintro rfl
    rfl

def boolOf : Json → Except String Bool
  | .bool b => .ok b
  | _ => .error "expected a boolean"

theorem boolOf_eq_ok {j : Json} {b : Bool} : boolOf j = .ok b ↔ j = .bool b := by
  cases j <;> simp [boolOf]

def nullOf : Json → Except String Unit
  | .null => .ok ()
  | _ => .error "expected null"

theorem nullOf_eq_ok {j : Json} {u : Unit} : nullOf j = .ok u ↔ j = .null := by
  cases j <;> simp [nullOf]

/-- A source part ID stored as written: a canonical positive decimal string. -/
def idOf (j : Json) : Except String Nat := do
  let s ← strOf j
  match parseNat? s with
  | some e => if 1 ≤ e then pure e else throw s!"the ID \"{s}\" is not positive"
  | none => throw s!"\"{s}\" is not a decimal ID"

theorem idOf_eq_ok {j : Json} {e : Nat} : idOf j = .ok e ↔ j = .str (toString e) ∧ 1 ≤ e := by
  unfold idOf
  rw [bind_eq_ok]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [strOf_eq_ok] at hs
    subst hs
    split at h
    · rename_i e' he
      rw [parseNat?_eq_some] at he
      split_ifs at h with h1
      rw [pure_eq_ok] at h
      subst h
      exact ⟨congrArg Json.str he, h1⟩
    · exact absurd h throw_ne_ok
  · rintro ⟨rfl, he⟩
    refine ⟨_, strOf_eq_ok.2 rfl, ?_⟩
    rw [show parseNat? (toString e) = some e from parseNat?_eq_some.2 rfl]
    simp only [if_pos he]
    rfl

/-- A reference to a row of a table of `n` rows: the decimal string of its one-based ID, decoded
to the zero-based index. -/
def refOf (n : Nat) (j : Json) : Except String Nat := do
  let s ← strOf j
  match parseNat? s with
  | some e => if 1 ≤ e ∧ e ≤ n then pure (e - 1) else throw s!"the ID \"{s}\" is not in 1..{n}"
  | none => throw s!"\"{s}\" is not a decimal ID"

theorem refOf_eq_ok {n : Nat} {j : Json} {i : Nat} :
    refOf n j = .ok i ↔ j = .str (toString (i + 1)) ∧ i < n := by
  unfold refOf
  rw [bind_eq_ok]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [strOf_eq_ok] at hs
    subst hs
    split at h
    · rename_i e he
      rw [parseNat?_eq_some] at he
      split_ifs at h with h1
      rw [pure_eq_ok] at h
      subst h
      refine ⟨?_, by omega⟩
      rw [he, Nat.sub_add_cancel h1.1]
    · exact absurd h throw_ne_ok
  · rintro ⟨rfl, hi⟩
    refine ⟨_, strOf_eq_ok.2 rfl, ?_⟩
    rw [show parseNat? (toString (i + 1)) = some (i + 1) from parseNat?_eq_some.2 rfl]
    simp only [if_pos (show 1 ≤ i + 1 ∧ i + 1 ≤ n by omega), Nat.add_sub_cancel]
    rfl

/-- A code into a pool of `n` entries: a JSON integer below `n`. -/
def codeOf (n : Nat) (j : Json) : Except String Nat := do
  let c ← natOf j
  if c < n then pure c else throw s!"the code {c} is not below {n}"

theorem codeOf_eq_ok {n : Nat} {j : Json} {c : Nat} :
    codeOf n j = .ok c ↔ j = natJson c ∧ c < n := by
  unfold codeOf
  rw [bind_eq_ok]
  constructor
  · rintro ⟨c', hc, h⟩
    rw [natOf_eq_ok] at hc
    split_ifs at h with h1
    rw [pure_eq_ok] at h
    subst h
    exact ⟨hc, h1⟩
  · rintro ⟨rfl, hc⟩
    exact ⟨c, natOf_eq_ok.2 rfl, by rw [if_pos hc]; rfl⟩

/-- A binary64 word: sixteen lowercase hexadecimal digits. -/
def wordOf (j : Json) : Except String Nat := do
  let s ← strOf j
  match parseWord? s with
  | some w => pure w
  | none => throw s!"\"{s}\" is not a 16-digit lowercase hexadecimal word"

theorem wordOf_eq_ok {j : Json} {w : Nat} :
    wordOf j = .ok w ↔ j = .str (hexWord w) ∧ w < 2 ^ 64 := by
  unfold wordOf
  rw [bind_eq_ok]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [strOf_eq_ok] at hs
    subst hs
    split at h
    · rename_i w' hw
      rw [pure_eq_ok] at h
      subst h
      obtain ⟨rfl, hlt⟩ := parseWord?_eq_some.1 hw
      exact ⟨rfl, hlt⟩
    · exact absurd h throw_ne_ok
  · rintro ⟨rfl, hw⟩
    refine ⟨_, strOf_eq_ok.2 rfl, ?_⟩
    rw [show parseWord? (hexWord w) = some w from parseWord?_eq_some.2 ⟨rfl, hw⟩]
    rfl

/-- An integer: Julia's decimal string of a `BigInt`. -/
def intOf (j : Json) : Except String Int := do
  let s ← strOf j
  match parseInt? s with
  | some i => pure i
  | none => throw s!"\"{s}\" is not a decimal integer"

theorem intOf_eq_ok {j : Json} {i : Int} : intOf j = .ok i ↔ j = .str (intString i) := by
  unfold intOf
  rw [bind_eq_ok]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [strOf_eq_ok] at hs
    subst hs
    split at h
    · rename_i i' hi
      rw [pure_eq_ok] at h
      subst h
      rw [parseInt?_eq_some.1 hi]
    · exact absurd h throw_ne_ok
  · rintro rfl
    refine ⟨_, strOf_eq_ok.2 rfl, ?_⟩
    rw [show parseInt? (intString i) = some i from parseInt?_eq_some.2 rfl]
    rfl

/-! ## Keys and arrays -/

/-- The value of key `key`, decoded by `dec`; errors name the key. -/
def get {α : Type} (o : JsonObject) (key : String) (dec : Json → Except String α) :
    Except String α :=
  match o[key]? with
  | some v => withCtx key (dec v)
  | none => .error s!"missing key \"{key}\""

theorem get_eq_ok {α : Type} {o : JsonObject} {key : String} {dec : Json → Except String α}
    {M : Json → α → Prop} (hdec : ∀ v x, dec v = .ok x ↔ M v x) {x : α} :
    get o key dec = .ok x ↔ ∃ v, o[key]? = some v ∧ M v x := by
  unfold get
  split
  · rename_i v hv
    rw [withCtx_eq_ok, hdec]
    constructor
    · intro h
      exact ⟨v, hv, h⟩
    · rintro ⟨v', hv', h⟩
      rw [hv, Option.some.injEq] at hv'
      subst hv'
      exact h
  · rename_i hv
    constructor
    · intro h
      cases h
    · rintro ⟨v, hv', -⟩
      rw [hv] at hv'
      cases hv'

/-- An array whose element `i` is decoded by `dec i`; errors name the index. -/
def decodeArray {α : Type} (dec : Nat → Json → Except String α) : Json → Except String (List α)
  | .arr a => do
    let l ← decodeList a.size (fun i => withCtx s!"[{i.val}]" (dec i.val a[i]))
    pure l.val
  | _ => .error "expected an array"

/-- The JSON value is an array of exactly `l.length` elements, element `i` matching `l[i]`. -/
def ArrayMatches {α : Type} (M : Nat → Json → α → Prop) (j : Json) (l : List α) : Prop :=
  ∃ a : Array Json, j = .arr a ∧ a.size = l.length ∧
    ∀ (i : Nat) (hi : i < l.length), ∃ x, a[i]? = some x ∧ M i x l[i]

theorem decodeArray_eq_ok {α : Type} {dec : Nat → Json → Except String α}
    {M : Nat → Json → α → Prop} (hdec : ∀ k v x, dec k v = .ok x ↔ M k v x) {j : Json}
    {l : List α} : decodeArray dec j = .ok l ↔ ArrayMatches M j l := by
  cases j with
  | arr a =>
    simp only [decodeArray, bind_eq_ok, pure_eq_ok]
    constructor
    · rintro ⟨⟨l', hl'⟩, hd, rfl⟩
      rw [decodeList_eq_ok] at hd
      refine ⟨a, rfl, hl'.symm, fun i hi => ?_⟩
      have hia : i < a.size := by rw [← hl']; exact hi
      refine ⟨a[i], by simp [hia], ?_⟩
      have := hd ⟨i, hia⟩
      rw [withCtx_eq_ok, hdec] at this
      simpa using this
    · rintro ⟨a', ha', hs, hrows⟩
      cases ha'
      refine ⟨⟨l, hs.symm⟩, ?_, rfl⟩
      rw [decodeList_eq_ok]
      intro i
      obtain ⟨x, hx, hm⟩ := hrows i.val (by omega)
      rw [Array.getElem?_eq_getElem (by omega), Option.some.injEq] at hx
      subst hx
      rw [withCtx_eq_ok, hdec]
      exact hm
  | _ => simp [decodeArray, ArrayMatches]

def encodeArray {α : Type} (enc : Nat → α → Json) (l : List α) : Json :=
  .arr (Array.ofFn fun i : Fin l.length => enc i.val l[i])

theorem arrayMatches_encode {α : Type} {M : Nat → Json → α → Prop} {enc : Nat → α → Json}
    {l : List α} (henc : ∀ (k : Nat) (hk : k < l.length), M k (enc k l[k]) l[k]) :
    ArrayMatches M (encodeArray enc l) l :=
  ⟨_, rfl, Array.size_ofFn, fun i hi => ⟨_, by simp [hi], henc i hi⟩⟩

theorem ArrayMatches.forall {α : Type} {M : Nat → Json → α → Prop} {j : Json} {l : List α}
    (h : ArrayMatches M j l) {P : α → Prop} (hP : ∀ k v x, M k v x → P x) : ∀ x ∈ l, P x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨_, _, _, hrows⟩ := h
  obtain ⟨v, -, hm⟩ := hrows i hi
  exact hP _ _ _ hm

def getArr {α : Type} (o : JsonObject) (key : String) (dec : Nat → Json → Except String α) :
    Except String (List α) :=
  get o key (decodeArray dec)

theorem getArr_eq_ok {α : Type} {o : JsonObject} {key : String}
    {dec : Nat → Json → Except String α} {M : Nat → Json → α → Prop}
    (hdec : ∀ k v x, dec k v = .ok x ↔ M k v x) {l : List α} :
    getArr o key dec = .ok l ↔ ∃ v, o[key]? = some v ∧ ArrayMatches M v l :=
  get_eq_ok fun _ _ => decodeArray_eq_ok hdec

/-- The `"id"` of row `k` is `toString (k + 1)`. -/
def rowId (o : JsonObject) (k : Nat) : Except String Unit := do
  let s ← get o "id" strOf
  if s = toString (k + 1) then pure () else throw s!"the id is \"{s}\", expected \"{k + 1}\""

theorem rowId_eq_ok {o : JsonObject} {k : Nat} {u : Unit} :
    rowId o k = .ok u ↔ o["id"]? = some (.str (toString (k + 1))) := by
  unfold rowId
  simp only [bind_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok]
  constructor
  · rintro ⟨s, ⟨v, hv, rfl⟩, h⟩
    split_ifs at h with h1
    rw [hv, h1]
  · intro h
    exact ⟨_, ⟨_, h, rfl⟩, by rw [if_pos rfl]; rfl⟩

/-! ## Values and tables -/

/-- A numeric cell: the binary64 word, the exact rational, or both. -/
inductive Value where
  | f64 (w : Nat)
  | q (num : Int) (den : Nat)
  | qf64 (num : Int) (den : Nat) (w : Nat)
  deriving DecidableEq

def decodeRational (j : Json) : Except String (Int × Nat) := do
  let o ← object "rational" 2 j
  let n ← get o "num" intOf
  let d ← get o "den" idOf
  pure (n, d)

def RationalMatches (j : Json) (n : Int) (d : Nat) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 2 ∧ o["num"]? = some (.str (intString n)) ∧
    o["den"]? = some (.str (toString d)) ∧ 1 ≤ d

theorem decodeRational_eq_ok {j : Json} {n : Int} {d : Nat} :
    decodeRational j = .ok (n, d) ↔ RationalMatches j n d := by
  unfold decodeRational RationalMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => intOf_eq_ok,
    get_eq_ok fun _ _ => idOf_eq_ok, pure_eq_ok, Prod.mk.injEq]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, n', ⟨_, hn, rfl⟩, d', ⟨_, hd, rfl, h1⟩, rfl, rfl⟩
    exact ⟨o, rfl, hs, hn, hd, h1⟩
  · rintro ⟨o, rfl, hs, hn, hd, h1⟩
    exact ⟨o, ⟨rfl, hs⟩, n, ⟨_, hn, rfl⟩, d, ⟨_, hd, rfl, h1⟩, rfl, rfl⟩

def decodeValue (j : Json) : Except String Value := do
  let o ← anyObject "value" j
  match o["q"]?, o["f64"]? with
  | some qj, some fj => do
    checkSize "value" o 2
    let nd ← withCtx "q" (decodeRational qj)
    let w ← withCtx "f64" (wordOf fj)
    pure (.qf64 nd.1 nd.2 w)
  | some qj, none => do
    checkSize "value" o 1
    let nd ← withCtx "q" (decodeRational qj)
    pure (.q nd.1 nd.2)
  | none, some fj => do
    checkSize "value" o 1
    let w ← withCtx "f64" (wordOf fj)
    pure (.f64 w)
  | none, none => .error "value: expected the key \"f64\" or \"q\""

def ValueMatches (j : Json) : Value → Prop
  | .f64 w => ∃ o, j = .obj o ∧ o.size = 1 ∧ o["q"]? = none ∧
      o["f64"]? = some (.str (hexWord w)) ∧ w < 2 ^ 64
  | .q n d => ∃ o, j = .obj o ∧ o.size = 1 ∧ (∃ v, o["q"]? = some v ∧ RationalMatches v n d) ∧
      o["f64"]? = none
  | .qf64 n d w => ∃ o, j = .obj o ∧ o.size = 2 ∧
      (∃ v, o["q"]? = some v ∧ RationalMatches v n d) ∧ o["f64"]? = some (.str (hexWord w)) ∧
      w < 2 ^ 64

theorem decodeValue_eq_ok {j : Json} {x : Value} : decodeValue j = .ok x ↔ ValueMatches j x := by
  unfold decodeValue
  rw [bind_eq_ok]
  constructor
  · rintro ⟨o, ho, h⟩
    rw [anyObject_eq_ok] at ho
    subst ho
    split at h
    · rename_i qj fj hq hf
      simp only [bind_eq_ok, checkSize_eq_ok, withCtx_eq_ok, wordOf_eq_ok, pure_eq_ok] at h
      obtain ⟨_, hs, ⟨n, d⟩, hnd, w, ⟨rfl, hw⟩, rfl⟩ := h
      exact ⟨o, rfl, hs, ⟨qj, hq, decodeRational_eq_ok.1 hnd⟩, hf, hw⟩
    · rename_i qj hq hf
      simp only [bind_eq_ok, checkSize_eq_ok, withCtx_eq_ok, pure_eq_ok] at h
      obtain ⟨_, hs, ⟨n, d⟩, hnd, rfl⟩ := h
      exact ⟨o, rfl, hs, ⟨qj, hq, decodeRational_eq_ok.1 hnd⟩, hf⟩
    · rename_i fj hq hf
      simp only [bind_eq_ok, checkSize_eq_ok, withCtx_eq_ok, wordOf_eq_ok, pure_eq_ok] at h
      obtain ⟨_, hs, w, ⟨rfl, hw⟩, rfl⟩ := h
      exact ⟨o, rfl, hs, hq, hf, hw⟩
    · exact absurd h withError_ne_ok
  · intro h
    cases x with
    | f64 w =>
      obtain ⟨o, rfl, hs, hq, hf, hw⟩ := h
      refine ⟨o, rfl, ?_⟩
      rw [hq, hf]
      simp only [bind_eq_ok, checkSize_eq_ok, withCtx_eq_ok, wordOf_eq_ok, pure_eq_ok]
      exact ⟨(), hs, w, ⟨rfl, hw⟩, rfl⟩
    | q n d =>
      obtain ⟨o, rfl, hs, ⟨qj, hq, hr⟩, hf⟩ := h
      refine ⟨o, rfl, ?_⟩
      rw [hq, hf]
      simp only [bind_eq_ok, checkSize_eq_ok, withCtx_eq_ok, pure_eq_ok]
      exact ⟨(), hs, (n, d), decodeRational_eq_ok.2 hr, rfl⟩
    | qf64 n d w =>
      obtain ⟨o, rfl, hs, ⟨qj, hq, hr⟩, hf, hw⟩ := h
      refine ⟨o, rfl, ?_⟩
      rw [hq, hf]
      simp only [bind_eq_ok, checkSize_eq_ok, withCtx_eq_ok, wordOf_eq_ok, pure_eq_ok]
      exact ⟨(), hs, (n, d), decodeRational_eq_ok.2 hr, w, ⟨rfl, hw⟩, rfl⟩

/-- One table cell: zero-based coordinates (`"at"`) and the value. -/
structure Entry where
  coords : List Nat
  value : Value
  deriving DecidableEq

def decodeEntry (j : Json) : Except String Entry := do
  let o ← object "entry" 2 j
  let c ← getArr o "at" (fun _ => natOf)
  let v ← get o "value" decodeValue
  pure ⟨c, v⟩

def EntryMatches (j : Json) (e : Entry) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 2 ∧
    (∃ v, o["at"]? = some v ∧ ArrayMatches (fun _ x c => x = natJson c) v e.coords) ∧
    ∃ v, o["value"]? = some v ∧ ValueMatches v e.value

theorem decodeEntry_eq_ok {j : Json} {e : Entry} : decodeEntry j = .ok e ↔ EntryMatches j e := by
  unfold decodeEntry EntryMatches
  simp only [bind_eq_ok, object_eq_ok, getArr_eq_ok fun _ _ _ => natOf_eq_ok,
    get_eq_ok fun _ _ => decodeValue_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, c, hc, v, hv, rfl⟩
    exact ⟨o, rfl, hs, hc, hv⟩
  · rintro ⟨o, rfl, hs, hc, hv⟩
    exact ⟨o, ⟨rfl, hs⟩, _, hc, _, hv, rfl⟩

/-- A numeric table: `axes` (zero-based variable indices) and `entries`. -/
structure NumTable where
  axes : List Nat
  entries : List Entry
  deriving DecidableEq

def decodeNumTable (nv : Nat) (j : Json) : Except String NumTable := do
  let o ← object "table" 2 j
  let a ← getArr o "axes" (fun _ => refOf nv)
  let e ← getArr o "entries" (fun _ => decodeEntry)
  pure ⟨a, e⟩

def NumTableMatches (nv : Nat) (j : Json) (t : NumTable) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 2 ∧
    (∃ v, o["axes"]? = some v ∧
      ArrayMatches (fun _ x i => x = .str (toString (i + 1)) ∧ i < nv) v t.axes) ∧
    ∃ v, o["entries"]? = some v ∧ ArrayMatches (fun _ => EntryMatches) v t.entries

theorem decodeNumTable_eq_ok {nv : Nat} {j : Json} {t : NumTable} :
    decodeNumTable nv j = .ok t ↔ NumTableMatches nv j t := by
  unfold decodeNumTable NumTableMatches
  simp only [bind_eq_ok, object_eq_ok, getArr_eq_ok fun _ _ _ => refOf_eq_ok,
    getArr_eq_ok fun _ _ _ => decodeEntry_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, a, ha, e, he, rfl⟩
    exact ⟨o, rfl, hs, ha, he⟩
  · rintro ⟨o, rfl, hs, ha, he⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ha, _, he, rfl⟩

/-! ## Rows -/

/-- A state row of a variable: its `State` part ID, its one-based `state_position` and label, as
written. -/
structure StateEntry where
  id : Nat
  position : Nat
  label : String
  deriving DecidableEq

def decodeState (j : Json) : Except String StateEntry := do
  let o ← object "state" 3 j
  let i ← get o "id" idOf
  let p ← get o "position" natOf
  let l ← get o "label" strOf
  pure ⟨i, p, l⟩

def StateMatches (j : Json) (e : StateEntry) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 3 ∧ o["id"]? = some (.str (toString e.id)) ∧ 1 ≤ e.id ∧
    o["position"]? = some (natJson e.position) ∧ o["label"]? = some (.str e.label)

theorem decodeState_eq_ok {j : Json} {e : StateEntry} : decodeState j = .ok e ↔ StateMatches j e := by
  unfold decodeState StateMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => idOf_eq_ok,
    get_eq_ok fun _ _ => natOf_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, i, ⟨_, hi, rfl, h1⟩, p, ⟨_, hp, rfl⟩, l, ⟨_, hl, rfl⟩, rfl⟩
    exact ⟨o, rfl, hs, hi, h1, hp, hl⟩
  · rintro ⟨o, rfl, hs, hi, h1, hp, hl⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hi, rfl, h1⟩, _, ⟨_, hp, rfl⟩, _, ⟨_, hl, rfl⟩, rfl⟩

/-- An ordered slot (`parents`, `information` or `inputs`): the part ID and the one-based position
as written, and the zero-based index of the variable. -/
structure Slot where
  id : Nat
  position : Nat
  var : Nat
  deriving DecidableEq

def decodeSlot (nv : Nat) (j : Json) : Except String Slot := do
  let o ← object "slot" 3 j
  let i ← get o "id" idOf
  let p ← get o "position" natOf
  let v ← get o "variable" (refOf nv)
  pure ⟨i, p, v⟩

def SlotMatches (nv : Nat) (j : Json) (s : Slot) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 3 ∧ o["id"]? = some (.str (toString s.id)) ∧ 1 ≤ s.id ∧
    o["position"]? = some (natJson s.position) ∧
    o["variable"]? = some (.str (toString (s.var + 1))) ∧ s.var < nv

theorem decodeSlot_eq_ok {nv : Nat} {j : Json} {s : Slot} :
    decodeSlot nv j = .ok s ↔ SlotMatches nv j s := by
  unfold decodeSlot SlotMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => idOf_eq_ok,
    get_eq_ok fun _ _ => natOf_eq_ok, get_eq_ok fun _ _ => refOf_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, i, ⟨_, hi, rfl, h1⟩, p, ⟨_, hp, rfl⟩, v, ⟨_, hv, rfl, hlt⟩, rfl⟩
    exact ⟨o, rfl, hs, hi, h1, hp, hv, hlt⟩
  · rintro ⟨o, rfl, hs, hi, h1, hp, hv, hlt⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hi, rfl, h1⟩, _, ⟨_, hp, rfl⟩, _, ⟨_, hv, rfl, hlt⟩, rfl⟩

/-- `"kind"`: a chance or a decision variable. -/
inductive Kind where
  | chance
  | decision
  deriving DecidableEq

def kindString : Kind → String
  | .chance => "chance"
  | .decision => "decision"

def kindOf (j : Json) : Except String Kind := do
  let s ← strOf j
  if s = "chance" then pure .chance
  else if s = "decision" then pure .decision
  else throw s!"\"{s}\" is not \"chance\" or \"decision\""

theorem kindOf_eq_ok {j : Json} {k : Kind} : kindOf j = .ok k ↔ j = .str (kindString k) := by
  unfold kindOf
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
    cases k <;> simp [kindString] <;> rfl

/-- A `"variables"` row (its `id`, the row number, is checked and not stored). -/
structure VariableEntry where
  name : String
  kind : Kind
  spaceRef : Nat
  states : List StateEntry
  deriving DecidableEq

def decodeVariable (npool : Nat) (k : Nat) (j : Json) : Except String VariableEntry := do
  let o ← object "variable" 5 j
  rowId o k
  let n ← get o "name" strOf
  let kd ← get o "kind" kindOf
  let sr ← get o "space_ref" (codeOf npool)
  let st ← getArr o "states" (fun _ => decodeState)
  pure ⟨n, kd, sr, st⟩

def VariableMatches (npool : Nat) (k : Nat) (j : Json) (e : VariableEntry) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 5 ∧ o["id"]? = some (.str (toString (k + 1))) ∧
    o["name"]? = some (.str e.name) ∧ o["kind"]? = some (.str (kindString e.kind)) ∧
    o["space_ref"]? = some (natJson e.spaceRef) ∧ e.spaceRef < npool ∧
    ∃ v, o["states"]? = some v ∧ ArrayMatches (fun _ => StateMatches) v e.states

theorem decodeVariable_eq_ok {npool k : Nat} {j : Json} {e : VariableEntry} :
    decodeVariable npool k j = .ok e ↔ VariableMatches npool k j e := by
  unfold decodeVariable VariableMatches
  simp only [bind_eq_ok, object_eq_ok, rowId_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok,
    get_eq_ok fun _ _ => kindOf_eq_ok, get_eq_ok fun _ _ => codeOf_eq_ok,
    getArr_eq_ok fun _ _ _ => decodeState_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hid, n, ⟨_, hn, rfl⟩, kd, ⟨_, hk, rfl⟩, sr, ⟨_, hsr, rfl, hlt⟩, st,
      hst, rfl⟩
    exact ⟨o, rfl, hs, hid, hn, hk, hsr, hlt, hst⟩
  · rintro ⟨o, rfl, hs, hid, hn, hk, hsr, hlt, hst⟩
    exact ⟨o, ⟨rfl, hs⟩, (), hid, _, ⟨_, hn, rfl⟩, _, ⟨_, hk, rfl⟩, _, ⟨_, hsr, rfl, hlt⟩, _, hst,
      rfl⟩

/-- A `"mechanisms"` row. -/
structure MechanismEntry where
  name : String
  target : Nat
  kernelRef : Nat
  parents : List Slot
  cpt : NumTable
  factor : NumTable
  deriving DecidableEq

def decodeMechanism (nv npool : Nat) (k : Nat) (j : Json) : Except String MechanismEntry := do
  let o ← object "mechanism" 7 j
  rowId o k
  let n ← get o "name" strOf
  let t ← get o "target" (refOf nv)
  let kr ← get o "kernel_ref" (codeOf npool)
  let ps ← getArr o "parents" (fun _ => decodeSlot nv)
  let c ← get o "cpt" (decodeNumTable nv)
  let f ← get o "factor" (decodeNumTable nv)
  pure ⟨n, t, kr, ps, c, f⟩

def MechanismMatches (nv npool : Nat) (k : Nat) (j : Json) (e : MechanismEntry) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 7 ∧ o["id"]? = some (.str (toString (k + 1))) ∧
    o["name"]? = some (.str e.name) ∧
    o["target"]? = some (.str (toString (e.target + 1))) ∧ e.target < nv ∧
    o["kernel_ref"]? = some (natJson e.kernelRef) ∧ e.kernelRef < npool ∧
    (∃ v, o["parents"]? = some v ∧ ArrayMatches (fun _ => SlotMatches nv) v e.parents) ∧
    (∃ v, o["cpt"]? = some v ∧ NumTableMatches nv v e.cpt) ∧
    ∃ v, o["factor"]? = some v ∧ NumTableMatches nv v e.factor

theorem decodeMechanism_eq_ok {nv npool k : Nat} {j : Json} {e : MechanismEntry} :
    decodeMechanism nv npool k j = .ok e ↔ MechanismMatches nv npool k j e := by
  unfold decodeMechanism MechanismMatches
  simp only [bind_eq_ok, object_eq_ok, rowId_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok,
    get_eq_ok fun _ _ => refOf_eq_ok, get_eq_ok fun _ _ => codeOf_eq_ok,
    getArr_eq_ok fun _ _ _ => decodeSlot_eq_ok, get_eq_ok fun _ _ => decodeNumTable_eq_ok,
    pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hid, n, ⟨_, hn, rfl⟩, t, ⟨_, ht, rfl, htl⟩, kr, ⟨_, hkr, rfl, hkl⟩,
      ps, hps, c, hc, f, hf, rfl⟩
    exact ⟨o, rfl, hs, hid, hn, ht, htl, hkr, hkl, hps, hc, hf⟩
  · rintro ⟨o, rfl, hs, hid, hn, ht, htl, hkr, hkl, hps, hc, hf⟩
    exact ⟨o, ⟨rfl, hs⟩, (), hid, _, ⟨_, hn, rfl⟩, _, ⟨_, ht, rfl, htl⟩, _, ⟨_, hkr, rfl, hkl⟩,
      _, hps, _, hc, _, hf, rfl⟩

/-- A `"decisions"` row. -/
structure DecisionEntry where
  name : String
  action : Nat
  information : List Slot
  deriving DecidableEq

def decodeDecision (nv : Nat) (k : Nat) (j : Json) : Except String DecisionEntry := do
  let o ← object "decision" 4 j
  rowId o k
  let n ← get o "name" strOf
  let a ← get o "action" (refOf nv)
  let inf ← getArr o "information" (fun _ => decodeSlot nv)
  pure ⟨n, a, inf⟩

def DecisionMatches (nv : Nat) (k : Nat) (j : Json) (e : DecisionEntry) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 4 ∧ o["id"]? = some (.str (toString (k + 1))) ∧
    o["name"]? = some (.str e.name) ∧
    o["action"]? = some (.str (toString (e.action + 1))) ∧ e.action < nv ∧
    ∃ v, o["information"]? = some v ∧ ArrayMatches (fun _ => SlotMatches nv) v e.information

theorem decodeDecision_eq_ok {nv k : Nat} {j : Json} {e : DecisionEntry} :
    decodeDecision nv k j = .ok e ↔ DecisionMatches nv k j e := by
  unfold decodeDecision DecisionMatches
  simp only [bind_eq_ok, object_eq_ok, rowId_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok,
    get_eq_ok fun _ _ => refOf_eq_ok, getArr_eq_ok fun _ _ _ => decodeSlot_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hid, n, ⟨_, hn, rfl⟩, a, ⟨_, ha, rfl, hal⟩, inf, hinf, rfl⟩
    exact ⟨o, rfl, hs, hid, hn, ha, hal, hinf⟩
  · rintro ⟨o, rfl, hs, hid, hn, ha, hal, hinf⟩
    exact ⟨o, ⟨rfl, hs⟩, (), hid, _, ⟨_, hn, rfl⟩, _, ⟨_, ha, rfl, hal⟩, _, hinf, rfl⟩

/-- A `"precedence"` row (zero-based decision indices). -/
structure PrecedenceEntry where
  earlier : Nat
  later : Nat
  deriving DecidableEq

def decodePrecedence (nd : Nat) (k : Nat) (j : Json) : Except String PrecedenceEntry := do
  let o ← object "precedence" 3 j
  rowId o k
  let e ← get o "earlier" (refOf nd)
  let l ← get o "later" (refOf nd)
  pure ⟨e, l⟩

def PrecedenceMatches (nd : Nat) (k : Nat) (j : Json) (e : PrecedenceEntry) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 3 ∧ o["id"]? = some (.str (toString (k + 1))) ∧
    o["earlier"]? = some (.str (toString (e.earlier + 1))) ∧ e.earlier < nd ∧
    o["later"]? = some (.str (toString (e.later + 1))) ∧ e.later < nd

theorem decodePrecedence_eq_ok {nd k : Nat} {j : Json} {e : PrecedenceEntry} :
    decodePrecedence nd k j = .ok e ↔ PrecedenceMatches nd k j e := by
  unfold decodePrecedence PrecedenceMatches
  simp only [bind_eq_ok, object_eq_ok, rowId_eq_ok, get_eq_ok fun _ _ => refOf_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hid, a, ⟨_, ha, rfl, hal⟩, b, ⟨_, hb, rfl, hbl⟩, rfl⟩
    exact ⟨o, rfl, hs, hid, ha, hal, hb, hbl⟩
  · rintro ⟨o, rfl, hs, hid, ha, hal, hb, hbl⟩
    exact ⟨o, ⟨rfl, hs⟩, (), hid, _, ⟨_, ha, rfl, hal⟩, _, ⟨_, hb, rfl, hbl⟩, rfl⟩

/-- A `"utilities"` row. -/
structure UtilityEntry where
  name : String
  utilityRef : Nat
  inputs : List Slot
  table : NumTable
  deriving DecidableEq

def decodeUtility (nv npool : Nat) (k : Nat) (j : Json) : Except String UtilityEntry := do
  let o ← object "utility" 5 j
  rowId o k
  let n ← get o "name" strOf
  let ur ← get o "utility_ref" (codeOf npool)
  let ins ← getArr o "inputs" (fun _ => decodeSlot nv)
  let t ← get o "table" (decodeNumTable nv)
  pure ⟨n, ur, ins, t⟩

def UtilityMatches (nv npool : Nat) (k : Nat) (j : Json) (e : UtilityEntry) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 5 ∧ o["id"]? = some (.str (toString (k + 1))) ∧
    o["name"]? = some (.str e.name) ∧
    o["utility_ref"]? = some (natJson e.utilityRef) ∧ e.utilityRef < npool ∧
    (∃ v, o["inputs"]? = some v ∧ ArrayMatches (fun _ => SlotMatches nv) v e.inputs) ∧
    ∃ v, o["table"]? = some v ∧ NumTableMatches nv v e.table

theorem decodeUtility_eq_ok {nv npool k : Nat} {j : Json} {e : UtilityEntry} :
    decodeUtility nv npool k j = .ok e ↔ UtilityMatches nv npool k j e := by
  unfold decodeUtility UtilityMatches
  simp only [bind_eq_ok, object_eq_ok, rowId_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok,
    get_eq_ok fun _ _ => codeOf_eq_ok, getArr_eq_ok fun _ _ _ => decodeSlot_eq_ok,
    get_eq_ok fun _ _ => decodeNumTable_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hid, n, ⟨_, hn, rfl⟩, ur, ⟨_, hur, rfl, hul⟩, ins, hins, t, ht, rfl⟩
    exact ⟨o, rfl, hs, hid, hn, hur, hul, hins, ht⟩
  · rintro ⟨o, rfl, hs, hid, hn, hur, hul, hins, ht⟩
    exact ⟨o, ⟨rfl, hs⟩, (), hid, _, ⟨_, hn, rfl⟩, _, ⟨_, hur, rfl, hul⟩, _, hins, _, ht, rfl⟩

/-- A `"reference_pool"` row: its `code` is the zero-based row number; the reference is stored. -/
def decodePoolEntry (k : Nat) (j : Json) : Except String Ref := do
  let o ← object "pool entry" 2 j
  let c ← get o "code" natOf
  require (c = k) s!"the code is {c}, expected {k}"
  get o "reference" (decodeRef "reference")

def PoolMatches (k : Nat) (j : Json) (r : Ref) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 2 ∧ o["code"]? = some (natJson k) ∧
    ∃ v, o["reference"]? = some v ∧ RefMatches v r

theorem decodePoolEntry_eq_ok {k : Nat} {j : Json} {r : Ref} :
    decodePoolEntry k j = .ok r ↔ PoolMatches k j r := by
  unfold decodePoolEntry PoolMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => natOf_eq_ok, require_eq_ok,
    get_eq_ok fun _ _ => decodeRef_eq_ok (row := "reference")]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, c, ⟨_, hc, rfl⟩, _, rfl, hr⟩
    exact ⟨o, rfl, hs, hc, hr⟩
  · rintro ⟨o, rfl, hs, hc, hr⟩
    exact ⟨o, ⟨rfl, hs⟩, k, ⟨_, hc, rfl⟩, (), rfl, hr⟩

/-- A hard-evidence row: the zero-based variable index and the zero-based state index. -/
structure HardEntry where
  var : Nat
  stateIndex : Nat
  deriving DecidableEq

def decodeHard (nv : Nat) (j : Json) : Except String HardEntry := do
  let o ← object "hard evidence" 2 j
  let v ← get o "variable" (refOf nv)
  let s ← get o "state_index" natOf
  pure ⟨v, s⟩

def HardMatches (nv : Nat) (j : Json) (e : HardEntry) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 2 ∧ o["variable"]? = some (.str (toString (e.var + 1))) ∧
    e.var < nv ∧ o["state_index"]? = some (natJson e.stateIndex)

theorem decodeHard_eq_ok {nv : Nat} {j : Json} {e : HardEntry} :
    decodeHard nv j = .ok e ↔ HardMatches nv j e := by
  unfold decodeHard HardMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => refOf_eq_ok,
    get_eq_ok fun _ _ => natOf_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, v, ⟨_, hv, rfl, hvl⟩, s, ⟨_, hsj, rfl⟩, rfl⟩
    exact ⟨o, rfl, hs, hv, hvl, hsj⟩
  · rintro ⟨o, rfl, hs, hv, hvl, hsj⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hv, rfl, hvl⟩, _, ⟨_, hsj, rfl⟩, rfl⟩

/-- `"evidence"`: the hard rows, and `"likelihood": null`. -/
def decodeEvidence (nv : Nat) (j : Json) : Except String (List HardEntry) := do
  let o ← object "evidence" 2 j
  get o "likelihood" nullOf
  getArr o "hard" (fun _ => decodeHard nv)

def EvidenceMatches (nv : Nat) (j : Json) (l : List HardEntry) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 2 ∧ o["likelihood"]? = some .null ∧
    ∃ v, o["hard"]? = some v ∧ ArrayMatches (fun _ => HardMatches nv) v l

theorem decodeEvidence_eq_ok {nv : Nat} {j : Json} {l : List HardEntry} :
    decodeEvidence nv j = .ok l ↔ EvidenceMatches nv j l := by
  unfold decodeEvidence EvidenceMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => nullOf_eq_ok,
    getArr_eq_ok fun _ _ _ => decodeHard_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, ⟨_, hl, rfl⟩, hh⟩
    exact ⟨o, rfl, hs, hl, hh⟩
  · rintro ⟨o, rfl, hs, hl, hh⟩
    exact ⟨o, ⟨rfl, hs⟩, (), ⟨_, hl, rfl⟩, hh⟩

/-- `"provenance"`: five strings. -/
structure Provenance where
  manifest : String
  modelName : String
  exporter : String
  origin : String
  exactSource : String
  deriving DecidableEq

def decodeProvenance (j : Json) : Except String Provenance := do
  let o ← object "provenance" 5 j
  let a ← get o "implementation_manifest_sha256" strOf
  let b ← get o "model_name" strOf
  let c ← get o "exporter" strOf
  let d ← get o "origin" strOf
  let e ← get o "exact_source" strOf
  pure ⟨a, b, c, d, e⟩

def ProvenanceMatches (j : Json) (p : Provenance) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 5 ∧
    o["implementation_manifest_sha256"]? = some (.str p.manifest) ∧
    o["model_name"]? = some (.str p.modelName) ∧ o["exporter"]? = some (.str p.exporter) ∧
    o["origin"]? = some (.str p.origin) ∧ o["exact_source"]? = some (.str p.exactSource)

theorem decodeProvenance_eq_ok {j : Json} {p : Provenance} :
    decodeProvenance j = .ok p ↔ ProvenanceMatches j p := by
  unfold decodeProvenance ProvenanceMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, a, ⟨_, ha, rfl⟩, b, ⟨_, hb, rfl⟩, c, ⟨_, hc, rfl⟩, d, ⟨_, hd, rfl⟩,
      e, ⟨_, he, rfl⟩, rfl⟩
    exact ⟨o, rfl, hs, ha, hb, hc, hd, he⟩
  · rintro ⟨o, rfl, hs, ha, hb, hc, hd, he⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, ha, rfl⟩, _, ⟨_, hb, rfl⟩, _, ⟨_, hc, rfl⟩, _, ⟨_, hd, rfl⟩,
      _, ⟨_, he, rfl⟩, rfl⟩

/-- `"numeric"`: the numeric mode, whether runtime bits are captured, and the normalization. -/
structure Numeric where
  mode : String
  runtimeBits : Bool
  normalization : String
  deriving DecidableEq

def decodeNumeric (j : Json) : Except String Numeric := do
  let o ← object "numeric" 3 j
  let m ← get o "mode" strOf
  let b ← get o "runtime_bits" boolOf
  let n ← get o "normalization" strOf
  pure ⟨m, b, n⟩

def NumericMatches (j : Json) (n : Numeric) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 3 ∧ o["mode"]? = some (.str n.mode) ∧
    o["runtime_bits"]? = some (.bool n.runtimeBits) ∧
    o["normalization"]? = some (.str n.normalization)

theorem decodeNumeric_eq_ok {j : Json} {n : Numeric} :
    decodeNumeric j = .ok n ↔ NumericMatches j n := by
  unfold decodeNumeric NumericMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok,
    get_eq_ok fun _ _ => boolOf_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, m, ⟨_, hm, rfl⟩, b, ⟨_, hb, rfl⟩, x, ⟨_, hx, rfl⟩, rfl⟩
    exact ⟨o, rfl, hs, hm, hb, hx⟩
  · rintro ⟨o, rfl, hs, hm, hb, hx⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hm, rfl⟩, _, ⟨_, hb, rfl⟩, _, ⟨_, hx, rfl⟩, rfl⟩

/-- `"runtime_tolerances"`: two binary64 words (metadata; no theorem reads them). -/
structure Tolerances where
  kernel : Nat
  decision : Nat
  deriving DecidableEq

def decodeTolerances (j : Json) : Except String Tolerances := do
  let o ← object "runtime_tolerances" 2 j
  let a ← get o "kernel_normalization_f64" wordOf
  let b ← get o "decision_probability_f64" wordOf
  pure ⟨a, b⟩

def TolerancesMatches (j : Json) (t : Tolerances) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 2 ∧
    o["kernel_normalization_f64"]? = some (.str (hexWord t.kernel)) ∧ t.kernel < 2 ^ 64 ∧
    o["decision_probability_f64"]? = some (.str (hexWord t.decision)) ∧ t.decision < 2 ^ 64

theorem decodeTolerances_eq_ok {j : Json} {t : Tolerances} :
    decodeTolerances j = .ok t ↔ TolerancesMatches j t := by
  unfold decodeTolerances TolerancesMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => wordOf_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, a, ⟨_, ha, rfl, hal⟩, b, ⟨_, hb, rfl, hbl⟩, rfl⟩
    exact ⟨o, rfl, hs, ha, hal, hb, hbl⟩
  · rintro ⟨o, rfl, hs, ha, hal, hb, hbl⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, ha, rfl, hal⟩, _, ⟨_, hb, rfl, hbl⟩, rfl⟩

/-! ## The certificate -/

/-- **The DVE certificate**, as `export_dve_certificate` writes it. References to variables and
decisions are zero-based indices; pool codes are zero-based. -/
structure Certificate where
  provenance : Provenance
  numeric : Numeric
  tolerances : Tolerances
  pool : List Ref
  vars : List VariableEntry
  topological : List Nat
  decisionOrder : List Nat
  mechanisms : List MechanismEntry
  decisions : List DecisionEntry
  precedence : List PrecedenceEntry
  utilities : List UtilityEntry
  hard : List HardEntry

/-- The `"format"` of the version-1 profile. -/
def certFormat : String := "ecorecipes.dve-certificate"

/-- The fourteen top-level keys. -/
def certKeys : List String :=
  ["format", "version", "provenance", "numeric", "runtime_tolerances", "reference_pool",
    "variables", "topological_order", "decision_order", "mechanisms", "decisions", "precedence",
    "utilities", "evidence"]

/-- **The decoder.** A parsed certificate to its records: pool first, then the variables (whose
`space_ref` must be a pool code), the decisions, and the rows that refer to them. -/
def decodeCertificate (j : Json) : Except String Certificate := do
  let o ← object "certificate" 14 j
  let fmt ← get o "format" strOf
  require (fmt = certFormat) s!"format is \"{fmt}\", expected \"{certFormat}\""
  let ver ← get o "version" natOf
  require (ver = 1) s!"version is {ver}, expected 1"
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

/-- **The document is the certificate `c`**: exactly the fourteen keys, the format and version,
and every key, row and column holding `c`'s value, with every reference in range. -/
def CertificateMatches (j : Json) (c : Certificate) : Prop :=
  ∃ o, j = .obj o ∧ o.size = 14 ∧ o["format"]? = some (.str certFormat) ∧
    o["version"]? = some (natJson 1) ∧
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

/-- **Faithfulness.** Decoding succeeds with `c` exactly when the document is `c`'s layout. -/
theorem decodeCertificate_eq_ok {j : Json} {c : Certificate} :
    decodeCertificate j = .ok c ↔ CertificateMatches j c := by
  unfold decodeCertificate CertificateMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok,
    get_eq_ok fun _ _ => natOf_eq_ok, require_eq_ok,
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
  · rintro ⟨o, ⟨rfl, hs⟩, fmt, ⟨_, hfmt, rfl⟩, _, rfl, ver, ⟨_, hver, rfl⟩, _, rfl, prov, hprov,
      num, hnum, tol, htol, pool, hpool, vars, hvars, decs, hdecs, topo, htopo, dord, hdord,
      mechs, hmechs, prec, hprec, us, hus, hard, hhard, rfl⟩
    exact ⟨o, rfl, hs, hfmt, hver, hprov, hnum, htol, hpool, hvars, hdecs, htopo, hdord, hmechs,
      hprec, hus, hhard⟩
  · rintro ⟨o, rfl, hs, hfmt, hver, hprov, hnum, htol, hpool, hvars, hdecs, htopo, hdord, hmechs,
      hprec, hus, hhard⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hfmt, rfl⟩, (), rfl, _, ⟨_, hver, rfl⟩, (), rfl, _, hprov, _, hnum,
      _, htol, _, hpool, _, hvars, _, hdecs, _, htopo, _, hdord, _, hmechs, _, hprec, _, hus, _,
      hhard, rfl⟩

/-! ## Encoding -/

def encodeRational (n : Int) (d : Nat) : Json :=
  Json.mkObj [("num", .str (intString n)), ("den", .str (toString d))]

def encodeValue : Value → Json
  | .f64 w => Json.mkObj [("f64", .str (hexWord w))]
  | .q n d => Json.mkObj [("q", encodeRational n d)]
  | .qf64 n d w => Json.mkObj [("q", encodeRational n d), ("f64", .str (hexWord w))]

def encodeEntry (e : Entry) : Json :=
  Json.mkObj [("at", encodeArray (fun _ c => natJson c) e.coords), ("value", encodeValue e.value)]

def encodeNumTable (t : NumTable) : Json :=
  Json.mkObj [("axes", encodeArray (fun _ i => .str (toString (i + 1))) t.axes),
    ("entries", encodeArray (fun _ => encodeEntry) t.entries)]

def encodeState (e : StateEntry) : Json :=
  Json.mkObj [("id", .str (toString e.id)), ("position", natJson e.position),
    ("label", .str e.label)]

def encodeSlot (s : Slot) : Json :=
  Json.mkObj [("id", .str (toString s.id)), ("position", natJson s.position),
    ("variable", Json.str (toString (s.var + 1)))]

def encodeVariable (k : Nat) (e : VariableEntry) : Json :=
  Json.mkObj [("id", Json.str (toString (k + 1))), ("name", .str e.name), ("kind", .str (kindString e.kind)),
    ("space_ref", natJson e.spaceRef), ("states", encodeArray (fun _ => encodeState) e.states)]

def encodeMechanism (k : Nat) (e : MechanismEntry) : Json :=
  Json.mkObj [("id", Json.str (toString (k + 1))), ("name", .str e.name), ("target", Json.str (toString (e.target + 1))),
    ("kernel_ref", natJson e.kernelRef), ("parents", encodeArray (fun _ => encodeSlot) e.parents),
    ("cpt", encodeNumTable e.cpt), ("factor", encodeNumTable e.factor)]

def encodeDecision (k : Nat) (e : DecisionEntry) : Json :=
  Json.mkObj [("id", Json.str (toString (k + 1))), ("name", .str e.name), ("action", Json.str (toString (e.action + 1))),
    ("information", encodeArray (fun _ => encodeSlot) e.information)]

def encodePrecedence (k : Nat) (e : PrecedenceEntry) : Json :=
  Json.mkObj [("id", Json.str (toString (k + 1))), ("earlier", Json.str (toString (e.earlier + 1))),
    ("later", Json.str (toString (e.later + 1)))]

def encodeUtility (k : Nat) (e : UtilityEntry) : Json :=
  Json.mkObj [("id", Json.str (toString (k + 1))), ("name", .str e.name), ("utility_ref", natJson e.utilityRef),
    ("inputs", encodeArray (fun _ => encodeSlot) e.inputs), ("table", encodeNumTable e.table)]

def encodePoolEntry (k : Nat) (r : Ref) : Json :=
  Json.mkObj [("code", natJson k), ("reference", encodeRef r)]

def encodeHard (e : HardEntry) : Json :=
  Json.mkObj [("variable", Json.str (toString (e.var + 1))), ("state_index", natJson e.stateIndex)]

def encodeEvidence (l : List HardEntry) : Json :=
  Json.mkObj [("hard", encodeArray (fun _ => encodeHard) l), ("likelihood", .null)]

def encodeProvenance (p : Provenance) : Json :=
  Json.mkObj [("implementation_manifest_sha256", .str p.manifest), ("model_name", .str p.modelName),
    ("exporter", .str p.exporter), ("origin", .str p.origin), ("exact_source", .str p.exactSource)]

def encodeNumeric (n : Numeric) : Json :=
  Json.mkObj [("mode", .str n.mode), ("runtime_bits", .bool n.runtimeBits),
    ("normalization", .str n.normalization)]

def encodeTolerances (t : Tolerances) : Json :=
  Json.mkObj [("kernel_normalization_f64", .str (hexWord t.kernel)),
    ("decision_probability_f64", .str (hexWord t.decision))]

/-- **The encoder**, the layout `export_dve_certificate` and `JSON3.write` produce (up to key order
and whitespace). -/
def encodeCertificate (c : Certificate) : Json :=
  Json.mkObj [("format", .str certFormat), ("version", natJson 1),
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
    ("evidence", encodeEvidence c.hard)]

/-! ## Range conditions -/

def Value.InRange : Value → Prop
  | .f64 w => w < 2 ^ 64
  | .q _ d => 1 ≤ d
  | .qf64 _ d w => 1 ≤ d ∧ w < 2 ^ 64

def NumTable.InRange (nv : Nat) (t : NumTable) : Prop :=
  (∀ a ∈ t.axes, a < nv) ∧ ∀ e ∈ t.entries, e.value.InRange

def Slot.InRange (nv : Nat) (s : Slot) : Prop := 1 ≤ s.id ∧ s.var < nv

/-- **Every reference in range**: what the decoder requires beyond the layout. -/
structure Certificate.InRange (c : Certificate) : Prop where
  tolerances : c.tolerances.kernel < 2 ^ 64 ∧ c.tolerances.decision < 2 ^ 64
  vars : ∀ e ∈ c.vars, e.spaceRef < c.pool.length ∧ ∀ s ∈ e.states, 1 ≤ s.id
  topological : ∀ v ∈ c.topological, v < c.vars.length
  decisionOrder : ∀ d ∈ c.decisionOrder, d < c.decisions.length
  mechanisms : ∀ e ∈ c.mechanisms, e.target < c.vars.length ∧
    e.kernelRef < c.pool.length ∧ (∀ s ∈ e.parents, s.InRange c.vars.length) ∧
    e.cpt.InRange c.vars.length ∧ e.factor.InRange c.vars.length
  decisions : ∀ e ∈ c.decisions, e.action < c.vars.length ∧
    ∀ s ∈ e.information, s.InRange c.vars.length
  precedence : ∀ e ∈ c.precedence, e.earlier < c.decisions.length ∧ e.later < c.decisions.length
  utilities : ∀ e ∈ c.utilities, e.utilityRef < c.pool.length ∧
    (∀ s ∈ e.inputs, s.InRange c.vars.length) ∧ e.table.InRange c.vars.length
  hard : ∀ e ∈ c.hard, e.var < c.vars.length

/-! ## Matches of encoded records -/

theorem getElem_mem' {α : Type} {l : List α} {k : Nat} (hk : k < l.length) : l[k] ∈ l :=
  List.getElem_mem hk

theorem rationalMatches_encode (n : Int) (d : Nat) (hd : 1 ≤ d) :
    RationalMatches (encodeRational n d) n d :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), hd⟩

theorem valueMatches_encode (x : Value) (hx : x.InRange) : ValueMatches (encodeValue x) x := by
  cases x with
  | f64 w =>
    exact ⟨_, rfl, mkObj_size (by simp),
      Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false (by simp),
      mkObj_getElem? (by simp) (by simp), hx⟩
  | q n d =>
    exact ⟨_, rfl, mkObj_size (by simp),
      ⟨_, mkObj_getElem? (by simp) (by simp), rationalMatches_encode n d hx⟩,
      Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false (by simp)⟩
  | qf64 n d w =>
    exact ⟨_, rfl, mkObj_size (by simp),
      ⟨_, mkObj_getElem? (by simp) (by simp), rationalMatches_encode n d hx.1⟩,
      mkObj_getElem? (by simp) (by simp), hx.2⟩

theorem entryMatches_encode (e : Entry) (he : e.value.InRange) : EntryMatches (encodeEntry e) e :=
  ⟨_, rfl, mkObj_size (by simp),
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := fun _ c => natJson c) fun _ _ => rfl⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp), valueMatches_encode _ he⟩⟩

theorem numTableMatches_encode {nv : Nat} (t : NumTable) (ht : t.InRange nv) :
    NumTableMatches nv (encodeNumTable t) t :=
  ⟨_, rfl, mkObj_size (by simp),
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := fun _ i => .str (toString (i + 1))) fun k hk =>
        ⟨rfl, ht.1 _ (getElem_mem' hk)⟩⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := fun _ => encodeEntry) fun k hk =>
        entryMatches_encode _ (ht.2 _ (getElem_mem' hk))⟩⟩

theorem slotMatches_encode {nv : Nat} (s : Slot) (hs : s.InRange nv) :
    SlotMatches nv (encodeSlot s) s :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp), hs.1,
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp), hs.2⟩

theorem slotsMatch_encode {nv : Nat} (l : List Slot) (hl : ∀ s ∈ l, s.InRange nv) :
    ArrayMatches (fun _ => SlotMatches nv) (encodeArray (fun _ => encodeSlot) l) l :=
  arrayMatches_encode (enc := fun _ => encodeSlot) fun _ hk =>
    slotMatches_encode _ (hl _ (getElem_mem' hk))

theorem stateMatches_encode (e : StateEntry) (he : 1 ≤ e.id) : StateMatches (encodeState e) e :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp), he,
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp)⟩

theorem variableMatches_encode {npool : Nat} (k : Nat) (e : VariableEntry)
    (he : e.spaceRef < npool ∧ ∀ s ∈ e.states, 1 ≤ s.id) :
    VariableMatches npool k (encodeVariable k e) e :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), he.1,
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := fun _ => encodeState) fun _ hi =>
        stateMatches_encode _ (he.2 _ (getElem_mem' hi))⟩⟩

theorem mechanismMatches_encode {nv npool : Nat} (k : Nat) (e : MechanismEntry)
    (he : e.target < nv ∧ e.kernelRef < npool ∧ (∀ s ∈ e.parents, s.InRange nv) ∧
      e.cpt.InRange nv ∧ e.factor.InRange nv) :
    MechanismMatches nv npool k (encodeMechanism k e) e :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp), he.1,
    mkObj_getElem? (by simp) (by simp), he.2.1,
    ⟨_, mkObj_getElem? (by simp) (by simp), slotsMatch_encode _ he.2.2.1⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp), numTableMatches_encode _ he.2.2.2.1⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp), numTableMatches_encode _ he.2.2.2.2⟩⟩

theorem decisionMatches_encode {nv : Nat} (k : Nat) (e : DecisionEntry)
    (he : e.action < nv ∧ ∀ s ∈ e.information, s.InRange nv) :
    DecisionMatches nv k (encodeDecision k e) e :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp), he.1,
    ⟨_, mkObj_getElem? (by simp) (by simp), slotsMatch_encode _ he.2⟩⟩

theorem precedenceMatches_encode {nd : Nat} (k : Nat) (e : PrecedenceEntry)
    (he : e.earlier < nd ∧ e.later < nd) : PrecedenceMatches nd k (encodePrecedence k e) e :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), he.1, mkObj_getElem? (by simp) (by simp), he.2⟩

theorem utilityMatches_encode {nv npool : Nat} (k : Nat) (e : UtilityEntry)
    (he : e.utilityRef < npool ∧ (∀ s ∈ e.inputs, s.InRange nv) ∧ e.table.InRange nv) :
    UtilityMatches nv npool k (encodeUtility k e) e :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp), he.1,
    ⟨_, mkObj_getElem? (by simp) (by simp), slotsMatch_encode _ he.2.1⟩,
    ⟨_, mkObj_getElem? (by simp) (by simp), numTableMatches_encode _ he.2.2⟩⟩

theorem poolMatches_encode (k : Nat) (r : Ref) : PoolMatches k (encodePoolEntry k r) r :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    ⟨_, mkObj_getElem? (by simp) (by simp), refMatches_encodeRef _⟩⟩

theorem hardMatches_encode {nv : Nat} (e : HardEntry) (he : e.var < nv) :
    HardMatches nv (encodeHard e) e :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp), he,
    mkObj_getElem? (by simp) (by simp)⟩

theorem evidenceMatches_encode {nv : Nat} (l : List HardEntry) (hl : ∀ e ∈ l, e.var < nv) :
    EvidenceMatches nv (encodeEvidence l) l :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    ⟨_, mkObj_getElem? (by simp) (by simp),
      arrayMatches_encode (enc := fun _ => encodeHard) fun _ hk =>
        hardMatches_encode _ (hl _ (getElem_mem' hk))⟩⟩

theorem provenanceMatches_encode (p : Provenance) : ProvenanceMatches (encodeProvenance p) p :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp)⟩

theorem numericMatches_encode (n : Numeric) : NumericMatches (encodeNumeric n) n :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp)⟩

theorem tolerancesMatches_encode (t : Tolerances) (ht : t.kernel < 2 ^ 64 ∧ t.decision < 2 ^ 64) :
    TolerancesMatches (encodeTolerances t) t :=
  ⟨_, rfl, mkObj_size (by simp), mkObj_getElem? (by simp) (by simp), ht.1,
    mkObj_getElem? (by simp) (by simp), ht.2⟩

/-- **Round trip.** An in-range certificate is recovered from its encoding. -/
theorem decodeCertificate_encode (c : Certificate) (hc : c.InRange) :
    decodeCertificate (encodeCertificate c) = .ok c :=
  decodeCertificate_eq_ok.2 ⟨_, rfl, mkObj_size (by simp),
    mkObj_getElem? (by simp) (by simp), mkObj_getElem? (by simp) (by simp),
    ⟨_, mkObj_getElem? (by simp) (by simp), provenanceMatches_encode _⟩,
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
    ⟨_, mkObj_getElem? (by simp) (by simp), evidenceMatches_encode _ hc.hard⟩⟩

/-! ## Failures -/

theorem ValueMatches.inRange {j : Json} {x : Value} (h : ValueMatches j x) : x.InRange := by
  cases x with
  | f64 w =>
    obtain ⟨_, -, -, -, -, hw⟩ := h
    exact hw
  | q n d =>
    obtain ⟨o, -, -, ⟨v, -, ⟨_, -, -, -, -, hd⟩⟩, -⟩ := h
    exact hd
  | qf64 n d w =>
    obtain ⟨o, -, -, ⟨v, -, ⟨_, -, -, -, -, hd⟩⟩, -, hw⟩ := h
    exact ⟨hd, hw⟩

theorem NumTableMatches.inRange {nv : Nat} {j : Json} {t : NumTable} (h : NumTableMatches nv j t) :
    t.InRange nv := by
  obtain ⟨o, -, -, ⟨_, -, ha⟩, ⟨_, -, he⟩⟩ := h
  exact ⟨ha.forall fun _ _ _ hm => hm.2,
    he.forall fun _ _ _ hm => by
      obtain ⟨_, -, -, -, ⟨_, -, hv⟩⟩ := hm
      exact hv.inRange⟩

theorem SlotMatches.inRange {nv : Nat} {j : Json} {s : Slot} (h : SlotMatches nv j s) :
    s.InRange nv := by
  obtain ⟨_, -, -, -, h1, -, -, h2⟩ := h
  exact ⟨h1, h2⟩

/-- **A decoded certificate has every reference in range**: a document with a variable or
decision ID outside `1..n`, a pool code past the pool, a nonpositive state or slot ID, a word of
`2 ^ 64` or more or a zero denominator does not decode. -/
theorem decodeCertificate_inRange {j : Json} {c : Certificate}
    (h : decodeCertificate j = .ok c) : c.InRange := by
  obtain ⟨o, -, -, -, -, -, -, ⟨_, -, htol⟩, -, ⟨_, -, hvars⟩, ⟨_, -, hdecs⟩, ⟨_, -, htopo⟩,
    ⟨_, -, hdord⟩, ⟨_, -, hmechs⟩, ⟨_, -, hprec⟩, ⟨_, -, hus⟩, ⟨_, -, hev⟩⟩ :=
    decodeCertificate_eq_ok.1 h
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

/-- **Failure: a missing top-level key.** -/
theorem decodeCertificate_error_of_missing_key {o : JsonObject} {k : String} (hk : k ∈ certKeys)
    (h : o[k]? = none) (c : Certificate) : decodeCertificate (.obj o) ≠ .ok c := fun hd => by
  obtain ⟨o', ho, -, hf, hv, ⟨_, hp, -⟩, ⟨_, hn, -⟩, ⟨_, ht, -⟩, ⟨_, hpool, -⟩, ⟨_, hvars, -⟩,
    ⟨_, hdecs, -⟩, ⟨_, htopo, -⟩, ⟨_, hdord, -⟩, ⟨_, hmechs, -⟩, ⟨_, hprec, -⟩, ⟨_, hus, -⟩,
    ⟨_, hev, -⟩⟩ := decodeCertificate_eq_ok.1 hd
  cases ho
  simp only [certKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all

/-- **Failure: a document that is not a JSON object.** -/
theorem decodeCertificate_error_of_not_object {j : Json} (h : ∀ o, j ≠ .obj o) (c : Certificate) :
    decodeCertificate j ≠ .ok c := fun hd => by
  obtain ⟨o, ho, -⟩ := decodeCertificate_eq_ok.1 hd
  exact h o ho

end InfluenceDiagramsProofs.DVECertificate
