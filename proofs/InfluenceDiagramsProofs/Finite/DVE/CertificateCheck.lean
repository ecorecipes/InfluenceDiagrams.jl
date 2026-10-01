import InfluenceDiagramsProofs.Finite.DVE.CertificateJson
import InfluenceDiagramsProofs.Finite.DVE.Schedule
import Mathlib.Data.Rat.BigOperators

/-!
# Checking a decoded DVE certificate against the decoded diagram

`Finite/DVE/CertificateJson.lean` decodes the certificate of `export_dve_certificate`;
`Finite/DVE/JsonRecords.lean` decodes the diagram's ACSet JSON into `Records.Diagram`. This
module connects the two. `certificateMatches r h c` (decidable) holds when the certificate
describes the checked diagram `r` exactly as Julia's exporter does:

* **variables and labels**: one row per variable, in part order, with the variable's name, its
  kind (`"decision"` exactly for actions), its space reference, and its state rows in
  `state_position` order (each the `State` part of that position, with its label);
* **mechanisms, decisions, utilities**: one row per part, with name, target or action, reference,
  and the ordered slots (`parents`, `information`, `inputs`), slot `j` being the part of position
  `j`; the policy axes of the label-order theorems are thus the certificate's information slots
  and the action's state rows;
* **tables**: the CPT axes are the parents then the target, the factor axes the parents and
  target without repeats (Julia's `unique`), the utility axes the scope; the entries list every
  coordinate of those axes' state counts exactly once, in lexicographic order with the rightmost
  coordinate fastest (`lexCoords`); every factor cell equals the CPT cell on its diagonal;
* **orders**: `topological_order` is a permutation of the variables in which every mechanism
  input, information variable and precedence arc points forward and every evidence variable
  precedes every action; `decision_order` is the decisions in that order and satisfies
  no-forgetting; the evidence rows are sorted, in range, and not on actions;
* **pool and numbers**: the reference pool has no duplicate and no unused entry; every value has
  the shape of the numeric mode, a finite word, a reduced rational, and, when both are present,
  the word is the rational's nearest-even rounding (`nearestBinary64`, `nearestBinary64_roundsTo`
  in BayesianNetworks; a rational `0` may carry either zero).

The exact value of a cell is the rational when present, otherwise the dyadic value of its
binary64 word (`Binary64.value`). `certKernel` and `certUtility` read the certificate's CPT and
utility tables at the coordinates of an assignment; under `certificateMatches` they are local
(`certKernel_local`, `certUtility_local`), `certOrder` is an `IDOrder` of the compiled diagram
built from `topological_order`, and `certNoForgetting` a `NoForgettingOrder` built from
`decision_order`.

**What the certificate determines.** The version-1 certificate is model data: it carries no
policy table, value or elimination plan. The theorems below are therefore about the model it
encodes, not about a Julia solution:

* `certificate_tables`: if the CPT cells are nonnegative (`Nonneg`, decidable), then Julia's
  sum-out representative run on the certificate's exact data, for any plan, returns on every
  information row the action of least `state_position` among the maximizers of the run's own
  score;
* `certificate_solve_spec`, `certificate_tables_optimal`: if moreover every CPT row sums to
  exactly one (`ExactNormalised`, decidable over `ℚ`), the DVE solution scheduled by the
  certificate's own orders is deterministic, realizes its value and attains the global optimum
  over all strategies, and every representative run's table entry, at every row of positive
  reach, is the least-position maximizer of the optimal continuation value.

The binary64 words Julia writes for decimal probabilities rarely sum to exactly one (three
`Float64` approximations of `0.7`, `0.2`, `0.1` sum to `1 - 2^-55`), so `ExactNormalised` is
decided and reported, never assumed; with `numeric_mode = :rational_exact` the rationals can.
Not proved: that Julia's own `Float64` or rational DVE run on the same data returns these tables
or this value, and evidence (`hard`) is checked structurally only; the semantic theorems are
for a certificate with no evidence row.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVECertificate

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram
open BayesianNetworksProofs.Raw InfluenceDiagramsProofs.Records

/-! ## Helpers -/

/-- `o` is `some a` with `P a`. -/
def OptHolds {α : Type} (P : α → Prop) : Option α → Prop
  | some a => P a
  | none => False

instance {α : Type} (P : α → Prop) [DecidablePred P] (o : Option α) : Decidable (OptHolds P o) :=
  match o with
  | some a => inferInstanceAs (Decidable (P a))
  | none => inferInstanceAs (Decidable False)

theorem OptHolds.of_eq {α : Type} {P : α → Prop} {o : Option α} {a : α} (h : OptHolds P o)
    (ha : o = some a) : P a := by
  subst ha
  exact h

/-- Every coordinate list of the given extents, lexicographic, the rightmost fastest. -/
def lexCoords : List Nat → List (List Nat)
  | [] => [[]]
  | n :: ns => (List.range n).flatMap fun i => (lexCoords ns).map (i :: ·)

theorem mem_lexCoords : ∀ {ds l : List Nat}, l ∈ lexCoords ds ↔ List.Forall₂ (· < ·) l ds
  | [], l => by
    simp only [lexCoords, List.mem_singleton, List.forall₂_nil_right_iff]
  | n :: ns, l => by
    simp only [lexCoords, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨i, hi, t, ht, rfl⟩
      exact List.Forall₂.cons hi (mem_lexCoords.1 ht)
    · intro h
      rcases h with _ | ⟨hab, hrest⟩
      exact ⟨_, hab, _, mem_lexCoords.2 hrest, rfl⟩

/-- Julia's `unique`: the first occurrence of each element, in order. -/
def uniqueFirst (l : List Nat) : List Nat :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- The exact value of a cell: the rational when present, otherwise the binary64 word's value. -/
def Value.toRat : Value → ℚ
  | .f64 w => Binary64.value w
  | .q n d => (n : ℚ) / (d : ℚ)
  | .qf64 n d _ => (n : ℚ) / (d : ℚ)

/-- The value of the cell at `coords`, or `none`. -/
def lookup (t : NumTable) (coords : List Nat) : Option Value :=
  (t.entries.find? fun e => decide (e.coords = coords)).map Entry.value

/-- The exact value of the cell at `coords` (`0` if there is none, which the checks exclude). -/
def cellValue (t : NumTable) (coords : List Nat) : ℚ :=
  ((lookup t coords).map Value.toRat).getD 0

/-- Every value of the certificate's tables. -/
def allValues (c : Certificate) : List Value :=
  (c.mechanisms.flatMap fun e => (e.cpt.entries ++ e.factor.entries).map Entry.value) ++
    c.utilities.flatMap fun e => e.table.entries.map Entry.value

/-! ## The diagram side -/

namespace Spec

variable (r : Diagram)

/-- The state count of a variable index (`0` out of range). -/
def dim (v : Nat) : Nat := if h : v < r.nv then r.stateCount ⟨v, h⟩ else 0

/-- Ordered slots: `l` has one slot per selected row, slot `j` being the selected row of position
`j`, with that row's part ID, `j + 1` and its variable. -/
def SlotsMatch {n : Nat} (sel : Fin n → Prop) [DecidablePred sel] (pos : Fin n → Nat)
    (var : Fin n → Nat) (l : List Slot) : Prop :=
  l.length = (Finset.univ.filter sel).card ∧
    ∀ j : Fin l.length, ∃ i : Fin n, sel i ∧ pos i = j.val ∧ l[j].id = i.val + 1 ∧
      l[j].position = j.val + 1 ∧ l[j].var = var i

/-- The state rows of variable `v`, in `state_position` order. -/
def StatesMatch (v : Fin r.nv) (l : List StateEntry) : Prop :=
  l.length = r.stateCount v ∧
    ∀ j : Fin l.length, ∃ s : Fin r.ns, (r.states s).var = v ∧ (r.states s).position = j.val ∧
      l[j].id = s.val + 1 ∧ l[j].position = j.val + 1 ∧ l[j].label = (r.states s).name

/-- A table's entries list every coordinate of its axes, lexicographically. -/
def Layout (t : NumTable) : Prop := t.entries.map Entry.coords = lexCoords (t.axes.map (dim r))

/-- Every factor cell is the CPT cell on its diagonal. -/
def Diagonal (e : MechanismEntry) : Prop :=
  ∀ fe ∈ e.factor.entries,
    lookup e.cpt (e.cpt.axes.map fun v => fe.coords.getD (e.factor.axes.idxOf v) 0) = some fe.value

def VariableOk (pool : List Ref) (v : Fin r.nv) (e : VariableEntry) : Prop :=
  e.name = (r.vars v).name ∧ (e.kind = .decision ↔ ∃ d, (r.decisions d).action = v) ∧
    pool[e.spaceRef]? = some (r.vars v).spaceRef ∧ StatesMatch r v e.states

def MechanismOk (pool : List Ref) (m : Fin r.nm) (e : MechanismEntry) : Prop :=
  e.name = (r.mechanisms m).name ∧ e.target = (r.mechanisms m).target.val ∧
    pool[e.kernelRef]? = some (r.mechanisms m).kernelRef ∧
    SlotsMatch (fun i => (r.inputs i).mechanism = m) (fun i => (r.inputs i).position)
      (fun i => (r.inputs i).var.val) e.parents ∧
    e.cpt.axes = e.parents.map Slot.var ++ [e.target] ∧ Layout r e.cpt ∧
    e.factor.axes = uniqueFirst e.cpt.axes ∧ Layout r e.factor ∧ Diagonal e

def DecisionOk (d : Fin r.nd) (e : DecisionEntry) : Prop :=
  e.name = (r.decisions d).name ∧ e.action = (r.decisions d).action.val ∧
    SlotsMatch (fun f => (r.information f).decision = d) (fun f => (r.information f).position)
      (fun f => (r.information f).var.val) e.information

def PrecedenceOk (p : Fin r.np) (e : PrecedenceEntry) : Prop :=
  e.earlier = (r.precedence p).earlier.val ∧ e.later = (r.precedence p).later.val

def UtilityOk (pool : List Ref) (j : Fin r.nu) (e : UtilityEntry) : Prop :=
  e.name = (r.utilities j).name ∧ pool[e.utilityRef]? = some (r.utilities j).ref ∧
    SlotsMatch (fun q => (r.utilityInputs q).utility = j) (fun q => (r.utilityInputs q).position)
      (fun q => (r.utilityInputs q).var.val) e.inputs ∧
    e.table.axes = e.inputs.map Slot.var ∧ Layout r e.table

/-- `u` must precede `v`: a mechanism input, an information arc or a precedence arc (between
action variables) of Julia's `information_graph`. -/
def Arc (u v : Nat) : Prop :=
  (∃ i : Fin r.ni, (r.inputs i).var.val = u ∧
      (r.mechanisms (r.inputs i).mechanism).target.val = v) ∨
    (∃ f : Fin r.nf, (r.information f).var.val = u ∧
      (r.decisions (r.information f).decision).action.val = v) ∨
    ∃ p : Fin r.np, (r.decisions (r.precedence p).earlier).action.val = u ∧
      (r.decisions (r.precedence p).later).action.val = v

/-- An evidence variable must precede every action (the evidence prefix). -/
def EvidenceArc (hard : List HardEntry) (u v : Nat) : Prop :=
  (∃ e ∈ hard, e.var = u) ∧ ∃ d : Fin r.nd, (r.decisions d).action.val = v

/-- The information set of a decision, as `compile` builds it. -/
def infoSet (d : Fin r.nd) : Finset (Fin r.nv) :=
  (Finset.univ.filter fun f => (r.information f).decision = d).image fun f => (r.information f).var

/-- No-forgetting between an earlier decision `e` and a later decision `l`. -/
def Remembers (e l : Nat) : Prop :=
  ∀ (he : e < r.nd) (hl : l < r.nd),
    insert (r.decisions ⟨e, he⟩).action (infoSet r ⟨e, he⟩) ⊆ infoSet r ⟨l, hl⟩

/-- The decision of an action variable. -/
def decisionOf (v : Nat) : Option Nat :=
  ((List.finRange r.nd).find? fun d => decide ((r.decisions d).action.val = v)).map Fin.val

/-- A value is finite, reduced, and (with both parts) its word is its rational's rounding. -/
def ValueOk : Value → Prop
  | .f64 w => Binary64.field w ≠ 2047
  | .q n d => Nat.Coprime n.natAbs d
  | .qf64 n d w => Nat.Coprime n.natAbs d ∧ Binary64.field w ≠ 2047 ∧
      (Binary64.nearestBinary64 ((n : ℚ) / d) = w ∨ ((n : ℚ) / d = 0 ∧ Binary64.value w = 0))

/-- The shape of a value under the numeric mode. -/
def ShapeOk (num : Numeric) : Value → Prop
  | .f64 _ => num.mode = "binary64_exact" ∧ num.runtimeBits = true
  | .q _ _ => num.mode = "rational_exact" ∧ num.runtimeBits = false
  | .qf64 _ _ _ => num.mode = "rational_exact" ∧ num.runtimeBits = true

end Spec

open Spec

/-! ## The checker -/

/-- **The certificate describes the checked diagram `r`** (see the module documentation). -/
structure Matches (r : Diagram) (c : Certificate) : Prop where
  vars_length : c.vars.length = r.nv
  vars : ∀ v : Fin r.nv, OptHolds (VariableOk r c.pool v) c.vars[v.val]?
  mechanisms_length : c.mechanisms.length = r.nm
  mechanisms : ∀ m : Fin r.nm, OptHolds (MechanismOk r c.pool m) c.mechanisms[m.val]?
  decisions_length : c.decisions.length = r.nd
  decisions : ∀ d : Fin r.nd, OptHolds (DecisionOk r d) c.decisions[d.val]?
  precedence_length : c.precedence.length = r.np
  precedence : ∀ p : Fin r.np, OptHolds (PrecedenceOk r p) c.precedence[p.val]?
  utilities_length : c.utilities.length = r.nu
  utilities : ∀ j : Fin r.nu, OptHolds (UtilityOk r c.pool j) c.utilities[j.val]?
  topo_length : c.topological.length = r.nv
  topo_nodup : c.topological.Nodup
  topo_range : ∀ v ∈ c.topological, v < r.nv
  topo_order : c.topological.Pairwise fun a b => ¬ Arc r b a ∧ ¬ EvidenceArc r c.hard b a
  order_length : c.decisionOrder.length = r.nd
  order_nodup : c.decisionOrder.Nodup
  order_range : ∀ d ∈ c.decisionOrder, d < r.nd
  order_topological : c.decisionOrder = c.topological.filterMap (decisionOf r)
  no_forgetting : c.decisionOrder.Pairwise (Remembers r)
  evidence_sorted : (c.hard.map HardEntry.var).Pairwise (· < ·)
  evidence_range : ∀ e ∈ c.hard, e.stateIndex < dim r e.var ∧ ∀ d : Fin r.nd,
    (r.decisions d).action.val ≠ e.var
  pool_nodup : c.pool.Nodup
  pool_used : ∀ k : Fin c.pool.length, (∃ e ∈ c.vars, e.spaceRef = k.val) ∨
    (∃ e ∈ c.mechanisms, e.kernelRef = k.val) ∨ ∃ e ∈ c.utilities, e.utilityRef = k.val
  normalization : c.numeric.normalization = "none"
  shapes : ∀ x ∈ allValues c, ShapeOk c.numeric x
  values : ∀ x ∈ allValues c, ValueOk x
  tolerances : Binary64.field c.tolerances.kernel ≠ 2047 ∧
    Binary64.field c.tolerances.decision ≠ 2047

/-- `Matches` as one conjunction, for its decision procedure. -/
theorem matches_iff (r : Diagram) (c : Certificate) : Matches r c ↔
    c.vars.length = r.nv ∧ (∀ v : Fin r.nv, OptHolds (VariableOk r c.pool v) c.vars[v.val]?) ∧
    c.mechanisms.length = r.nm ∧
    (∀ m : Fin r.nm, OptHolds (MechanismOk r c.pool m) c.mechanisms[m.val]?) ∧
    c.decisions.length = r.nd ∧ (∀ d : Fin r.nd, OptHolds (DecisionOk r d) c.decisions[d.val]?) ∧
    c.precedence.length = r.np ∧
    (∀ p : Fin r.np, OptHolds (PrecedenceOk r p) c.precedence[p.val]?) ∧
    c.utilities.length = r.nu ∧
    (∀ j : Fin r.nu, OptHolds (UtilityOk r c.pool j) c.utilities[j.val]?) ∧
    c.topological.length = r.nv ∧ c.topological.Nodup ∧ (∀ v ∈ c.topological, v < r.nv) ∧
    c.topological.Pairwise (fun a b => ¬ Arc r b a ∧ ¬ EvidenceArc r c.hard b a) ∧
    c.decisionOrder.length = r.nd ∧ c.decisionOrder.Nodup ∧ (∀ d ∈ c.decisionOrder, d < r.nd) ∧
    c.decisionOrder = c.topological.filterMap (decisionOf r) ∧
    c.decisionOrder.Pairwise (Remembers r) ∧ (c.hard.map HardEntry.var).Pairwise (· < ·) ∧
    (∀ e ∈ c.hard, e.stateIndex < dim r e.var ∧ ∀ d : Fin r.nd,
      (r.decisions d).action.val ≠ e.var) ∧
    c.pool.Nodup ∧
    (∀ k : Fin c.pool.length, (∃ e ∈ c.vars, e.spaceRef = k.val) ∨
      (∃ e ∈ c.mechanisms, e.kernelRef = k.val) ∨ ∃ e ∈ c.utilities, e.utilityRef = k.val) ∧
    c.numeric.normalization = "none" ∧ (∀ x ∈ allValues c, ShapeOk c.numeric x) ∧
    (∀ x ∈ allValues c, ValueOk x) ∧
    (Binary64.field c.tolerances.kernel ≠ 2047 ∧ Binary64.field c.tolerances.decision ≠ 2047) := by
  constructor
  · intro h
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16,
      h.17, h.18, h.19, h.20, h.21, h.22, h.23, h.24, h.25, h.26, h.27⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27⟩

section Decidable

variable (r : Diagram)

instance (e l : Nat) : Decidable (Remembers r e l) := by unfold Remembers; infer_instance

instance (u v : Nat) : Decidable (Arc r u v) := by unfold Arc; infer_instance

instance (hard : List HardEntry) (u v : Nat) : Decidable (EvidenceArc r hard u v) := by
  unfold EvidenceArc; infer_instance

instance {n : Nat} (sel : Fin n → Prop) [DecidablePred sel] (pos : Fin n → Nat)
    (var : Fin n → Nat) (l : List Slot) : Decidable (SlotsMatch sel pos var l) := by
  unfold SlotsMatch; infer_instance

instance (v : Fin r.nv) (l : List StateEntry) : Decidable (StatesMatch r v l) := by
  unfold StatesMatch; infer_instance

instance (t : NumTable) : Decidable (Layout r t) := by unfold Layout; infer_instance

instance (e : MechanismEntry) : Decidable (Diagonal e) := by unfold Diagonal; infer_instance

instance (pool : List Ref) (v : Fin r.nv) (e : VariableEntry) :
    Decidable (VariableOk r pool v e) := by unfold VariableOk; infer_instance

instance (pool : List Ref) (m : Fin r.nm) (e : MechanismEntry) :
    Decidable (MechanismOk r pool m e) := by unfold MechanismOk; infer_instance

instance (d : Fin r.nd) (e : DecisionEntry) : Decidable (DecisionOk r d e) := by
  unfold DecisionOk; infer_instance

instance (p : Fin r.np) (e : PrecedenceEntry) : Decidable (PrecedenceOk r p e) := by
  unfold PrecedenceOk; infer_instance

instance (pool : List Ref) (j : Fin r.nu) (e : UtilityEntry) :
    Decidable (UtilityOk r pool j e) := by unfold UtilityOk; infer_instance

instance (x : Value) : Decidable (ValueOk x) := by cases x <;> unfold ValueOk <;> infer_instance

instance (num : Numeric) (x : Value) : Decidable (ShapeOk num x) := by
  cases x <;> unfold ShapeOk <;> infer_instance

instance (c : Certificate) : Decidable (Matches r c) := decidable_of_iff _ (matches_iff r c).symm

end Decidable

/-- **The checker** of the task statement: the certificate `c` describes the fully valid decoded
diagram `r`. Decidable. -/
def certificateMatches (r : Diagram) (_h : r.FullValid) (c : Certificate) : Prop := Matches r c

instance (r : Diagram) (h : r.FullValid) (c : Certificate) :
    Decidable (certificateMatches r h c) := inferInstanceAs (Decidable (Matches r c))

/-- The CPT cells are nonnegative (decidable over `ℚ`). -/
def Nonneg (c : Certificate) : Prop :=
  ∀ e ∈ c.mechanisms, ∀ x ∈ e.cpt.entries, 0 ≤ x.value.toRat

instance (c : Certificate) : Decidable (Nonneg c) := by unfold Nonneg; infer_instance

/-- Every CPT row sums to exactly one (decidable over `ℚ`): for every parent coordinate row, the
cells over the target's states. -/
def ExactNormalised (r : Diagram) (c : Certificate) : Prop :=
  ∀ m : Fin r.nm, OptHolds (fun e => ∀ row ∈ lexCoords ((e.parents.map Slot.var).map (dim r)),
    ∑ a : Fin (r.stateCount (r.mechanisms m).target), cellValue e.cpt (row ++ [a.val]) = 1)
    c.mechanisms[m.val]?

instance (r : Diagram) (c : Certificate) : Decidable (ExactNormalised r c) := by
  unfold ExactNormalised; infer_instance

/-! ## Structural consequences -/

section Structure

variable {r : Diagram} {c : Certificate}

theorem Spec.SlotsMatch.mem {n : Nat} {sel : Fin n → Prop} [DecidablePred sel] {pos : Fin n → Nat}
    {var : Fin n → Nat} {l : List Slot} (h : SlotsMatch sel pos var l) {s : Slot} (hs : s ∈ l) :
    ∃ i, sel i ∧ s.var = var i := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  obtain ⟨i, hi, -, -, -, hv⟩ := h.2 ⟨j, hj⟩
  exact ⟨i, hi, hv⟩

/-- **The certificate's state rows are the label order of the label-order theorems**: the row at
index `a` of variable `v` has position `a + 1` and the label `stateLabel a`. -/
theorem Matches.stateLabel (hm : Matches r c) (h : r.Valid) (v : Fin r.nv)
    (a : Fin (r.stateCount v)) :
    OptHolds (fun e => ∃ ha : a.val < e.states.length,
      e.states[a.val].label = r.stateLabel h v a ∧ e.states[a.val].position = a.val + 1)
      c.vars[v.val]? := by
  have hv := hm.vars v
  cases hc : c.vars[v.val]? with
  | none => rw [hc] at hv; exact hv
  | some e =>
    rw [hc] at hv
    change VariableOk r c.pool v e at hv
    obtain ⟨hlen, hst⟩ := hv.2.2.2
    have ha : a.val < e.states.length := by rw [hlen]; exact a.isLt
    obtain ⟨s, hsv, hsp, -, hpos, hlab⟩ := hst ⟨a.val, ha⟩
    have hrec : r.stateRecord h v a = s :=
      h.state_positions.2 _ _ ((r.stateRecord_var h v a).trans hsv.symm)
        ((r.stateRecord_position h v a).trans hsp.symm)
    refine ⟨ha, ?_, hpos⟩
    show _ = (r.states (r.stateRecord h v a)).name
    rw [hrec]
    exact hlab

/-- **The certificate's information slots are the information rows in position order**: slot `j`
of decision `d` has the variable of every (by `FullValid`, the unique) information row of `d` at
position `j`. -/
theorem Matches.information (hm : Matches r c) (h : r.FullValid) (d : Fin r.nd) :
    OptHolds (fun e => ∀ (j : Nat) (hj : j < e.information.length) (f : Fin r.nf),
      (r.information f).decision = d → (r.information f).position = j →
        e.information[j].var = (r.information f).var.val) c.decisions[d.val]? := by
  have hd := hm.decisions d
  cases hc : c.decisions[d.val]? with
  | none => rw [hc] at hd; exact hd
  | some e =>
    rw [hc] at hd
    change DecisionOk r d e at hd
    have hsl := hd.2.2.2
    intro j hj f hfd hfp
    obtain ⟨f', hf'd, hf'p, -, -, hvar⟩ := hsl ⟨j, hj⟩
    have : f' = f := h.information_positions.2 f' f (hf'd.trans hfd.symm) (hf'p.trans hfp.symm)
    subst this
    exact hvar

end Structure

/-! ## The certificate's model -/

section Model

variable (r : Diagram) (h : r.Valid) (c : Certificate)

/-- The coordinates of an assignment along a list of variable indices. -/
def coordsOf (x : (r.compile h).Assignment) (vs : List Nat) : List Nat :=
  vs.map fun v => if hv : v < r.nv then (x ⟨v, hv⟩).val else 0

/-- **The certificate's kernel**: the exact CPT cell at the parents' coordinates and the target's
state. -/
noncomputable def certKernel : (r.compile h).Kernel ℝ := fun m x a =>
  match c.mechanisms[m.val]? with
  | some e => ((cellValue e.cpt (coordsOf r h x (e.parents.map Slot.var) ++ [a.val]) : ℚ) : ℝ)
  | none => 0

/-- **The certificate's utilities**: the exact utility cell at the scope's coordinates. -/
noncomputable def certUtility : Utility (r.compile h) ℝ := fun j x =>
  match c.utilities[j.val]? with
  | some e => ((cellValue e.table (coordsOf r h x (e.inputs.map Slot.var)) : ℚ) : ℝ)
  | none => 0

end Model

section ModelFacts

variable {r : Diagram} {c : Certificate}

theorem coordsOf_congr (h : r.Valid) {x x' : (r.compile h).Assignment} {vs : List Nat}
    (hx : ∀ v ∈ vs, ∀ hv : v < r.nv, x ⟨v, hv⟩ = x' ⟨v, hv⟩) :
    coordsOf r h x vs = coordsOf r h x' vs := by
  unfold coordsOf
  refine List.map_congr_left fun v hv => ?_
  split_ifs with hlt
  · rw [hx v hv hlt]
  · rfl

theorem certKernel_local (hm : Matches r c) (h : r.Valid) (m : Fin r.nm) :
    Local (certKernel r h c) m := by
  intro x x' hxx
  funext a
  unfold certKernel
  have hmo := hm.mechanisms m
  cases hc : c.mechanisms[m.val]? with
  | none => rfl
  | some e =>
    rw [hc] at hmo
    change MechanismOk r c.pool m e at hmo
    have hsl := hmo.2.2.2.1
    simp only
    rw [coordsOf_congr h (x := x) (x' := x')]
    intro v hv hlt
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hv
    obtain ⟨i, hi, hvar⟩ := hsl.mem hs
    apply hxx
    refine Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, ?_⟩
    exact Fin.ext hvar.symm

theorem certUtility_local (hm : Matches r c) (h : r.Valid) (j : Fin r.nu) :
    Utility.Local (certUtility r h c) j := by
  intro x x' hxx
  unfold certUtility
  have huo := hm.utilities j
  cases hc : c.utilities[j.val]? with
  | none => rfl
  | some e =>
    rw [hc] at huo
    change UtilityOk r c.pool j e at huo
    have hsl := huo.2.2.1
    simp only
    rw [coordsOf_congr h (x := x) (x' := x')]
    intro v hv hlt
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hv
    obtain ⟨i, hi, hvar⟩ := hsl.mem hs
    apply hxx
    refine Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, ?_⟩
    exact Fin.ext hvar.symm

theorem cellValue_nonneg {t : NumTable} (ht : ∀ x ∈ t.entries, 0 ≤ x.value.toRat)
    (coords : List Nat) : 0 ≤ cellValue t coords := by
  unfold cellValue lookup
  cases hf : t.entries.find? (fun e => decide (e.coords = coords)) with
  | none => simp
  | some e =>
    simp only [Option.map_some, Option.getD_some]
    exact ht e (List.mem_of_find?_eq_some hf)

theorem certKernel_nonneg (hn : Nonneg c) (h : r.Valid) (m : Fin r.nm)
    (x : (r.compile h).Assignment) (a : (r.compile h).states ((r.compile h).target m)) :
    0 ≤ certKernel r h c m x a := by
  unfold certKernel
  cases hc : c.mechanisms[m.val]? with
  | none => exact le_refl 0
  | some e =>
    simp only
    exact_mod_cast cellValue_nonneg (hn e (List.mem_of_getElem? hc)) _

theorem certKernel_normalised (hm : Matches r c) (hnorm : ExactNormalised r c) (h : r.Valid)
    (m : Fin r.nm) : Normalised (certKernel r h c) m := by
  intro x
  have hmo := hm.mechanisms m
  have hno := hnorm m
  unfold certKernel
  cases hc : c.mechanisms[m.val]? with
  | none => rw [hc] at hmo; exact absurd hmo id
  | some e =>
    rw [hc] at hmo hno
    change MechanismOk r c.pool m e at hmo
    have hsl := hmo.2.2.2.1
    simp only
    have hrow : coordsOf r h x (e.parents.map Slot.var) ∈
        lexCoords ((e.parents.map Slot.var).map (dim r)) := by
      rw [mem_lexCoords, coordsOf, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
        List.forall₂_same]
      intro v hv
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hv
      obtain ⟨i, -, hvar⟩ := hsl.mem hs
      have hlt : s.var < r.nv := hvar ▸ (r.inputs i).var.isLt
      simp only [dif_pos hlt, dim]
      exact (x ⟨s.var, hlt⟩).isLt
    have := congrArg (fun q : ℚ => (q : ℝ)) (hno _ hrow)
    simpa only [Rat.cast_sum, Rat.cast_one] using this

/-! ## The certificate's orders -/

theorem mem_of_nodup_length {l : List Nat} {n : Nat} (hn : l.Nodup) (hl : l.length = n)
    (hr : ∀ v ∈ l, v < n) (v : Nat) (hv : v < n) : v ∈ l := by
  by_contra hnot
  have hsub : l.toFinset ⊆ (Finset.range n).erase v := by
    intro x hx
    rw [List.mem_toFinset] at hx
    rw [Finset.mem_erase, Finset.mem_range]
    exact ⟨fun he => hnot (he ▸ hx), hr x hx⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn, Finset.card_erase_of_mem (Finset.mem_range.2 hv),
    Finset.card_range] at this
  omega

/-- **The certificate's `topological_order` is an `IDOrder` of the compiled diagram.** -/
def certOrder (hm : Matches r c) (h : r.FullValid) : (r.compile h.valid).IDOrder where
  order := c.topological.pmap Fin.mk hm.topo_range
  nodup := List.Nodup.pmap (fun _ _ _ _ he => Fin.val_eq_of_eq he) hm.topo_nodup
  complete v := List.mem_pmap.2 ⟨v.val,
    mem_of_nodup_length hm.topo_nodup hm.topo_length hm.topo_range v.val v.isLt, rfl⟩
  parents_before := by
    refine (List.pairwise_pmap _).2 (hm.topo_order.imp fun {a b} hab ha hb m hma hbm => ?_)
    obtain ⟨i, hi, he⟩ := Finset.mem_image.1 hbm
    apply hab.1
    refine Or.inl ⟨i, congrArg Fin.val he, ?_⟩
    have hmi : (r.inputs i).mechanism = m := (Finset.mem_filter.1 hi).2
    rw [hmi]
    exact congrArg Fin.val hma
  info_before_action := by
    refine (List.pairwise_pmap _).2 (hm.topo_order.imp fun {a b} hab ha hb d hda hbd => ?_)
    obtain ⟨f, hf, he⟩ := Finset.mem_image.1 hbd
    apply hab.1
    refine Or.inr (Or.inl ⟨f, congrArg Fin.val he, ?_⟩)
    have hdf : (r.information f).decision = d := (Finset.mem_filter.1 hf).2
    rw [hdf]
    exact congrArg Fin.val hda
  no_self := h.idOrder.no_self
  no_self_info := h.idOrder.no_self_info

/-- **The certificate's `decision_order` is a `NoForgettingOrder` of the compiled diagram.** -/
def certNoForgetting (hm : Matches r c) (h : r.FullValid) :
    DVE.NoForgettingOrder (r.compile h.valid) where
  reverseDecisions := (c.decisionOrder.pmap Fin.mk hm.order_range).reverse
  nodup := List.nodup_reverse.2 (List.Nodup.pmap (fun _ _ _ _ he => Fin.val_eq_of_eq he)
    hm.order_nodup)
  complete d := List.mem_reverse.2 (List.mem_pmap.2 ⟨d.val,
    mem_of_nodup_length hm.order_nodup hm.order_length hm.order_range d.val d.isLt, rfl⟩)
  remembers := by
    rw [List.pairwise_reverse]
    exact (List.pairwise_pmap _).2 (hm.no_forgetting.imp fun {a b} hab ha hb => hab ha hb)

end ModelFacts

/-! ## Soundness -/

section Soundness

variable (r : Diagram) (h : r.FullValid) (c : Certificate)

/-- **Tables of the certificate's exact data.** If the certificate matches the checked diagram and
its CPT cells are nonnegative, then Julia's sum-out representative run on the certificate's exact
kernel and utilities, with any plan and any zero-row representative choice, returns on every
information row the action of least `state_position` among the maximizers of the run's own
score. -/
theorem certificate_tables (hm : certificateMatches r h c) (hn : Nonneg c)
    (keep : (r.compile h.valid).V → Bool) (plan : DVE.Plan (r.compile h.valid) Finset.univ)
    (d : (r.compile h.valid).D) (x : (r.compile h.valid).Assignment) :
    ∃ t, (∀ a, ((DVE.solveRepPlanWith (r.selector h.valid) keep (certKernel r h.valid c)
          (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
          (certUtility_local hm h.valid) plan).strategy d).kernel x a = if a = t then 1 else 0) ∧
      (∀ b, DVE.solveRepPlanScore keep (certKernel r h.valid c) (certKernel_local hm h.valid)
          (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid)
          plan d x b ≤
        DVE.solveRepPlanScore keep (certKernel r h.valid c) (certKernel_local hm h.valid)
          (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid)
          plan d x t) ∧
      ∀ b, (∀ c', DVE.solveRepPlanScore keep (certKernel r h.valid c) (certKernel_local hm h.valid)
            (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
            (certUtility_local hm h.valid) plan d x c' ≤
          DVE.solveRepPlanScore keep (certKernel r h.valid c) (certKernel_local hm h.valid)
            (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
            (certUtility_local hm h.valid) plan d x b) →
        r.statePosition h.valid _ t ≤ r.statePosition h.valid _ b :=
  r.solveRepRecords_table_of_fullValid h keep _ _ _ _ _ plan d x

/-- **Optimality on the certificate's exact data.** If moreover every CPT row sums to exactly one,
the DVE solution scheduled by the certificate's `decision_order` (with its `topological_order`
as the order) is deterministic, realizes its reported value, and that value is the global
optimum of the certificate's model over all strategies. -/
theorem certificate_solve_spec (hm : certificateMatches r h c) (hn : Nonneg c)
    (hnorm : ExactNormalised r c) :
    let sol := DVE.solve (certKernel r h.valid c) (certKernel_local hm h.valid)
      (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid)
      (certOrder hm h) (certNoForgetting hm h)
    sol.strategy.Deterministic ∧
      expectedUtility (certKernel r h.valid c) sol.strategy (certUtility r h.valid c) = sol.value ∧
      sol.value = optimalValue (certKernel r h.valid c) (certUtility r h.valid c) :=
  DVE.solve_spec _ h.closed _ _ (certKernel_local hm h.valid) (certKernel_normalised hm hnorm h.valid)
    (certKernel_nonneg hn h.valid) _ (certUtility_local hm h.valid)

/-- **First-label optimal tables on the certificate's exact data**: with exactly normalised
nonnegative CPTs, every representative run's table entry, at every row of positive reach, is the
action of least `state_position` among the maximizers of the optimal continuation value. -/
theorem certificate_tables_optimal (hm : certificateMatches r h c) (hn : Nonneg c)
    (hnorm : ExactNormalised r c) (keep : (r.compile h.valid).V → Bool)
    (plan : DVE.Plan (r.compile h.valid) Finset.univ) (d : (r.compile h.valid).D)
    (x : (r.compile h.valid).Assignment) (ρ : Strategy (r.compile h.valid) ℝ)
    (hx : DVE.reach (certKernel r h.valid c) (fun _ => 1) ρ d x ≠ 0) :
    ∃ t, (∀ a, ((DVE.solveRepPlanWith (r.selector h.valid) keep (certKernel r h.valid c)
          (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
          (certUtility_local hm h.valid) plan).strategy d).kernel x a = if a = t then 1 else 0) ∧
      (∀ b, DVE.optimalContinuation (certKernel r h.valid c) (certUtility r h.valid c)
          (fun _ => 1) d x b ≤
        DVE.optimalContinuation (certKernel r h.valid c) (certUtility r h.valid c)
          (fun _ => 1) d x t) ∧
      ∀ b, (∀ c', DVE.optimalContinuation (certKernel r h.valid c) (certUtility r h.valid c)
            (fun _ => 1) d x c' ≤
          DVE.optimalContinuation (certKernel r h.valid c) (certUtility r h.valid c)
            (fun _ => 1) d x b) →
        r.statePosition h.valid _ t ≤ r.statePosition h.valid _ b :=
  r.solveRepRecords_optimal_of_fullValid h keep _ _ (certKernel_normalised hm hnorm h.valid) _ _
    _ plan d x ρ hx

end Soundness

end InfluenceDiagramsProofs.DVECertificate
