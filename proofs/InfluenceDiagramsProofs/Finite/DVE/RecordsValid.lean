import InfluenceDiagramsProofs.Finite.DVE.LabelOrder
import BayesianNetworksProofs.Finite.JsonRecords
import Mathlib.Algebra.BigOperators.Fin

/-!
# Full validity of influence-diagram records

`Records.Diagram.Valid` checks only the state rows, which is all the label-order theorems of
`LabelOrder.lean` read. `FullValid` checks every table, the decidable counterpart of what
BayesianNetworks' `Raw.Network.Valid` checks for a network:

* the state rows (`Valid`): bounded unique positions per variable, a state for every variable,
  unique labels per variable;
* the `Input`, `InformationInput` and `UtilityInput` rows: bounded unique positions per mechanism,
  per decision and per utility (`Raw.Positioned`);
* the generators: mechanism targets and decision actions are injective, disjoint, and cover the
  variables (every variable has exactly one generator);
* acyclicity: some injective rank puts every mechanism input below the mechanism's target and
  every information variable below the decision's action (`chance.Acyclic`, decided by the
  proved placement of `Raw.Tables.computeRank`);
* decision precedence: some injective rank does all that and also puts the action of every
  `DecisionPrecedence` row's `earlier` decision below the action of its `later` decision
  (`informationTables.Acyclic`). These ranks are the topological orders of Julia's
  `information_graph`, which adds one arc per precedence row (earlier action to later action) to
  the causal and information arcs; `validate` reports a cycle in it, or in the precedence rows
  alone, as `DecisionPrecedenceCycleError` (or as a `:downstream` information error).

`chance` is the chance part with every decision instantiated as a mechanism, as Julia's
`instantiate` does: decision `d` becomes the mechanism `nm + d` named `policy[name]` with kernel
reference `PolicyRef(name)`, targeting the action, whose inputs are the information rows of `d`
with their positions. `FullValid.chance_valid`: the instantiated rows satisfy `Raw.Tables.Valid`,
so `chance_network_valid` gives a BN `Raw.Network` satisfying `Raw.Network.Valid`.

From `FullValid` the compiled diagram is closed (`FullValid.closed`) and has an `IDOrder`
(`FullValid.idOrder`, from the computed rank). The label-order theorems then lose those
hypotheses: `solveRepRecords_table_of_fullValid` (no `Closed`),
`solveRepRecords_optimal_of_fullValid` and `solveRecords_table_of_fullValid` (neither `Closed`
nor `IDOrder`). The original theorems, under `Valid` with the hypotheses, are unchanged.

Julia's `validate` (`InfluenceDiagrams.jl/src/validation.jl`) checks the `DecisionPrecedence` rows
in three ways, and `FullValid` mirrors each: both IDs in `1..nDecision` (`DanglingReferenceError`;
here by the type `Fin nd`, which the decoder enforces), the precedence rows alone acyclic
(`_check_precedence!`, Kahn's algorithm on the decisions; a self-loop is a cycle), and the
combined graph acyclic (`_check_information_order!`). Duplicate rows are allowed by both (Graphs'
`add_edge!` ignores a repeated arc; a repeated rank inequality is harmless), and no other
precedence check exists. `FullValid.precedence_rank` derives the decision-only acyclicity and
`FullValid.precedence_irrefl` the absence of self-loops.

`NamesUnique` is the separate, decidable check of `validate(...; unique_names = true)`: variable
and mechanism names (BayesianNetworks' `_check_unique_names!`) and decision and utility names
(`_check_id_names!`) unique; Julia leaves it off by default, and so does `FullValid`.

Not checked: the no-forgetting condition (`NoForgettingOrder` stays a hypothesis).
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram
open BayesianNetworksProofs.Raw

namespace Records

/-! ## Positions over an appended table -/

theorem castAdd_ne_natAdd {a b : Nat} (i : Fin a) (j : Fin b) :
    Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

/-- The owner map of two tables appended, the second's owners shifted past the first's. -/
def appendOwner {n1 n2 o1 o2 : Nat} (own1 : Fin n1 → Fin o1) (own2 : Fin n2 → Fin o2) :
    Fin (n1 + n2) → Fin (o1 + o2) :=
  Fin.append (fun i => Fin.castAdd o2 (own1 i)) (fun j => Fin.natAdd o1 (own2 j))

theorem card_fibre_left {n1 n2 o1 o2 : Nat} (own1 : Fin n1 → Fin o1) (own2 : Fin n2 → Fin o2)
    (o : Fin o1) :
    Fintype.card {s : Fin (n1 + n2) // appendOwner own1 own2 s = Fin.castAdd o2 o} =
      Fintype.card {s : Fin n1 // own1 s = o} := by
  rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_add]
  simp only [appendOwner, Fin.append_left, Fin.append_right]
  have h1 : ∀ i, (Fin.castAdd o2 (own1 i) = Fin.castAdd o2 o) ↔ own1 i = o :=
    fun i => (Fin.castAdd_injective o1 o2).eq_iff
  have h2 : ∀ j, ¬ (Fin.natAdd o1 (own2 j) = Fin.castAdd o2 o) :=
    fun j h => castAdd_ne_natAdd o (own2 j) h.symm
  simp [h1, h2]

theorem card_fibre_right {n1 n2 o1 o2 : Nat} (own1 : Fin n1 → Fin o1) (own2 : Fin n2 → Fin o2)
    (o : Fin o2) :
    Fintype.card {s : Fin (n1 + n2) // appendOwner own1 own2 s = Fin.natAdd o1 o} =
      Fintype.card {s : Fin n2 // own2 s = o} := by
  rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_add]
  simp only [appendOwner, Fin.append_left, Fin.append_right]
  have h1 : ∀ i, ¬ (Fin.castAdd o2 (own1 i) = Fin.natAdd o1 o) :=
    fun i h => castAdd_ne_natAdd (own1 i) o h
  have h2 : ∀ j, (Fin.natAdd o1 (own2 j) = Fin.natAdd o1 o) ↔ own2 j = o :=
    fun j => (Fin.natAdd_injective o2 o1).eq_iff
  simp [h1, h2]

/-- Bounded unique positions on both tables give bounded unique positions on the appended table. -/
theorem positioned_append {n1 n2 o1 o2 : Nat} {own1 : Fin n1 → Fin o1} {own2 : Fin n2 → Fin o2}
    {pos1 : Fin n1 → Nat} {pos2 : Fin n2 → Nat} (h1 : Positioned own1 pos1)
    (h2 : Positioned own2 pos2) : Positioned (appendOwner own1 own2) (Fin.append pos1 pos2) := by
  refine ⟨fun r => ?_, fun r s => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) r
    · have hc := card_fibre_left own1 own2 (own1 i)
      have hlt := h1.1 i
      simp only [appendOwner, Fin.append_left] at hc ⊢
      convert hlt using 1
    · have hc := card_fibre_right own1 own2 (own2 j)
      have hlt := h2.1 j
      simp only [appendOwner, Fin.append_right] at hc ⊢
      convert hlt using 1
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) r <;>
      refine Fin.addCases (fun i' => ?_) (fun j' => ?_) s <;>
      simp only [appendOwner, Fin.append_left, Fin.append_right]
    · intro ho hp
      rw [h1.2 i i' ((Fin.castAdd_injective o1 o2) ho) hp]
    · intro ho
      exact absurd ho (castAdd_ne_natAdd _ _)
    · intro ho
      exact absurd ho.symm (castAdd_ne_natAdd _ _)
    · intro ho hp
      rw [h2.2 j j' ((Fin.natAdd_injective o2 o1) ho) hp]

namespace Diagram

/-! ## The instantiated chance part -/

/-- The mechanism a decision becomes under `instantiate`: target the action, named
`policy[name]`, with kernel reference `PolicyRef(name)`. -/
def policyMechanism {nv : Nat} (d : DecisionRow nv) : MechanismRow nv :=
  ⟨d.action, "policy[" ++ d.name ++ "]", .policy d.name⟩

/-- **The chance part with every decision instantiated**: the BN rows of the diagram, plus one
policy mechanism per decision (after the chance mechanisms) whose inputs are the decision's
information rows (after the chance inputs), positions kept. -/
def chance (r : Diagram) : Raw.Tables where
  nv := r.nv
  ns := r.ns
  nm := r.nm + r.nd
  ni := r.ni + r.nf
  vars := r.vars
  states := r.states
  mechanisms := Fin.append r.mechanisms fun d => policyMechanism (r.decisions d)
  inputs := Fin.append
    (fun i => ⟨Fin.castAdd r.nd (r.inputs i).mechanism, (r.inputs i).var, (r.inputs i).position⟩)
    (fun f => ⟨Fin.natAdd r.nm (r.information f).decision, (r.information f).var,
      (r.information f).position⟩)

theorem chance_target_left (r : Diagram) (m : Fin r.nm) :
    (r.chance.mechanisms (Fin.castAdd r.nd m)).target = (r.mechanisms m).target := by
  simp [chance]

theorem chance_target_right (r : Diagram) (d : Fin r.nd) :
    (r.chance.mechanisms (Fin.natAdd r.nm d)).target = (r.decisions d).action := by
  simp [chance, policyMechanism]

theorem chance_input_left (r : Diagram) (i : Fin r.ni) :
    r.chance.inputs (Fin.castAdd r.nf i) =
      ⟨Fin.castAdd r.nd (r.inputs i).mechanism, (r.inputs i).var, (r.inputs i).position⟩ := by
  simp [chance]

theorem chance_input_right (r : Diagram) (f : Fin r.nf) :
    r.chance.inputs (Fin.natAdd r.ni f) =
      ⟨Fin.natAdd r.nm (r.information f).decision, (r.information f).var,
        (r.information f).position⟩ := by
  simp [chance]

/-- The acyclicity of the instantiated chance part, unpacked: one injective rank orders every
mechanism input before its target and every information variable before its action. -/
theorem chance_acyclic_iff (r : Diagram) : r.chance.Acyclic ↔
    ∃ rank : Fin r.nv → Fin r.nv, Function.Injective rank ∧
      (∀ i, rank (r.inputs i).var < rank (r.mechanisms (r.inputs i).mechanism).target) ∧
      ∀ f, rank (r.information f).var < rank (r.decisions (r.information f).decision).action := by
  constructor
  · rintro ⟨rank, hinj, hc⟩
    refine ⟨rank, hinj, fun i => ?_, fun f => ?_⟩
    · have := hc (Fin.castAdd r.nf i)
      rw [chance_input_left] at this
      simpa [chance_target_left] using this
    · have := hc (Fin.natAdd r.ni f)
      rw [chance_input_right] at this
      simpa [chance_target_right] using this
  · rintro ⟨rank, hinj, hi, hf⟩
    refine ⟨rank, hinj, fun k => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun f => ?_) k
    · rw [chance_input_left]
      simpa [chance_target_left] using hi i
    · rw [chance_input_right]
      simpa [chance_target_right] using hf f

/-! ## Decision precedence -/

/-- **The information graph as tables**: the instantiated chance part with one more input per
`DecisionPrecedence` row, by which the policy mechanism of `later` reads the action of `earlier`
(at position `0`; only the rank conditions read these rows). Its causal ranks are exactly the
topological orders of Julia's `information_graph` (`informationTables_causalRank_iff`). -/
def informationTables (r : Diagram) : Raw.Tables where
  nv := r.nv
  ns := r.ns
  nm := r.nm + r.nd
  ni := (r.ni + r.nf) + r.np
  vars := r.vars
  states := r.states
  mechanisms := Fin.append r.mechanisms fun d => policyMechanism (r.decisions d)
  inputs := Fin.append
    (Fin.append
      (fun i => ⟨Fin.castAdd r.nd (r.inputs i).mechanism, (r.inputs i).var, (r.inputs i).position⟩)
      (fun f => ⟨Fin.natAdd r.nm (r.information f).decision, (r.information f).var,
        (r.information f).position⟩))
    (fun p => ⟨Fin.natAdd r.nm (r.precedence p).later, (r.decisions (r.precedence p).earlier).action,
      0⟩)

theorem informationTables_input_left (r : Diagram) (k : Fin (r.ni + r.nf)) :
    r.informationTables.inputs (Fin.castAdd r.np k) = r.chance.inputs k := by
  simp [informationTables, chance]

theorem informationTables_input_right (r : Diagram) (p : Fin r.np) :
    r.informationTables.inputs (Fin.natAdd (r.ni + r.nf) p) =
      ⟨Fin.natAdd r.nm (r.precedence p).later, (r.decisions (r.precedence p).earlier).action, 0⟩ := by
  simp [informationTables]

theorem informationTables_mechanisms (r : Diagram) :
    r.informationTables.mechanisms = r.chance.mechanisms := rfl

/-- A causal rank of the information tables is a causal rank of the instantiated chance part that
also orders every precedence row's earlier action below its later action. -/
theorem informationTables_causalRank_iff (r : Diagram) (rank : Fin r.nv → Fin r.nv) :
    r.informationTables.CausalRank rank ↔ r.chance.CausalRank rank ∧
      ∀ p, rank (r.decisions (r.precedence p).earlier).action <
        rank (r.decisions (r.precedence p).later).action := by
  constructor
  · rintro ⟨hinj, hc⟩
    refine ⟨⟨hinj, fun k => ?_⟩, fun p => ?_⟩
    · have := hc (Fin.castAdd r.np k)
      rw [informationTables_input_left] at this
      exact this
    · have := hc (Fin.natAdd (r.ni + r.nf) p)
      rw [informationTables_input_right] at this
      rw [informationTables_mechanisms] at this
      simpa only [chance_target_right] using this
  · rintro ⟨⟨hinj, hc⟩, hp⟩
    refine ⟨hinj, fun k => ?_⟩
    refine Fin.addCases (fun k => ?_) (fun p => ?_) k
    · rw [informationTables_input_left]
      exact hc k
    · rw [informationTables_input_right, informationTables_mechanisms]
      simpa only [chance_target_right] using hp p

/-- The acyclicity of the information graph, unpacked: one injective rank orders every mechanism
input before its target, every information variable before its action, and every precedence
row's earlier action before its later action. -/
theorem informationTables_acyclic_iff (r : Diagram) : r.informationTables.Acyclic ↔
    ∃ rank : Fin r.nv → Fin r.nv, Function.Injective rank ∧
      (∀ i, rank (r.inputs i).var < rank (r.mechanisms (r.inputs i).mechanism).target) ∧
      (∀ f, rank (r.information f).var < rank (r.decisions (r.information f).decision).action) ∧
      ∀ p, rank (r.decisions (r.precedence p).earlier).action <
        rank (r.decisions (r.precedence p).later).action := by
  constructor
  · rintro ⟨rank, hr⟩
    obtain ⟨hc, hp⟩ := (r.informationTables_causalRank_iff rank).1 hr
    refine ⟨rank, hc.1, fun i => ?_, fun f => ?_, hp⟩
    · have := hc.2 (Fin.castAdd r.nf i)
      rw [chance_input_left] at this
      simpa [chance_target_left] using this
    · have := hc.2 (Fin.natAdd r.ni f)
      rw [chance_input_right] at this
      simpa [chance_target_right] using this
  · rintro ⟨rank, hinj, hi, hf, hp⟩
    refine ⟨rank, (r.informationTables_causalRank_iff rank).2 ⟨⟨hinj, fun k => ?_⟩, hp⟩⟩
    refine Fin.addCases (fun i => ?_) (fun f => ?_) k
    · rw [chance_input_left]
      simpa [chance_target_left] using hi i
    · rw [chance_input_right]
      simpa [chance_target_right] using hf f

/-- An acyclic information graph has an acyclic instantiated chance part. -/
theorem chance_acyclic_of_informationTables {r : Diagram} (h : r.informationTables.Acyclic) :
    r.chance.Acyclic := by
  obtain ⟨rank, hr⟩ := h
  exact ⟨rank, ((r.informationTables_causalRank_iff rank).1 hr).1⟩

/-! ## Unique names -/

/-- **`validate(...; unique_names = true)`**: variable, mechanism, decision and utility names are
each unique (`DuplicateNameError` otherwise). Not part of `FullValid`, as in Julia, where the
option is off by default. -/
structure NamesUnique (r : Diagram) : Prop where
  variable_names : ∀ v w, (r.vars v).name = (r.vars w).name → v = w
  mechanism_names : ∀ m n, (r.mechanisms m).name = (r.mechanisms n).name → m = n
  decision_names : ∀ d e, (r.decisions d).name = (r.decisions e).name → d = e
  utility_names : ∀ j k, (r.utilities j).name = (r.utilities k).name → j = k

theorem namesUnique_iff (r : Diagram) : r.NamesUnique ↔
    (∀ v w, (r.vars v).name = (r.vars w).name → v = w) ∧
    (∀ m n, (r.mechanisms m).name = (r.mechanisms n).name → m = n) ∧
    (∀ d e, (r.decisions d).name = (r.decisions e).name → d = e) ∧
    ∀ j k, (r.utilities j).name = (r.utilities k).name → j = k :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

instance (r : Diagram) : Decidable r.NamesUnique := decidable_of_iff _ (namesUnique_iff r).symm

def namesCheck (r : Diagram) : Bool := decide r.NamesUnique

theorem namesCheck_iff (r : Diagram) : r.namesCheck = true ↔ r.NamesUnique := by
  simp [namesCheck]

/-! ## Full validity -/

/-- **Every table checked**: the state rows (`Valid`), positions of inputs, information inputs
and utility inputs, the generators (one per variable), acyclicity of the instantiated chance
part, and acyclicity of the information graph with the decision-precedence arcs. All decidable. -/
structure FullValid (r : Diagram) : Prop where
  valid : r.Valid
  input_positions : Positioned (fun i => (r.inputs i).mechanism) (fun i => (r.inputs i).position)
  information_positions :
    Positioned (fun f => (r.information f).decision) (fun f => (r.information f).position)
  utility_positions :
    Positioned (fun q => (r.utilityInputs q).utility) (fun q => (r.utilityInputs q).position)
  targets_injective : Function.Injective fun m => (r.mechanisms m).target
  actions_injective : Function.Injective fun d => (r.decisions d).action
  disjoint : ∀ m d, (r.mechanisms m).target ≠ (r.decisions d).action
  cover : ∀ v, (∃ m, (r.mechanisms m).target = v) ∨ ∃ d, (r.decisions d).action = v
  acyclic : r.chance.Acyclic
  /-- The decision-precedence rows are consistent: Julia's `information_graph` is acyclic. -/
  precedence_acyclic : r.informationTables.Acyclic

theorem fullValid_iff (r : Diagram) : r.FullValid ↔
    r.Valid ∧ Positioned (fun i => (r.inputs i).mechanism) (fun i => (r.inputs i).position) ∧
    Positioned (fun f => (r.information f).decision) (fun f => (r.information f).position) ∧
    Positioned (fun q => (r.utilityInputs q).utility) (fun q => (r.utilityInputs q).position) ∧
    (∀ m m', (r.mechanisms m).target = (r.mechanisms m').target → m = m') ∧
    (∀ d d', (r.decisions d).action = (r.decisions d').action → d = d') ∧
    (∀ m d, (r.mechanisms m).target ≠ (r.decisions d).action) ∧
    (∀ v, (∃ m, (r.mechanisms m).target = v) ∨ ∃ d, (r.decisions d).action = v) ∧
    r.chance.Acyclic ∧ r.informationTables.Acyclic :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, fun _ _ he => h.5 he, fun _ _ he => h.6 he, h.7, h.8, h.9,
      h.10⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun _ _ he => h.2.2.2.2.1 _ _ he,
      fun _ _ he => h.2.2.2.2.2.1 _ _ he, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩⟩

instance (r : Diagram) : Decidable r.FullValid := decidable_of_iff _ (fullValid_iff r).symm

def fullCheck (r : Diagram) : Bool := decide r.FullValid

theorem fullCheck_iff (r : Diagram) : r.fullCheck = true ↔ r.FullValid := by simp [fullCheck]

/-- **The instantiated chance part satisfies BN's row checks and is acyclic.** -/
theorem FullValid.chance_valid {r : Diagram} (h : r.FullValid) : r.chance.Valid := by
  refine ⟨⟨h.valid.state_positions, ?_, h.valid.nonempty_states, h.valid.state_names, ?_⟩,
    h.acyclic⟩
  · have hp := positioned_append h.input_positions h.information_positions
    have howner : (fun k => (r.chance.inputs k).mechanism) =
        appendOwner (fun i => (r.inputs i).mechanism) (fun f => (r.information f).decision) := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun f => ?_) k
      · rw [chance_input_left]
        simp [appendOwner]
      · rw [chance_input_right]
        simp [appendOwner]
    have hpos : (fun k => (r.chance.inputs k).position) =
        Fin.append (fun i => (r.inputs i).position) (fun f => (r.information f).position) := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun f => ?_) k
      · rw [chance_input_left]
        simp
      · rw [chance_input_right]
        simp
    rw [howner, hpos]
    exact hp
  · constructor
    · intro k k' he
      revert he
      refine Fin.addCases (fun m => ?_) (fun d => ?_) k <;>
        refine Fin.addCases (fun m' => ?_) (fun d' => ?_) k' <;>
        simp only [chance_target_left, chance_target_right] <;> intro he
      · rw [h.targets_injective he]
      · exact absurd he (h.disjoint m d')
      · exact absurd he.symm (h.disjoint m' d)
      · rw [h.actions_injective he]
    · intro v
      rcases h.cover v with ⟨m, hm⟩ | ⟨d, hd⟩
      · exact ⟨Fin.castAdd r.nd m, by simp only [chance_target_left]; exact hm⟩
      · exact ⟨Fin.natAdd r.nm d, by simp only [chance_target_right]; exact hd⟩

/-- **The decision-precedence rows alone are acyclic** (Julia's `_check_precedence!`): some
injective rank of the decisions puts every row's `earlier` below its `later`. -/
theorem FullValid.precedence_rank {r : Diagram} (h : r.FullValid) :
    ∃ rank : Fin r.nd → ℕ, Function.Injective rank ∧
      ∀ p, rank (r.precedence p).earlier < rank (r.precedence p).later := by
  obtain ⟨rank, hinj, -, -, hp⟩ := r.informationTables_acyclic_iff.1 h.precedence_acyclic
  refine ⟨fun d => (rank (r.decisions d).action).val, fun d e he => ?_, fun p => hp p⟩
  exact h.actions_injective (hinj (Fin.ext he))

/-- **No precedence row is a self-loop.** -/
theorem FullValid.precedence_irrefl {r : Diagram} (h : r.FullValid) (p : Fin r.np) :
    (r.precedence p).earlier ≠ (r.precedence p).later := by
  obtain ⟨rank, -, hp⟩ := h.precedence_rank
  intro he
  have := hp p
  rw [he] at this
  exact lt_irrefl _ this

/-- **The ID's instantiated chance part is a BN `Raw.Network` satisfying `Raw.Network.Valid`**,
with the computed causal rank. -/
theorem FullValid.chance_network_valid {r : Diagram} (h : r.FullValid) :
    ∃ rank, r.chance.computeRank = some rank ∧ (r.chance.withRank rank).Valid := by
  obtain ⟨hrows, hac⟩ := h.chance_valid
  obtain ⟨rank, hrank⟩ := Tables.computeRank_complete hac
  exact ⟨rank, hrank, (Network.valid_iff_tables _).2 ⟨hrows, Tables.computeRank_sound hrank⟩⟩

noncomputable section

/-- **Closedness of the compiled diagram**, from `FullValid`. -/
theorem FullValid.closed {r : Diagram} (h : r.FullValid) : (r.compile h.valid).Closed :=
  (r.compile h.valid).closed_iff.2 ⟨h.targets_injective, h.actions_injective, h.disjoint, h.cover⟩

/-- A causal rank of the instantiated chance part. -/
def FullValid.rank {r : Diagram} (h : r.FullValid) : Fin r.nv ≃ Fin r.nv :=
  let hr := (r.chance_acyclic_iff.1 h.acyclic).choose_spec
  Equiv.ofBijective _ ⟨hr.1, Finite.surjective_of_injective hr.1⟩

theorem FullValid.rank_input {r : Diagram} (h : r.FullValid) (i : Fin r.ni) :
    h.rank (r.inputs i).var < h.rank (r.mechanisms (r.inputs i).mechanism).target :=
  (r.chance_acyclic_iff.1 h.acyclic).choose_spec.2.1 i

theorem FullValid.rank_information {r : Diagram} (h : r.FullValid) (f : Fin r.nf) :
    h.rank (r.information f).var < h.rank (r.decisions (r.information f).decision).action :=
  (r.chance_acyclic_iff.1 h.acyclic).choose_spec.2.2 f

/-- **An `IDOrder` of the compiled diagram**, listing the variables by the rank. -/
def FullValid.idOrder {r : Diagram} (h : r.FullValid) : (r.compile h.valid).IDOrder where
  order := List.ofFn h.rank.symm
  nodup := List.nodup_ofFn.2 h.rank.symm.injective
  complete v := List.mem_ofFn.2 ⟨h.rank v, h.rank.symm_apply_apply v⟩
  parents_before := by
    apply List.pairwise_ofFn.2
    intro a b hab m hm hv
    obtain ⟨i, hi, he⟩ := Finset.mem_image.1 hv
    have hown := (Finset.mem_filter.1 hi).2
    have hr := h.rank_input i
    change (r.mechanisms m).target = h.rank.symm a at hm
    rw [hown, hm, he, h.rank.apply_symm_apply, h.rank.apply_symm_apply] at hr
    exact (not_lt_of_ge hab.le) hr
  info_before_action := by
    apply List.pairwise_ofFn.2
    intro a b hab d hd hv
    obtain ⟨f, hf, he⟩ := Finset.mem_image.1 hv
    have hown := (Finset.mem_filter.1 hf).2
    have hr := h.rank_information f
    change (r.decisions d).action = h.rank.symm a at hd
    rw [hown, hd, he, h.rank.apply_symm_apply, h.rank.apply_symm_apply] at hr
    exact (not_lt_of_ge hab.le) hr
  no_self m := by
    intro hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.1 hm
    have hr := h.rank_input i
    rw [(Finset.mem_filter.1 hi).2, he] at hr
    exact lt_irrefl _ hr
  no_self_info d := by
    intro hd
    obtain ⟨f, hf, he⟩ := Finset.mem_image.1 hd
    have hr := h.rank_information f
    rw [(Finset.mem_filter.1 hf).2, he] at hr
    exact lt_irrefl _ hr

/-! ## The label-order theorems under `FullValid` -/

/-- `solveRepRecords_table` without the `Closed` hypothesis: Julia's sum-out representative, any
plan, every information row, is the least checked `state_position` among the maximizers of the
run's own score. -/
theorem solveRepRecords_table_of_fullValid (r : Diagram) (h : r.FullValid)
    (keep : (r.compile h.valid).V → Bool) (κ : (r.compile h.valid).Kernel ℝ)
    (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility (r.compile h.valid) ℝ)
    (hu : ∀ j, Utility.Local u j) (plan : DVE.Plan (r.compile h.valid) Finset.univ)
    (d : (r.compile h.valid).D) (x : (r.compile h.valid).Assignment) :
    ∃ t, (∀ a, ((DVE.solveRepPlanWith (r.selector h.valid) keep κ hloc hnonneg u hu plan).strategy
          d).kernel x a = if a = t then 1 else 0) ∧
      (∀ b, DVE.solveRepPlanScore keep κ hloc hnonneg u hu plan d x b ≤
        DVE.solveRepPlanScore keep κ hloc hnonneg u hu plan d x t) ∧
      ∀ b, (∀ c, DVE.solveRepPlanScore keep κ hloc hnonneg u hu plan d x c ≤
          DVE.solveRepPlanScore keep κ hloc hnonneg u hu plan d x b) →
        r.statePosition h.valid _ t ≤ r.statePosition h.valid _ b :=
  r.solveRepRecords_table h.valid keep κ h.closed hloc hnonneg u hu plan d x

/-- `solveRepRecords_optimal` without the `Closed` and `IDOrder` hypotheses. -/
theorem solveRepRecords_optimal_of_fullValid (r : Diagram) (h : r.FullValid)
    (keep : (r.compile h.valid).V → Bool) (κ : (r.compile h.valid).Kernel ℝ)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility (r.compile h.valid) ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : DVE.Plan (r.compile h.valid) Finset.univ) (d : (r.compile h.valid).D)
    (x : (r.compile h.valid).Assignment) (ρ : Strategy (r.compile h.valid) ℝ)
    (hx : DVE.reach κ (fun _ => 1) ρ d x ≠ 0) :
    ∃ t, (∀ a, ((DVE.solveRepPlanWith (r.selector h.valid) keep κ hloc hnonneg u hu plan).strategy
          d).kernel x a = if a = t then 1 else 0) ∧
      (∀ b, DVE.optimalContinuation κ u (fun _ => 1) d x b ≤
        DVE.optimalContinuation κ u (fun _ => 1) d x t) ∧
      ∀ b, (∀ c, DVE.optimalContinuation κ u (fun _ => 1) d x c ≤
          DVE.optimalContinuation κ u (fun _ => 1) d x b) →
        r.statePosition h.valid _ t ≤ r.statePosition h.valid _ b :=
  r.solveRepRecords_optimal h.valid keep κ h.closed h.idOrder hloc hnorm hnonneg u hu plan d x ρ hx

/-- `solveRecords_table` without the `Closed` and `IDOrder` hypotheses (the order is
`FullValid.idOrder`; the no-forgetting order stays a hypothesis). -/
theorem solveRecords_table_of_fullValid (r : Diagram) (h : r.FullValid)
    (κ : (r.compile h.valid).Kernel ℝ) (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility (r.compile h.valid) ℝ) (hu : ∀ j, Utility.Local u j)
    (nf : DVE.NoForgettingOrder (r.compile h.valid)) (d : (r.compile h.valid).D)
    (x : (r.compile h.valid).Assignment) :
    ∃ t, (∀ a, ((DVE.solveWith (r.selector h.valid) κ hloc hnonneg u hu h.idOrder nf).strategy
          d).kernel x a = if a = t then 1 else 0) ∧
      (∀ b, DVE.solveScore κ hloc hnonneg u hu h.idOrder nf d x b ≤
        DVE.solveScore κ hloc hnonneg u hu h.idOrder nf d x t) ∧
      ∀ b, (∀ c, DVE.solveScore κ hloc hnonneg u hu h.idOrder nf d x c ≤
          DVE.solveScore κ hloc hnonneg u hu h.idOrder nf d x b) →
        r.statePosition h.valid _ t ≤ r.statePosition h.valid _ b :=
  r.solveRecords_table h.valid κ h.closed hloc hnonneg u hu h.idOrder nf d x

end

end Diagram
end Records
end InfluenceDiagramsProofs
