import InfluenceDiagramsProofs.Finite.DVE.Representative
import BayesianNetworksProofs.Finite.RawRecords

/-!
# Action labels in checked state-position order

`Selector.ordered` takes an arbitrary linear order on every action space. Julia's
`argmax_table` returns the first maximizing entry along the action axis, and that axis lists
the action's states in `state_position` order. This module derives the order from checked
records instead of supplying it.

* `positionOrder pos` is the linear order induced by an injective position map, and
  `firstArgmax_least_position` / `eq_firstArgmax_of_least_position` show that under it
  `firstArgmax` is exactly the maximizer of least position.
* `Records.Diagram` holds raw influence-diagram rows: variables and their state rows
  (`var`, `position`, `name`, the BN `Raw.StateRow`), mechanisms, inputs, decisions, information
  rows, utilities (`name`, `ref`), utility inputs and decision-precedence rows, with external
  IDs already decoded to `Fin`. `Valid` checks only what the label order needs: every variable
  has a state, positions are bounded and unique per variable (`Raw.Positioned`), and labels are
  unique per variable; `RecordsValid.lean` adds `FullValid`, which checks every table. `compile`
  builds the
  `FinInfluenceDiagram` whose state space for `v` is `Fin (stateCount v)`; `stateRecord` is
  the record at each position (the positional bijection `Raw.positionEquiv`, derived, not
  assumed), with `stateRecord_position`.
* `actionOrder` orders each action space by the checked `position` of its records
  (`actionOrder_le_iff`: it is the order of `Fin`), and `selector` is `Selector.ordered` with
  that order.

Headline results: `solveRecords_table` (the model's driver, every information row: the entry is
the state of least `position` among the maximizers of `solveScore`), `solveRepRecords_table`
(Julia's sum-out representative, any plan, every row, its own score) and
`solveRepRecords_optimal` (Julia's representative, any plan, every row of positive reach: the
state of least `position` among the maximizers of `optimalContinuation`).

What is not proved here: that Julia's arrays are laid out in that order is the
`FiniteKernels` `Layout/` result together with the Julia test pinning the action axis to
`states(id, v)`; that Julia's DVE certificate (`variables[].states`, rows of
`id`, `position`, `label`) decodes into these records is not formalised (there is no Lean
consumer of that certificate; the ACSet JSON of `write_json_influence_diagram` is decoded into
them by `Finite/DVE/JsonRecords.lean`); here the DVE hypotheses (`Closed`, `IDOrder`,
`NoForgettingOrder`) of the compiled diagram stay hypotheses (`RecordsValid.lean` derives
`Closed` and an `IDOrder` from `FullValid`; `NoForgettingOrder` stays one); and Julia's
execution itself is not proved.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram

noncomputable section

/-! ## Least-position maximizers -/

/-- The linear order induced by an injective position map. -/
@[reducible] def positionOrder {A : Type} (pos : A → ℕ) (hpos : Function.Injective pos) : LinearOrder A :=
  LinearOrder.lift' pos hpos

theorem positionOrder_le_iff {A : Type} (pos : A → ℕ) (hpos : Function.Injective pos)
    (a b : A) : (positionOrder pos hpos).le a b ↔ pos a ≤ pos b :=
  Iff.rfl

/-- Under the position order, `firstArgmax` maximizes and has the least position among all
maximizers. -/
theorem firstArgmax_least_position {A : Type} [Fintype A] [Nonempty A] (pos : A → ℕ)
    (hpos : Function.Injective pos) (f : A → ℝ) :
    (∀ b, f b ≤ f (@firstArgmax A _ _ (positionOrder pos hpos) f)) ∧
      ∀ b, (∀ c, f c ≤ f b) → pos (@firstArgmax A _ _ (positionOrder pos hpos) f) ≤ pos b :=
  letI := positionOrder pos hpos
  ⟨firstArgmax_maximizes f, fun b hb => firstArgmax_first f b hb⟩

/-- Conversely, the maximizer of least position is `firstArgmax`. -/
theorem eq_firstArgmax_of_least_position {A : Type} [Fintype A] [Nonempty A] (pos : A → ℕ)
    (hpos : Function.Injective pos) (f : A → ℝ) (t : A) (ht : ∀ b, f b ≤ f t)
    (hleast : ∀ b, (∀ c, f c ≤ f b) → pos t ≤ pos b) :
    t = @firstArgmax A _ _ (positionOrder pos hpos) f := by
  letI := positionOrder pos hpos
  obtain ⟨hmax, hfirst⟩ := firstArgmax_least_position pos hpos f
  exact hpos (le_antisymm (hleast _ hmax) (hfirst t ht))

/-! ## Checked influence-diagram records -/

namespace Records

open BayesianNetworksProofs.Raw

structure DecisionRow (nv : Nat) where
  action : Fin nv
  name : String

structure InformationRow (nv nd : Nat) where
  decision : Fin nd
  var : Fin nv
  position : Nat

structure UtilityRow where
  name : String
  ref : Ref

structure UtilityInputRow (nv nu : Nat) where
  utility : Fin nu
  var : Fin nv
  position : Nat

/-- A `DecisionPrecedence` row: `earlier` is taken before `later`. -/
structure PrecedenceRow (nd : Nat) where
  earlier : Fin nd
  later : Fin nd

/-- Raw influence-diagram rows with decoded finite IDs: every table of the `SchInfluenceDiagram`
ACSet (`Finite/DVE/JsonRecords.lean` decodes them from Julia's JSON), and the shape of the
`variables` / `mechanisms` / `decisions` / `utilities` sections of the DVE certificate. -/
structure Diagram where
  nv : Nat
  ns : Nat
  nm : Nat
  ni : Nat
  nd : Nat
  nf : Nat
  nu : Nat
  nq : Nat
  np : Nat
  vars : Fin nv → VariableRow
  states : Fin ns → StateRow nv
  mechanisms : Fin nm → MechanismRow nv
  inputs : Fin ni → InputRow nv nm
  decisions : Fin nd → DecisionRow nv
  information : Fin nf → InformationRow nv nd
  utilities : Fin nu → UtilityRow
  utilityInputs : Fin nq → UtilityInputRow nv nu
  precedence : Fin np → PrecedenceRow nd

namespace Diagram

def stateOwner (r : Diagram) (s : Fin r.ns) : Fin r.nv := (r.states s).var

def stateCount (r : Diagram) (v : Fin r.nv) : Nat :=
  Fintype.card {s : Fin r.ns // r.stateOwner s = v}

/-- The checks the label order needs; all decidable. -/
structure Valid (r : Diagram) : Prop where
  state_positions : Positioned r.stateOwner (fun s => (r.states s).position)
  nonempty_states : ∀ v, 0 < r.stateCount v
  state_names : ∀ s t, (r.states s).var = (r.states t).var →
    (r.states s).name = (r.states t).name → s = t

theorem valid_iff (r : Diagram) : r.Valid ↔
    Positioned r.stateOwner (fun s => (r.states s).position) ∧ (∀ v, 0 < r.stateCount v) ∧
      ∀ s t, (r.states s).var = (r.states t).var →
        (r.states s).name = (r.states t).name → s = t :=
  ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

instance (r : Diagram) : Decidable r.Valid := decidable_of_iff _ (valid_iff r).symm

def check (r : Diagram) : Bool := decide r.Valid

theorem check_iff (r : Diagram) : r.check = true ↔ r.Valid := by simp [check]

/-- The finite influence diagram of checked records. The state space of `v` is
`Fin (stateCount v)`, indexed by checked position. -/
@[reducible] def compile (r : Diagram) (h : r.Valid) : FinInfluenceDiagram where
  V := Fin r.nv
  M := Fin r.nm
  states v := Fin (r.stateCount v)
  nonemptyS v := ⟨⟨0, h.nonempty_states v⟩⟩
  target m := (r.mechanisms m).target
  parents m := (Finset.univ.filter fun i => (r.inputs i).mechanism = m).image
    fun i => (r.inputs i).var
  D := Fin r.nd
  action d := (r.decisions d).action
  info d := (Finset.univ.filter fun i => (r.information i).decision = d).image
    fun i => (r.information i).var
  U := Fin r.nu
  uscope j := (Finset.univ.filter fun i => (r.utilityInputs i).utility = j).image
    fun i => (r.utilityInputs i).var

/-- The positional bijection between the state records of `v` and `Fin (stateCount v)`,
derived from bounded unique positions. -/
def stateOrder (r : Diagram) (h : r.Valid) (v : Fin r.nv) :
    {s : Fin r.ns // r.stateOwner s = v} ≃ Fin (r.stateCount v) :=
  positionEquiv r.stateOwner (fun s => (r.states s).position) h.state_positions v

/-- The state record at each position. -/
def stateRecord (r : Diagram) (h : r.Valid) (v : Fin r.nv) (a : Fin (r.stateCount v)) :
    Fin r.ns :=
  ((r.stateOrder h v).symm a).val

theorem stateRecord_var (r : Diagram) (h : r.Valid) (v : Fin r.nv) (a : Fin (r.stateCount v)) :
    (r.states (r.stateRecord h v a)).var = v :=
  ((r.stateOrder h v).symm a).property

theorem stateRecord_position (r : Diagram) (h : r.Valid) (v : Fin r.nv)
    (a : Fin (r.stateCount v)) : (r.states (r.stateRecord h v a)).position = a.val :=
  congrArg Fin.val ((r.stateOrder h v).apply_symm_apply a)

/-- Every state record of `v` is the record at its own position. -/
theorem stateRecord_of_mem (r : Diagram) (h : r.Valid) (s : Fin r.ns) :
    ∃ a : Fin (r.stateCount (r.states s).var), r.stateRecord h _ a = s ∧
      a.val = (r.states s).position :=
  ⟨r.stateOrder h _ ⟨s, rfl⟩, congrArg Subtype.val ((r.stateOrder h _).symm_apply_apply _), rfl⟩

/-- The checked `state_position` of a state. -/
def statePosition (r : Diagram) (h : r.Valid) (v : Fin r.nv) (a : Fin (r.stateCount v)) : ℕ :=
  (r.states (r.stateRecord h v a)).position

/-- The label (`state_name`) of a state. -/
def stateLabel (r : Diagram) (h : r.Valid) (v : Fin r.nv) (a : Fin (r.stateCount v)) : String :=
  (r.states (r.stateRecord h v a)).name

theorem statePosition_eq (r : Diagram) (h : r.Valid) (v : Fin r.nv) (a : Fin (r.stateCount v)) :
    r.statePosition h v a = a.val :=
  r.stateRecord_position h v a

theorem statePosition_injective (r : Diagram) (h : r.Valid) (v : Fin r.nv) :
    Function.Injective (r.statePosition h v) := by
  intro a b he
  rw [statePosition_eq, statePosition_eq] at he
  exact Fin.ext he

theorem stateLabel_injective (r : Diagram) (h : r.Valid) (v : Fin r.nv) :
    Function.Injective (r.stateLabel h v) := by
  intro a b he
  have hs : (r.stateOrder h v).symm a = (r.stateOrder h v).symm b :=
    Subtype.ext (h.state_names _ _ ((r.stateRecord_var h v a).trans (r.stateRecord_var h v b).symm)
      he)
  exact (r.stateOrder h v).symm.injective hs

/-- Each action space ordered by the checked positions of its state records. -/
@[reducible] def actionOrder (r : Diagram) (h : r.Valid) (d : (r.compile h).D) :
    LinearOrder ((r.compile h).states ((r.compile h).action d)) :=
  positionOrder (r.statePosition h (r.decisions d).action)
    (r.statePosition_injective h (r.decisions d).action)

/-- The position order is the order of `Fin (stateCount v)`. -/
theorem actionOrder_le_iff (r : Diagram) (h : r.Valid) (d : (r.compile h).D)
    (a b : Fin (r.stateCount (r.decisions d).action)) :
    (r.actionOrder h d).le a b ↔ a ≤ b := by
  change r.statePosition h _ a ≤ r.statePosition h _ b ↔ a.val ≤ b.val
  rw [statePosition_eq, statePosition_eq]

/-- The first-label selector of the checked records. -/
def selector (r : Diagram) (h : r.Valid) : DVE.Selector (r.compile h) :=
  @DVE.Selector.ordered (r.compile h) (r.actionOrder h)

/-! ## The returned tables in state-position terms -/

/-- **The model's first-label table is the least checked `state_position` among the
maximizers, on every information row.** -/
theorem solveRecords_table (r : Diagram) (h : r.Valid) (κ : (r.compile h).Kernel ℝ)
    (hclosed : (r.compile h).Closed) (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility (r.compile h) ℝ) (hu : ∀ j, Utility.Local u j) (ord : (r.compile h).IDOrder)
    (nf : DVE.NoForgettingOrder (r.compile h)) (d : (r.compile h).D)
    (x : (r.compile h).Assignment) :
    ∃ t, (∀ a, ((DVE.solveWith (r.selector h) κ hloc hnonneg u hu ord nf).strategy d).kernel x a =
        if a = t then 1 else 0) ∧
      (∀ b, DVE.solveScore κ hloc hnonneg u hu ord nf d x b ≤
        DVE.solveScore κ hloc hnonneg u hu ord nf d x t) ∧
      ∀ b, (∀ c, DVE.solveScore κ hloc hnonneg u hu ord nf d x c ≤
          DVE.solveScore κ hloc hnonneg u hu ord nf d x b) →
        r.statePosition h _ t ≤ r.statePosition h _ b := by
  have hinj := ((r.compile h).closed_iff.1 hclosed).2.1
  refine ⟨_, fun a => @DVE.runWith_kernel (r.compile h) (r.selector h) hinj _ _ _ _ d
    (Finset.mem_univ _) x a, ?_⟩
  exact @firstArgmax_least_position _ ((r.compile h).fintypeS _) ((r.compile h).nonemptyS _) _
    (r.statePosition_injective h _) _

/-- **Julia's sum-out representative, any plan, every information row:** the entry is the
least checked `state_position` among the maximizers of the run's own score. -/
theorem solveRepRecords_table (r : Diagram) (h : r.Valid) (keep : (r.compile h).V → Bool)
    (κ : (r.compile h).Kernel ℝ) (hclosed : (r.compile h).Closed) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility (r.compile h) ℝ)
    (hu : ∀ j, Utility.Local u j) (plan : DVE.Plan (r.compile h) Finset.univ)
    (d : (r.compile h).D) (x : (r.compile h).Assignment) :
    ∃ t, (∀ a, ((DVE.solveRepPlanWith (r.selector h) keep κ hloc hnonneg u hu plan).strategy
          d).kernel x a = if a = t then 1 else 0) ∧
      (∀ b, DVE.solveRepPlanScore keep κ hloc hnonneg u hu plan d x b ≤
        DVE.solveRepPlanScore keep κ hloc hnonneg u hu plan d x t) ∧
      ∀ b, (∀ c, DVE.solveRepPlanScore keep κ hloc hnonneg u hu plan d x c ≤
          DVE.solveRepPlanScore keep κ hloc hnonneg u hu plan d x b) →
        r.statePosition h _ t ≤ r.statePosition h _ b := by
  have hinj := ((r.compile h).closed_iff.1 hclosed).2.1
  refine ⟨_, fun a => @DVE.runRepWith_kernel (r.compile h) (r.selector h) keep hinj _ _ _ _ d
    (Finset.mem_univ _) x a, ?_⟩
  exact @firstArgmax_least_position _ ((r.compile h).fintypeS _) ((r.compile h).nonemptyS _) _
    (r.statePosition_injective h _) _

/-- **Julia's sum-out representative, any plan, every row of positive reach:** the entry is the
least checked `state_position` among the maximizers of the optimal continuation value, a
quantity that mentions no plan, bucket, representative or selector. -/
theorem solveRepRecords_optimal (r : Diagram) (h : r.Valid) (keep : (r.compile h).V → Bool)
    (κ : (r.compile h).Kernel ℝ) (hclosed : (r.compile h).Closed) (ord : (r.compile h).IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility (r.compile h) ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : DVE.Plan (r.compile h) Finset.univ) (d : (r.compile h).D)
    (x : (r.compile h).Assignment) (ρ : Strategy (r.compile h) ℝ)
    (hx : DVE.reach κ (fun _ => 1) ρ d x ≠ 0) :
    ∃ t, (∀ a, ((DVE.solveRepPlanWith (r.selector h) keep κ hloc hnonneg u hu plan).strategy
          d).kernel x a = if a = t then 1 else 0) ∧
      (∀ b, DVE.optimalContinuation κ u (fun _ => 1) d x b ≤
        DVE.optimalContinuation κ u (fun _ => 1) d x t) ∧
      ∀ b, (∀ c, DVE.optimalContinuation κ u (fun _ => 1) d x c ≤
          DVE.optimalContinuation κ u (fun _ => 1) d x b) →
        r.statePosition h _ t ≤ r.statePosition h _ b :=
  ⟨_, fun a => @DVE.solveRepPlanOrdered_optimal (r.compile h) (r.actionOrder h) keep κ hclosed
      ord hloc hnorm hnonneg u hu plan d x ρ hx a,
    @firstArgmax_least_position _ ((r.compile h).fintypeS _) ((r.compile h).nonemptyS _) _
      (r.statePosition_injective h _) _⟩

end Diagram
end Records

end
end InfluenceDiagramsProofs
