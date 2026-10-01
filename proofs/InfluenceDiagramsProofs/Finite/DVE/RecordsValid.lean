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
  proved placement of `Raw.Tables.computeRank`).

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

Not checked: decision precedence rows (stored, not validated), unique variable, decision or
utility names, and the no-forgetting condition (`NoForgettingOrder` stays a hypothesis).
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

/-! ## Full validity -/

/-- **Every table checked**: the state rows (`Valid`), positions of inputs, information inputs
and utility inputs, the generators (one per variable) and acyclicity of the instantiated chance
part. All decidable. -/
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

theorem fullValid_iff (r : Diagram) : r.FullValid ↔
    r.Valid ∧ Positioned (fun i => (r.inputs i).mechanism) (fun i => (r.inputs i).position) ∧
    Positioned (fun f => (r.information f).decision) (fun f => (r.information f).position) ∧
    Positioned (fun q => (r.utilityInputs q).utility) (fun q => (r.utilityInputs q).position) ∧
    (∀ m m', (r.mechanisms m).target = (r.mechanisms m').target → m = m') ∧
    (∀ d d', (r.decisions d).action = (r.decisions d').action → d = d') ∧
    (∀ m d, (r.mechanisms m).target ≠ (r.decisions d).action) ∧
    (∀ v, (∃ m, (r.mechanisms m).target = v) ∨ ∃ d, (r.decisions d).action = v) ∧
    r.chance.Acyclic :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, fun _ _ he => h.5 he, fun _ _ he => h.6 he, h.7, h.8, h.9⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun _ _ he => h.2.2.2.2.1 _ _ he,
      fun _ _ he => h.2.2.2.2.2.1 _ _ he, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2⟩⟩

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
