import InfluenceDiagramsProofs.Finite.DVE.Driver

/-!
# Initialisation and the returned solution

Each chance mechanism contributes `(κ,0)` and each utility contributes `(1,u)`, with its
actual dependency scope. The solver starts from those separate valuations, executes `run`,
and returns the scalar utility and reconstructed policies. No strategy enumeration occurs.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

variable {id : FinInfluenceDiagram}

def chanceValuation (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (m : id.M) : Valuation id.toFinBayesNet where
  scope := insert (id.target m) (id.parents m)
  prob x := κ m x (x (id.target m))
  util _ := 0
  prob_local x y h := by
    dsimp only
    rw [hloc m x y (fun v hv => h v (Finset.mem_insert_of_mem hv)),
      h (id.target m) (Finset.mem_insert_self _ _)]
  util_local := fun _ _ _ => rfl
  nonneg x := hnonneg m x _

def utilityValuation (u : Utility id ℝ) (hloc : ∀ j, Utility.Local u j) (j : id.U) :
    Valuation id.toFinBayesNet where
  scope := id.uscope j
  prob _ := 1
  util := u j
  prob_local := fun _ _ _ => rfl
  util_local := hloc j
  nonneg _ := zero_le_one

def initial (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) : State id Finset.univ where
  valuations := Finset.univ.toList.map (chanceValuation κ hloc hnonneg) ++
    Finset.univ.toList.map (utilityValuation u hu)
  supported := Finset.subset_univ _

theorem collect_prob {bn : FinBayesNet} (vs : List (Valuation bn)) (x : bn.Assignment) :
    (collect vs).prob x = (vs.map fun v => v.prob x).prod := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [collect, combine, ih]

theorem collect_util {bn : FinBayesNet} (vs : List (Valuation bn)) (x : bn.Assignment) :
    (collect vs).util x = (vs.map fun v => v.util x).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [collect, combine, ih]

theorem initial_prob (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (x : id.Assignment) :
    (collect (initial κ hloc hnonneg u hu).valuations).prob x =
      ∏ m, κ m x (x (id.target m)) := by
  simp [initial, collect_prob, List.map_map, chanceValuation, utilityValuation]

theorem initial_util (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (x : id.Assignment) :
    (collect (initial κ hloc hnonneg u hu).valuations).util x = totalUtility u x := by
  simp [initial, collect_util, List.map_map, chanceValuation, utilityValuation, totalUtility]

theorem initial_correct (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (σ : Strategy id ℝ) : Correct κ u (initial κ hloc hnonneg u hu) σ := by
  constructor
  · intro x
    simp [initial_prob, marg_empty, freeJoint_empty]
  · intro x
    simp [weight, initial_prob, initial_util, marg_empty, freeJoint_empty]
  · intro τ _ x
    simp [weight, initial_prob, initial_util, marg_empty, freeJoint_empty]

def CoversChance {R : Finset id.V} (s : State id R) : Prop :=
  ∀ v ∈ R, (∀ d, id.action d ≠ v) → v ∈ (collect s.valuations).scope

theorem initial_covers_chance (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) :
    CoversChance (initial κ hloc hnonneg u hu) := by
  intro v _ hv
  obtain ⟨g, hg⟩ := hclosed.2 v
  cases g with
  | inr d => exact False.elim (hv d hg)
  | inl m =>
    have hm : chanceValuation κ hloc hnonneg m ∈ (initial κ hloc hnonneg u hu).valuations := by
      apply List.mem_append_left
      exact List.mem_map.2 ⟨m, Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩
    apply collect_scope _ hm
    change v ∈ insert (id.target m) (id.parents m)
    have he : id.target m = v := hg
    rw [← he]
    exact Finset.mem_insert_self _ _

theorem CoversChance.next {R : Finset id.V} {s : State id R} (h : CoversChance s)
    (a : id.V) (t : State id (R.erase a))
    (ht : (collect t.valuations).scope = (collect s.valuations).scope.erase a) :
    CoversChance t := by
  intro v hv hc
  rw [ht]
  exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hv).1, h v (Finset.mem_erase.1 hv).2 hc⟩

def chanceBucketsPresent {R : Finset id.V} (plan : Plan id R) (s : State id R) : Prop :=
  match plan with
  | .done => True
  | .chance v _ _ next =>
    bucket v s.valuations ≠ [] ∧ chanceBucketsPresent next (s.chance v)
  | .decision d _ _ next => chanceBucketsPresent next (s.decision d)

/-- In a closed compiled model, no scheduled chance variable disappears prematurely.
Thus the source's skip-absent-variable optimisation does not change a no-evidence run. -/
theorem chanceBucketsPresent_of_covers {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (h : CoversChance s) : chanceBucketsPresent plan s := by
  induction plan with
  | done => trivial
  | chance v hv hc next ih =>
    constructor
    · intro he
      have hs := h v hv hc
      rw [collect_partition_scope v s.valuations, he] at hs
      have hr : v ∈ (collect (outside v s.valuations)).scope := by
        simpa [collect, unit] using hs
      exact outside_notMem v s.valuations hr
    · exact ih _ (h.next v _ (step_scope_eq v s.valuations (sumOut v) (fun _ => rfl)))
  | decision d _ _ next ih =>
    exact ih _ (h.next _ _ (step_scope_eq _ s.valuations (maxOut _) (fun _ => rfl)))

def defaultStrategy : Strategy id ℝ :=
  fun d => Policy.const d (Classical.choice (id.nonemptyS (id.action d)))

theorem defaultStrategy_deterministic : (defaultStrategy (id := id)).Deterministic := by
  intro d
  exact ⟨fun _ => Classical.choice (id.nonemptyS (id.action d)), fun _ _ _ => rfl, rfl⟩

theorem deterministic_nonneg (σ : Strategy id ℝ) (h : σ.Deterministic) : σ.Nonneg := by
  intro d x a
  obtain ⟨f, hf, he⟩ := h d
  rw [he, Policy.ofFun_kernel]
  split_ifs
  · exact zero_le_one
  · exact le_refl 0

theorem update_policy_deterministic {R : Finset id.V} (s : State id R) (d : id.D)
    (hi : R.erase (id.action d) = id.info d) (σ : Strategy id ℝ) (hσ : σ.Deterministic) :
    Strategy.Deterministic (Function.update σ d (s.policy d hi)) := by
  intro e
  by_cases h : e = d
  · subst e
    simp only [Function.update_self]
    unfold State.policy
    refine ⟨_, ?_, rfl⟩
    intro x y h
    apply choice_local
    intro v hv
    apply h
    rw [← hi]
    exact Finset.erase_subset_erase _ ((filter_scope_subset _ s.valuations).trans s.supported) hv
  · rw [Function.update_of_ne h]
    exact hσ e

theorem run_deterministic {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (σ : Strategy id ℝ) (hσ : σ.Deterministic) : (run plan s σ).2.Deterministic := by
  induction plan generalizing σ with
  | done => exact hσ
  | chance v _ _ next ih => exact ih (s.chance v) σ hσ
  | decision d _ hi next ih =>
    exact ih (s.decision d) _ (update_policy_deterministic s d hi σ hσ)

def baseAssignment (id : FinInfluenceDiagram) : id.Assignment :=
  fun v => Classical.choice (id.nonemptyS v)

structure Solution (id : FinInfluenceDiagram) where
  value : ℝ
  strategy : Strategy id ℝ

def solvePlan (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) : Solution id :=
  let result := run plan (initial κ hloc hnonneg u hu) defaultStrategy
  ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩

/-- End-to-end correctness for the actual bucket driver on a structural strong plan.
The next module constructs such plans from arbitrary finite no-forgetting decision lists. -/
theorem solvePlan_spec (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : RankedOrder id)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) :
    let sol := solvePlan κ hloc hnonneg u hu plan
    sol.strategy.Deterministic ∧ expectedUtility κ sol.strategy u = sol.value ∧
      sol.value = optimalValue κ u := by
  let result := run plan (initial κ hloc hnonneg u hu) (defaultStrategy (id := id))
  have hc : Correct κ u result.1 result.2 := run_correct hclosed ord hloc hnorm plan _ _
    (initial_correct κ hloc hnonneg u hu _)
  have hd : result.2.Deterministic :=
    run_deterministic plan _ _ defaultStrategy_deterministic
  have hp : (collect result.1.valuations).prob (baseAssignment id) = 1 := by
    rw [hc.mass, Finset.compl_empty, freeJoint_univ, marg_univ]
    exact sum_joint_instantiate_eq_one κ result.2 hclosed ord.order hloc hnorm
  have hr : expectedUtility κ result.2 u =
      (collect result.1.valuations).util (baseAssignment id) := by
    have h := hc.realizes (baseAssignment id)
    rw [weight, hp, one_mul, Finset.compl_empty, freeJoint_univ, marg_univ] at h
    exact h.symm
  have ho : ∀ σ : Strategy id ℝ, σ.Nonneg →
      expectedUtility κ σ u ≤ (collect result.1.valuations).util (baseAssignment id) := by
    intro σ hσ
    have h := hc.dominates σ hσ (baseAssignment id)
    rw [weight, hp, one_mul, Finset.compl_empty, freeJoint_univ, marg_univ] at h
    exact h
  change result.2.Deterministic ∧ expectedUtility κ result.2 u =
    (collect result.1.valuations).util (baseAssignment id) ∧
      (collect result.1.valuations).util (baseAssignment id) = optimalValue κ u
  refine ⟨hd, hr, le_antisymm ?_ ?_⟩
  · rw [← hr]
    exact expectedUtility_le_optimalValue κ u result.2 (deterministic_nonneg _ hd)
  · obtain ⟨σ, _, hσ, hvalue⟩ := optimalValue_attained κ u
    rw [← hvalue]
    exact ho σ hσ

end
end InfluenceDiagramsProofs.DVE
