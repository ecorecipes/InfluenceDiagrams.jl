import InfluenceDiagramsProofs.Finite.DVE.Schedule

/-!
# Action-independent evidence

Evidence is supported on a chance-ancestral set containing no action. This is a structural
non-action-descendant condition, not an assumption that the likelihood normalizer is
strategy-independent. That independence is proved below. Nonnegative likelihood weights
include hard evidence indicators. Conditional claims require strictly positive evidence mass.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

variable {id : FinInfluenceDiagram}

structure Evidence (id : FinInfluenceDiagram) where
  ancestors : Finset id.V
  closed : ∀ m, id.target m ∈ ancestors → id.parents m ⊆ ancestors
  no_action : ∀ d, id.action d ∉ ancestors
  likelihood : id.Assignment → ℝ
  localOn : Depends ancestors likelihood
  nonneg : ∀ x, 0 ≤ likelihood x

namespace Evidence

/-- Hard observations on any subset of an action-free ancestral set. -/
def hard (A O : Finset id.V) (hO : O ⊆ A)
    (hc : ∀ m, id.target m ∈ A → id.parents m ⊆ A)
    (ha : ∀ d, id.action d ∉ A) (observed : id.Assignment) : Evidence id where
  ancestors := A
  closed := hc
  no_action := ha
  likelihood x := if ∀ v ∈ O, x v = observed v then 1 else 0
  localOn x y h := by
    dsimp only
    have he : (∀ v ∈ O, x v = observed v) ↔ (∀ v ∈ O, y v = observed v) := by
      constructor
      · intro hx v hv
        rw [← h v (hO hv)]
        exact hx v hv
      · intro hy v hv
        rw [h v (hO hv)]
        exact hy v hv
    simp only [he]
  nonneg x := by
    split_ifs
    · exact zero_le_one
    · exact le_refl 0

def valuation (e : Evidence id) : Valuation id.toFinBayesNet where
  scope := e.ancestors
  prob := e.likelihood
  util _ := 0
  prob_local := e.localOn
  util_local := fun _ _ _ => rfl
  nonneg := e.nonneg

/-- Put the action-free ancestral evidence block before every action. The original topological
order remains available; the new ranks preserve every causal and information inequality. -/
def ranked (e : Evidence id) (ord : id.IDOrder) : RankedOrder id where
  order := ord
  rank v := if v ∈ e.ancestors then ord.order.idxOf v else ord.order.length + ord.order.idxOf v
  parents_lt m v hv := by
    have hold := (RankedOrder.ofOrder ord).parents_lt m v hv
    have hlen := List.idxOf_lt_length_of_mem (ord.complete v)
    by_cases ht : id.target m ∈ e.ancestors
    · have hp := e.closed m ht hv
      simpa [ht, hp] using hold
    · by_cases hp : v ∈ e.ancestors
      · simp only [ht, hp, ↓reduceIte]
        exact hlen.trans_le (Nat.le_add_right _ _)
      · simpa [ht, hp] using Nat.add_lt_add_left hold ord.order.length
  info_lt d v hv := by
    have hold := (RankedOrder.ofOrder ord).info_lt d v hv
    have hlen := List.idxOf_lt_length_of_mem (ord.complete v)
    by_cases hp : v ∈ e.ancestors
    · simp only [e.no_action, hp, ↓reduceIte]
      exact hlen.trans_le (Nat.le_add_right _ _)
    · simpa [e.no_action, hp] using Nat.add_lt_add_left hold ord.order.length

theorem rank_before_actions (e : Evidence id) (ord : id.IDOrder) (d : id.D)
    (v : id.V) (hv : v ∈ e.ancestors) :
    (e.ranked ord).rank v < (e.ranked ord).rank (id.action d) := by
  simp only [ranked, hv, e.no_action, ↓reduceIte]
  exact (List.idxOf_lt_length_of_mem (ord.complete v)).trans_le (Nat.le_add_right _ _)

theorem probability_independent (e : Evidence id) (κ : id.Kernel ℝ)
    (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (E : Finset id.V) (σ : Strategy id ℝ) (d : id.D) (hd : id.action d ∉ E)
    (hboundary : Eᶜ ⊆ insert (id.action d) (id.info d))
    (x : id.Assignment) (a : id.states (id.action d)) :
    marg E (fun y => freeJoint κ E σ y * e.likelihood y) (Function.update x (id.action d) a) =
      marg E (fun y => freeJoint κ E σ y * e.likelihood y) x := by
  apply probability_independent_weighted κ hclosed (e.ranked ord) hloc hnorm E σ d hd hboundary
  · intro y z h
    apply e.localOn
    intro v hv
    exact h v (Finset.mem_filter.2 ⟨Finset.mem_univ _, (e.rank_before_actions ord d v hv).le⟩)
  · intro y b
    apply e.localOn
    intro v hv
    exact Function.update_of_ne (show v ≠ id.action d from fun he => e.no_action d (he ▸ hv)) _ _

end Evidence

def evidenceMass (κ : id.Kernel ℝ) (σ : Strategy id ℝ) (e : Evidence id) : ℝ :=
  ∑ x, joint (strategyKernel κ σ) x * e.likelihood x

def evidenceNumerator (κ : id.Kernel ℝ) (σ : Strategy id ℝ) (u : Utility id ℝ)
    (e : Evidence id) : ℝ :=
  ∑ x, joint (strategyKernel κ σ) x * e.likelihood x * totalUtility u x

def conditionalEU (κ : id.Kernel ℝ) (σ : Strategy id ℝ) (u : Utility id ℝ)
    (e : Evidence id) : ℝ := evidenceNumerator κ σ u e / evidenceMass κ σ e

theorem evidenceMass_nonneg (e : Evidence id) (κ : id.Kernel ℝ)
    (hκ : ∀ m x a, 0 ≤ κ m x a) (σ : Strategy id ℝ) (hσ : σ.Nonneg) :
    0 ≤ evidenceMass κ σ e := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (e.nonneg x)
  rw [joint_instantiate]
  exact mul_nonneg (Finset.prod_nonneg fun m _ => hκ m x _)
    (Finset.prod_nonneg fun d _ => hσ d x _)

/-- Evidence mass is independent of all policy choices, derived from action-free ancestry and
normalized downstream mechanisms/policies. Positivity is not assumed by this equality. -/
theorem evidenceMass_independent (e : Evidence id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (σ τ : Strategy id ℝ) : evidenceMass κ σ e = evidenceMass κ τ e := by
  let U := e.ancestors
  have hU : UpstreamClosed (bn := id.instantiate) U := by
    rintro (m | d) hm
    · exact e.closed m hm
    · exact False.elim (e.no_action d hm)
  have hd (ρ : Strategy id ℝ) (x : id.Assignment) :
      marg (bn := id.instantiate) Uᶜ (joint (strategyKernel κ ρ)) x =
        ∏ m ∈ Finset.univ.filter (fun m => id.instantiate.target m ∈ U),
          strategyKernel κ ρ m x (x (id.instantiate.target m)) :=
    marg_joint_upstream _ (closed_instantiate hclosed) ord.toTopoOrder
      (local_instantiate κ ρ hloc) (normalised_instantiate κ ρ hnorm) U hU x
  have heq (x : id.Assignment) :
      marg (bn := id.instantiate) Uᶜ (joint (strategyKernel κ σ)) x =
        marg (bn := id.instantiate) Uᶜ (joint (strategyKernel κ τ)) x := by
    rw [hd, hd]
    apply Finset.prod_congr rfl
    intro m hm
    cases m with
    | inl m => rfl
    | inr d => exact False.elim (e.no_action d (Finset.mem_filter.1 hm).2)
  have hw (ρ : Strategy id ℝ) (x : id.Assignment) :
      marg (bn := id.instantiate) Uᶜ (fun y => joint (strategyKernel κ ρ) y * e.likelihood y) x =
        e.likelihood x * marg (bn := id.instantiate) Uᶜ (joint (strategyKernel κ ρ)) x := by
    have hf : (fun y => joint (bn := id.instantiate) (strategyKernel κ ρ) y * e.likelihood y) =
        (fun y => e.likelihood y * joint (bn := id.instantiate) (strategyKernel κ ρ) y) := by
      funext y
      ring
    rw [hf]
    exact marg_mul_left fun y hy => e.localOn y x fun v hv =>
      mem_fibre.1 hy v (fun hc => Finset.mem_compl.1 hc hv)
  have hs (ρ : Strategy id ℝ) :
      evidenceMass κ ρ e =
        marg U (fun x => e.likelihood x *
          marg (bn := id.instantiate) Uᶜ (joint (strategyKernel κ ρ)) x)
          (baseAssignment id) := by
    calc
      _ = marg (bn := id.instantiate) Finset.univ
          (fun y => joint (strategyKernel κ ρ) y * e.likelihood y) (baseAssignment id) :=
        (marg_univ _ _).symm
      _ = marg (bn := id.instantiate) (U ∪ Uᶜ)
          (fun y => joint (strategyKernel κ ρ) y * e.likelihood y) (baseAssignment id) :=
        congrArg (fun S => marg (bn := id.instantiate) S
          (fun y => joint (strategyKernel κ ρ) y * e.likelihood y) (baseAssignment id))
          (Finset.union_compl U).symm
      _ = marg U (fun x => marg (bn := id.instantiate) Uᶜ
          (fun y => joint (strategyKernel κ ρ) y * e.likelihood y) x) (baseAssignment id) :=
        marg_union_disjoint (Finset.disjoint_left.2 (fun _ hu hc => Finset.mem_compl.1 hc hu)) _ _
      _ = _ := congrArg (fun f => marg (bn := id.instantiate) U f (baseAssignment id)) (funext (hw ρ))
  rw [hs, hs]
  simp_rw [heq]

structure WeightedCorrect (κ : id.Kernel ℝ) (u : Utility id ℝ) (e : Evidence id)
    {R : Finset id.V} (s : State id R) (σ : Strategy id ℝ) : Prop where
  mass : ∀ x, (collect s.valuations).prob x =
    marg Rᶜ (fun y => freeJoint κ Rᶜ σ y * e.likelihood y) x
  realizes : ∀ x, (collect s.valuations).weight x =
    marg Rᶜ (fun y => freeJoint κ Rᶜ σ y * (e.likelihood y * totalUtility u y)) x
  dominates : ∀ τ : Strategy id ℝ, τ.Nonneg → ∀ x,
    marg Rᶜ (fun y => freeJoint κ Rᶜ τ y * (e.likelihood y * totalUtility u y)) x ≤
      (collect s.valuations).weight x

theorem WeightedCorrect.chance {κ : id.Kernel ℝ} {u : Utility id ℝ} {e : Evidence id}
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ} (h : WeightedCorrect κ u e s σ)
    (v : id.V) (hv : v ∈ R) (hc : ∀ d, id.action d ≠ v) :
    WeightedCorrect κ u e (s.chance v) σ := by
  have hn : v ∉ Rᶜ := by simpa using hv
  constructor
  · intro x
    change (collect (chanceStep v s.valuations)).prob x = _
    rw [chanceStep_prob, compl_erase, freeJoint_insert_chance κ Rᶜ σ v hc, marg_insert hn]
    exact Finset.sum_congr rfl fun b _ => h.mass _
  · intro x
    change (collect (chanceStep v s.valuations)).weight x = _
    rw [chanceStep_weight, compl_erase, freeJoint_insert_chance κ Rᶜ σ v hc, marg_insert hn]
    exact Finset.sum_congr rfl fun b _ => h.realizes _
  · intro τ hτ x
    change _ ≤ (collect (chanceStep v s.valuations)).weight x
    rw [chanceStep_weight, compl_erase, freeJoint_insert_chance κ Rᶜ τ v hc, marg_insert hn]
    exact Finset.sum_le_sum fun b _ => h.dominates τ hτ _

theorem WeightedCorrect.decision {κ : id.Kernel ℝ} {u : Utility id ℝ} {e : Evidence id}
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ} (h : WeightedCorrect κ u e s σ)
    (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (d : id.D) (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d) :
    WeightedCorrect κ u e (s.decision d) (Function.update σ d (s.policy d hi)) := by
  have hn : id.action d ∉ Rᶜ := by simpa using hd
  have hinj := (id.closed_iff.1 hclosed).2.1
  have hinfo := info_disjoint d hi
  let f := choice (id.action d) (collect (bucket (id.action d) s.valuations))
  have hpi : ∀ x a, (s.policy d hi).kernel x a = if a = f x then 1 else 0 := by
    intro x a
    rfl
  have heval : ∀ (F : id.Assignment → ℝ) (x : id.Assignment),
      marg (insert (id.action d) Rᶜ)
      (fun y => freeJoint κ (insert (id.action d) Rᶜ)
        (Function.update σ d (s.policy d hi)) y * F y) x =
      marg Rᶜ (fun y => freeJoint κ Rᶜ σ y * F y) (Function.update x (id.action d) (f x)) := by
    intro F x
    rw [decision_marginal κ Rᶜ σ hinj d hn hinfo]
    simp [hpi, ite_mul]
  have hp : ∀ x a, (collect s.valuations).prob (Function.update x (id.action d) a) =
      (collect s.valuations).prob x := by
    intro x a
    rw [h.mass, h.mass]
    exact e.probability_independent κ hclosed ord hloc hnorm Rᶜ σ d hn
      (by simpa using information_boundary d hi) x a
  constructor
  · intro x
    change (collect (decisionStep (id.action d) s.valuations)).prob x = _
    rw [(decisionStep_eval _ _ hp x).1, h.mass, compl_erase, heval]
  · intro x
    change (collect (decisionStep (id.action d) s.valuations)).weight x = _
    rw [weight, (decisionStep_eval _ _ hp x).1, (decisionStep_eval _ _ hp x).2]
    change (collect s.valuations).weight (Function.update x (id.action d) (f x)) = _
    rw [h.realizes, compl_erase, heval]
  · intro τ hτ x
    change _ ≤ (collect (decisionStep (id.action d) s.valuations)).weight x
    rw [compl_erase]
    have hc := decision_marginal κ Rᶜ τ hinj d hn hinfo (τ d)
      (fun y => e.likelihood y * totalUtility u y) x
    simp only [Function.update_eq_self] at hc
    rw [hc]
    calc
      _ ≤ ∑ a, (τ d).kernel x a * (collect (decisionStep (id.action d) s.valuations)).weight x :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          ((h.dominates τ hτ _).trans (decisionStep_dominates _ _ hp x a)) (hτ d x a)
      _ = _ := by rw [← Finset.sum_mul, (τ d).normalised x, one_mul]

theorem run_weighted_correct {κ : id.Kernel ℝ} {u : Utility id ℝ} {e : Evidence id}
    (hclosed : id.Closed) (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ)
    (h : WeightedCorrect κ u e s σ) :
    WeightedCorrect κ u e (run plan s σ).1 (run plan s σ).2 := by
  induction plan generalizing σ with
  | done => exact h
  | chance v hv hc next ih => exact ih (s.chance v) σ (h.chance v hv hc)
  | decision d hd hi next ih =>
    exact ih (s.decision d) _ (h.decision hclosed ord hloc hnorm d hd hi)

def initialEvidence (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) : State id Finset.univ where
  valuations := e.valuation :: (initial κ hloc hnonneg u hu).valuations
  supported := Finset.subset_univ _

theorem initialEvidence_correct (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) (σ : Strategy id ℝ) :
    WeightedCorrect κ u e (initialEvidence κ hloc hnonneg u hu e) σ := by
  constructor
  · intro x
    simp [initialEvidence, collect, combine, Evidence.valuation, initial_prob,
      marg_empty, freeJoint_empty, mul_comm]
  · intro x
    simp [initialEvidence, collect, combine, Evidence.valuation, initial_prob, initial_util,
      marg_empty, freeJoint_empty, weight]
    ring
  · intro τ _ x
    simp [initialEvidence, collect, combine, Evidence.valuation, initial_prob, initial_util,
      marg_empty, freeJoint_empty, weight]
    exact le_of_eq (by ring)

def solveEvidence (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (e : Evidence id) : Solution id :=
  let result := run (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e) defaultStrategy
  ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩

/-- **DVE with action-independent evidence.** Positive evidence mass is the explicit boundary.
The output policy realizes its conditional value and dominates every admissible stochastic
competitor. Zero information rows inside a positive-mass evidence event remain allowed. -/
theorem solveEvidence_spec (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) (hpositive : 0 < evidenceMass κ defaultStrategy e) :
    let sol := solveEvidence κ hloc hnonneg u hu ord nf e
    sol.strategy.Deterministic ∧ conditionalEU κ sol.strategy u e = sol.value ∧
      ∀ σ : Strategy id ℝ, σ.Nonneg → conditionalEU κ σ u e ≤ sol.value := by
  let result := run (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e) defaultStrategy
  have hc : WeightedCorrect κ u e result.1 result.2 := run_weighted_correct hclosed ord hloc hnorm
    _ _ _ (initialEvidence_correct κ hloc hnonneg u hu e _)
  have hd : result.2.Deterministic :=
    run_deterministic _ _ _ defaultStrategy_deterministic
  let Z := evidenceMass κ defaultStrategy e
  have hp : (collect result.1.valuations).prob (baseAssignment id) = Z := by
    rw [hc.mass, Finset.compl_empty, freeJoint_univ, marg_univ]
    exact evidenceMass_independent e κ hclosed ord hloc hnorm result.2 defaultStrategy
  have hr : evidenceNumerator κ result.2 u e =
      Z * (collect result.1.valuations).util (baseAssignment id) := by
    have h := hc.realizes (baseAssignment id)
    rw [weight, hp, Finset.compl_empty, freeJoint_univ, marg_univ] at h
    simpa only [evidenceNumerator, mul_assoc] using h.symm
  have ho : ∀ σ : Strategy id ℝ, σ.Nonneg →
      evidenceNumerator κ σ u e ≤ Z * (collect result.1.valuations).util (baseAssignment id) := by
    intro σ hσ
    have h := hc.dominates σ hσ (baseAssignment id)
    rw [weight, hp, Finset.compl_empty, freeJoint_univ, marg_univ] at h
    simpa only [evidenceNumerator, mul_assoc] using h
  change result.2.Deterministic ∧ conditionalEU κ result.2 u e =
    (collect result.1.valuations).util (baseAssignment id) ∧
      ∀ σ : Strategy id ℝ, σ.Nonneg → conditionalEU κ σ u e ≤
        (collect result.1.valuations).util (baseAssignment id)
  refine ⟨hd, ?_, ?_⟩
  · unfold conditionalEU
    rw [hr, evidenceMass_independent e κ hclosed ord hloc hnorm result.2 defaultStrategy]
    exact mul_div_cancel_left₀ _ (ne_of_gt hpositive)
  · intro σ hσ
    unfold conditionalEU
    rw [evidenceMass_independent e κ hclosed ord hloc hnorm σ defaultStrategy]
    apply (div_le_iff₀ hpositive).2
    simpa only [mul_comm] using ho σ hσ

/-- The evidence check uses the driver-computed mass, not an exhaustive oracle. -/
def solveEvidenceChecked (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (e : Evidence id) : Option (Solution id) :=
  let result := run (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e) defaultStrategy
  if 0 < (collect result.1.valuations).prob (baseAssignment id) then
    some ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩
  else none

theorem runEvidence_mass (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) :
    let result := run (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e) defaultStrategy
    (collect result.1.valuations).prob (baseAssignment id) = evidenceMass κ defaultStrategy e := by
  dsimp only
  have hc := run_weighted_correct hclosed ord hloc hnorm (nf.plan ord.no_self_info)
    (initialEvidence κ hloc hnonneg u hu e) defaultStrategy
    (initialEvidence_correct κ hloc hnonneg u hu e _)
  rw [hc.mass, Finset.compl_empty, freeJoint_univ, marg_univ]
  exact evidenceMass_independent e κ hclosed ord hloc hnorm _ defaultStrategy

/-- Exact positive-mass boundary: the checked driver returns a solution precisely when
the evidence has positive mass. No choice of strategy can rescue a zero-mass event. -/
theorem solveEvidenceChecked_eq (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) :
    solveEvidenceChecked κ hloc hnonneg u hu ord nf e =
      if 0 < evidenceMass κ defaultStrategy e then
        some (solveEvidence κ hloc hnonneg u hu ord nf e) else none := by
  unfold solveEvidenceChecked
  dsimp only
  rw [runEvidence_mass κ hclosed ord nf hloc hnorm hnonneg u hu e]
  rfl

/-- With valid nonnegative inputs, failure of the evidence check means exactly zero mass. -/
theorem solveEvidenceChecked_none_iff (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) :
    solveEvidenceChecked κ hloc hnonneg u hu ord nf e = none ↔
      evidenceMass κ defaultStrategy e = 0 := by
  rw [solveEvidenceChecked_eq κ hclosed ord nf hloc hnorm hnonneg u hu e]
  by_cases hp : 0 < evidenceMass κ defaultStrategy e
  · simp [hp, ne_of_gt hp]
  · have hz : evidenceMass κ defaultStrategy e = 0 := le_antisymm (le_of_not_gt hp)
      (evidenceMass_nonneg e κ hnonneg _ (deterministic_nonneg _ defaultStrategy_deterministic))
    simp [hz]

def weightedUtility (u : Utility id ℝ) (e : Evidence id) : Utility id ℝ :=
  fun j x => e.likelihood x * u j x

theorem expectedUtility_weighted (κ : id.Kernel ℝ) (σ : Strategy id ℝ)
    (u : Utility id ℝ) (e : Evidence id) :
    expectedUtility κ σ (weightedUtility u e) = evidenceNumerator κ σ u e := by
  simp only [expectedUtility, weightedUtility, totalUtility, evidenceNumerator,
    ← Finset.mul_sum, mul_assoc]

/-- An independent global oracle, obtained by weighting utilities and dividing by the
strategy-independent evidence mass. This definition is not used by either driver. -/
def conditionalOptimalValue (κ : id.Kernel ℝ) (u : Utility id ℝ) (e : Evidence id) : ℝ :=
  optimalValue κ (weightedUtility u e) / evidenceMass κ defaultStrategy e

/-- The evidence driver equals the global oracle, under the same explicit positive-mass
and structural evidence assumptions as its realization/dominance theorem. -/
theorem solveEvidence_eq_optimal (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) (hpositive : 0 < evidenceMass κ defaultStrategy e) :
    (solveEvidence κ hloc hnonneg u hu ord nf e).value = conditionalOptimalValue κ u e := by
  let sol := solveEvidence κ hloc hnonneg u hu ord nf e
  have hs := solveEvidence_spec κ hclosed ord nf hloc hnorm hnonneg u hu e hpositive
  have he (σ : Strategy id ℝ) : conditionalEU κ σ u e =
      expectedUtility κ σ (weightedUtility u e) / evidenceMass κ defaultStrategy e := by
    rw [conditionalEU, expectedUtility_weighted,
      evidenceMass_independent e κ hclosed ord hloc hnorm σ defaultStrategy]
  apply le_antisymm
  · rw [← hs.2.1, he]
    exact div_le_div_of_nonneg_right
      (expectedUtility_le_optimalValue κ _ sol.strategy (deterministic_nonneg _ hs.1)) hpositive.le
  · obtain ⟨σ, _, hσ, hv⟩ := optimalValue_attained κ (weightedUtility u e)
    rw [conditionalOptimalValue, ← hv, ← he]
    exact hs.2.2 σ hσ

end
end InfluenceDiagramsProofs.DVE
