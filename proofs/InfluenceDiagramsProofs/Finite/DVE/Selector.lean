import InfluenceDiagramsProofs.Finite.DVE.Guard.Complete
import InfluenceDiagramsProofs.Finite.OrderedPolicies

/-!
# The bucket driver parameterised by its selector, and first-label policy tables

`DVE.run` records, at every decision, a fixed classical maximizer of the bucket utility row.
Julia's `argmax_table` instead takes the first maximizing action label. This module
parameterises the driver by an arbitrary maximizing `Selector` without editing `run`:
`runWith_classical` proves that the original driver is the classical instance, and
`runWith_state` proves that the computed valuations never depend on the selector.

For every selector the returned deterministic strategy realizes the reported value and
attains the existing global optimum (`solveWith_spec`); the exact all-row guard never rejects
(`solveGuardedWith_spec`); and the same holds for action-independent evidence
(`solveEvidenceWith_spec`, `solveEvidenceGuardedWith_eq`). A decision step in fact needs a
maximizer only on rows of positive probability (`Inv.decisionOf`); this is what later lets
explicitly conditioned inputs be compared with the likelihood representation.

`Selector.ordered` picks `firstArgmax` in a supplied linear order on every action space: the
least maximizing state, which is Julia's first-label rule when the order is state position.
`solveOrdered_table` proves that the returned policy is **exactly** `orderedTable` of the
bucket-utility score on every information row, reachable or not, so the table is uniquely
determined by the scores. `solveOrdered_semantic` identifies the choice semantically on every
row of positive reach probability: it is the least action maximizing the unnormalized expected
utility of acting there and then following the returned later policies. A row of zero
probability has no semantic score; there the table is fixed by the bucket representatives.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

variable {id : FinInfluenceDiagram}

/-! ## Selectors and bucket scores -/

/-- A local action selector: any rule returning a maximizer of a finite action score. -/
structure Selector (id : FinInfluenceDiagram) where
  pick : (d : id.D) → (id.states (id.action d) → ℝ) → id.states (id.action d)
  maximizes : ∀ (d : id.D) (f : id.states (id.action d) → ℝ) (b : id.states (id.action d)),
    f b ≤ f (pick d f)

/-- The fixed classical choice used by `DVE.run`. -/
def Selector.classical (id : FinInfluenceDiagram) : Selector id where
  pick _ f := argmax f
  maximizes _ f b := le_argmax f b

/-- The least maximizing state in a supplied order: the first-label rule. -/
def Selector.ordered (id : FinInfluenceDiagram)
    [∀ d : id.D, LinearOrder (id.states (id.action d))] : Selector id where
  pick _ f := firstArgmax f
  maximizes _ f b := firstArgmax_maximizes f b

/-- The utility row of the bucket of `a` at `x`, as a function of the value of `a`. -/
def bucketScore {bn : FinBayesNet} (vs : List (Valuation bn)) (a : bn.V)
    (x : bn.Assignment) (b : bn.states a) : ℝ :=
  (collect (bucket a vs)).util (Function.update x a b)

theorem util_update_eq_score {bn : FinBayesNet} (vs : List (Valuation bn)) (a : bn.V)
    (x : bn.Assignment) (b : bn.states a) :
    (collect vs).util (Function.update x a b) =
      bucketScore vs a x b + (collect (outside a vs)).util x := by
  rw [(collect_partition a vs _).2, util_update_of_notMem _ (outside_notMem a vs)]
  rfl

/-- On a positive row that is constant in `a`, comparing bucket utility scores is comparing
the weighted valuation of the whole state. -/
theorem score_le_iff_weight_le {bn : FinBayesNet} (vs : List (Valuation bn)) (a : bn.V)
    (x : bn.Assignment)
    (hp : ∀ b, (collect vs).prob (Function.update x a b) = (collect vs).prob x)
    (hpos : 0 < (collect vs).prob x) (b c : bn.states a) :
    bucketScore vs a x b ≤ bucketScore vs a x c ↔
      (collect vs).weight (Function.update x a b) ≤
        (collect vs).weight (Function.update x a c) := by
  simp only [weight, hp, util_update_eq_score]
  constructor
  · intro h
    exact mul_le_mul_of_nonneg_left (by linarith) hpos.le
  · intro h
    have := le_of_mul_le_mul_left h hpos
    linarith

/-- `firstArgmax` depends only on the order that a score induces on the actions. -/
theorem firstArgmax_congr {A : Type} [Fintype A] [Nonempty A] [LinearOrder A] {f g : A → ℝ}
    (h : ∀ a b, f a ≤ f b ↔ g a ≤ g b) : firstArgmax f = firstArgmax g := by
  apply le_antisymm
  · exact firstArgmax_first f _ fun b => (h b _).2 (firstArgmax_maximizes g b)
  · exact firstArgmax_first g _ fun b => (h b _).1 (firstArgmax_maximizes f b)

theorem firstArgmax_score_eq_weight {bn : FinBayesNet} (vs : List (Valuation bn)) (a : bn.V)
    [LinearOrder (bn.states a)] (x : bn.Assignment)
    (hp : ∀ b, (collect vs).prob (Function.update x a b) = (collect vs).prob x)
    (hpos : 0 < (collect vs).prob x) :
    firstArgmax (bucketScore vs a x) =
      firstArgmax (fun b => (collect vs).weight (Function.update x a b)) :=
  firstArgmax_congr (score_le_iff_weight_le vs a x hp hpos)

theorem bucketScore_local {R : Finset id.V} (s : State id R) (d : id.D)
    (hi : R.erase (id.action d) = id.info d) (x y : id.Assignment)
    (h : ∀ v ∈ id.info d, x v = y v) :
    bucketScore s.valuations (id.action d) x = bucketScore s.valuations (id.action d) y := by
  funext b
  unfold bucketScore
  apply (collect (bucket (id.action d) s.valuations)).util_local
  apply update_agree
  intro v hv
  apply h
  rw [← hi]
  exact Finset.erase_subset_erase _ ((filter_scope_subset _ s.valuations).trans s.supported) hv

/-! ## The parameterised driver -/

/-- The deterministic local policy that `sel` reads off the bucket utility of `d`. -/
def State.policyWith (sel : Selector id) {R : Finset id.V} (d : id.D) (s : State id R)
    (hi : R.erase (id.action d) = id.info d) : Policy id ℝ d :=
  Policy.ofFun (fun x => sel.pick d (bucketScore s.valuations (id.action d) x))
    (fun x y h => congrArg (sel.pick d) (bucketScore_local s d hi x y h))

/-- The bucket driver of `run`, with the local selector as a parameter. -/
def runWith (sel : Selector id) {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (σ : Strategy id ℝ) : State id ∅ × Strategy id ℝ :=
  match plan with
  | .done => (s, σ)
  | .chance v _ _ next => runWith sel next (s.chance v) σ
  | .decision d _ hi next =>
    runWith sel next (s.decision d) (Function.update σ d (s.policyWith sel d hi))

/-- The valuations alone; no selector and no strategy enter them. -/
def runState {R : Finset id.V} (plan : Plan id R) (s : State id R) : State id ∅ :=
  match plan with
  | .done => s
  | .chance v _ _ next => runState next (s.chance v)
  | .decision d _ _ next => runState next (s.decision d)

theorem runWith_state (sel : Selector id) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) : (runWith sel plan s σ).1 = runState plan s := by
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih => exact ih (s.chance v) σ
  | decision d _ hi next ih =>
    exact ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))

theorem run_state {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ) :
    (run plan s σ).1 = runState plan s := by
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih => exact ih (s.chance v) σ
  | decision d _ hi next ih => exact ih (s.decision d) (Function.update σ d (s.policy d hi))

/-- The existing driver is the classical instance of the parameterised one. -/
theorem runWith_classical {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (σ : Strategy id ℝ) : runWith (Selector.classical id) plan s σ = run plan s σ := by
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih => exact ih (s.chance v) σ
  | decision d _ hi next ih =>
    show runWith (Selector.classical id) next (s.decision d)
        (Function.update σ d (s.policyWith (Selector.classical id) d hi)) =
      run next (s.decision d) (Function.update σ d (s.policy d hi))
    rw [ih]
    rfl

/-- A decision is only ever assigned while its action is still to be eliminated. -/
theorem runWith_snd_of_notMem (sel : Selector id) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) (e : id.D) (he : id.action e ∉ R) :
    (runWith sel plan s σ).2 e = σ e := by
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih => exact ih (s.chance v) σ (fun h => he (Finset.mem_of_mem_erase h))
  | decision d hd hi next ih =>
    refine (ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))
      (fun h => he (Finset.mem_of_mem_erase h))).trans ?_
    exact Function.update_of_ne (fun h : e = d => he (by rw [h]; exact hd)) _ _

theorem runWith_policy_at_step (sel : Selector id) {R : Finset id.V} (d : id.D)
    (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d)
    (next : Plan id (R.erase (id.action d))) (s : State id R) (σ : Strategy id ℝ) :
    (runWith sel (.decision d hd hi next) s σ).2 d = s.policyWith sel d hi := by
  refine (runWith_snd_of_notMem sel next (s.decision d)
    (Function.update σ d (s.policyWith sel d hi)) d (Finset.notMem_erase _ _)).trans ?_
  exact Function.update_self _ _ _

theorem runWith_deterministic (sel : Selector id) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) (hσ : σ.Deterministic) :
    (runWith sel plan s σ).2.Deterministic := by
  induction plan generalizing σ with
  | done => exact hσ
  | chance v _ _ next ih => exact ih (s.chance v) σ hσ
  | decision d _ hi next ih =>
    apply ih (s.decision d) (Function.update σ d (s.policyWith sel d hi))
    intro e
    by_cases h : e = d
    · subst e
      simp only [Function.update_self]
      exact ⟨_, fun x y h => congrArg (sel.pick d) (bucketScore_local s d hi x y h), rfl⟩
    · rw [Function.update_of_ne h]
      exact hσ e

/-! ## The invariant with an arbitrary weight, and decisions maximizing on positive rows -/

/-- `Correct` and `WeightedCorrect` with an arbitrary weight `L` on assignments. -/
structure Inv (κ : id.Kernel ℝ) (u : Utility id ℝ) (L : id.Assignment → ℝ)
    {R : Finset id.V} (s : State id R) (σ : Strategy id ℝ) : Prop where
  mass : ∀ x, (collect s.valuations).prob x = marg Rᶜ (fun y => freeJoint κ Rᶜ σ y * L y) x
  realizes : ∀ x, (collect s.valuations).weight x =
    marg Rᶜ (fun y => freeJoint κ Rᶜ σ y * (L y * totalUtility u y)) x
  dominates : ∀ τ : Strategy id ℝ, τ.Nonneg → ∀ x,
    marg Rᶜ (fun y => freeJoint κ Rᶜ τ y * (L y * totalUtility u y)) x ≤
      (collect s.valuations).weight x

/-- Free-action independence of the weighted probability marginal, as proved structurally
in `Semantics.lean` and `Evidence.lean`. -/
def Independent (κ : id.Kernel ℝ) (L : id.Assignment → ℝ) : Prop :=
  ∀ (E : Finset id.V) (σ : Strategy id ℝ) (d : id.D), id.action d ∉ E →
    Eᶜ ⊆ insert (id.action d) (id.info d) → ∀ x a,
      marg E (fun y => freeJoint κ E σ y * L y) (Function.update x (id.action d) a) =
        marg E (fun y => freeJoint κ E σ y * L y) x

theorem independent_one (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) : Independent κ (fun _ => 1) := by
  intro E σ d hd hb x a
  simpa only [mul_one] using
    probability_independent κ hclosed (RankedOrder.ofOrder ord) hloc hnorm E σ d hd hb x a

theorem independent_evidence (e : Evidence id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) :
    Independent κ e.likelihood :=
  fun E σ d hd hb x a => e.probability_independent κ hclosed ord hloc hnorm E σ d hd hb x a

theorem Inv.ofCorrect {κ : id.Kernel ℝ} {u : Utility id ℝ} {R : Finset id.V}
    {s : State id R} {σ : Strategy id ℝ} (h : Correct κ u s σ) : Inv κ u (fun _ => 1) s σ where
  mass x := by simpa only [mul_one] using h.mass x
  realizes x := by simpa only [one_mul] using h.realizes x
  dominates τ hτ x := by simpa only [one_mul] using h.dominates τ hτ x

theorem Inv.ofWeighted {κ : id.Kernel ℝ} {u : Utility id ℝ} {e : Evidence id}
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ} (h : WeightedCorrect κ u e s σ) :
    Inv κ u e.likelihood s σ :=
  ⟨h.mass, h.realizes, h.dominates⟩

theorem Inv.chance {κ : id.Kernel ℝ} {u : Utility id ℝ} {L : id.Assignment → ℝ}
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ} (h : Inv κ u L s σ)
    (v : id.V) (hv : v ∈ R) (hc : ∀ d, id.action d ≠ v) :
    Inv κ u L (s.chance v) σ := by
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

theorem Inv.prob_update {κ : id.Kernel ℝ} {u : Utility id ℝ} {L : id.Assignment → ℝ}
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ} (h : Inv κ u L s σ)
    (hind : Independent κ L) (d : id.D) (hd : id.action d ∈ R)
    (hi : R.erase (id.action d) = id.info d) (x : id.Assignment) (a : id.states (id.action d)) :
    (collect s.valuations).prob (Function.update x (id.action d) a) =
      (collect s.valuations).prob x := by
  rw [h.mass, h.mass]
  exact hind Rᶜ σ d (by simpa using hd) (by simpa using information_boundary d hi) x a

/-- The decision step with an arbitrary deterministic policy that maximizes the bucket utility
on every row of positive probability. What it chooses on zero-probability rows is irrelevant
to mass, realization and dominance. -/
theorem Inv.decisionOf {κ : id.Kernel ℝ} {u : Utility id ℝ} {L : id.Assignment → ℝ}
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ} (h : Inv κ u L s σ)
    (hind : Independent κ L) (hclosed : id.Closed)
    (d : id.D) (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d)
    (π : Policy id ℝ d) (f : id.Assignment → id.states (id.action d))
    (hπ : ∀ x a, π.kernel x a = if a = f x then 1 else 0)
    (hmax : ∀ x, (collect s.valuations).prob x ≠ 0 → ∀ b,
      bucketScore s.valuations (id.action d) x b ≤
        bucketScore s.valuations (id.action d) x (f x)) :
    Inv κ u L (s.decision d) (Function.update σ d π) := by
  have hn : id.action d ∉ Rᶜ := by simpa using hd
  have hinj := (id.closed_iff.1 hclosed).2.1
  have hinfo := info_disjoint d hi
  have heval : ∀ (F : id.Assignment → ℝ) (x : id.Assignment),
      marg (insert (id.action d) Rᶜ)
      (fun y => freeJoint κ (insert (id.action d) Rᶜ) (Function.update σ d π) y * F y) x =
      marg Rᶜ (fun y => freeJoint κ Rᶜ σ y * F y) (Function.update x (id.action d) (f x)) := by
    intro F x
    rw [decision_marginal κ Rᶜ σ hinj d hn hinfo]
    simp [hπ, ite_mul]
  have hp := h.prob_update hind d hd hi
  constructor
  · intro x
    change (collect (decisionStep (id.action d) s.valuations)).prob x = _
    rw [(decisionStep_eval _ _ hp x).1, hp, compl_erase, heval, ← h.mass, hp]
  · intro x
    change (collect (decisionStep (id.action d) s.valuations)).weight x = _
    rw [compl_erase, heval, ← h.realizes]
    simp only [weight]
    rw [(decisionStep_eval _ _ hp x).1, (decisionStep_eval _ _ hp x).2, hp, hp]
    by_cases hz : (collect s.valuations).prob x = 0
    · rw [hz, zero_mul, zero_mul]
    · congr 1
      rw [util_update_eq_score, util_update_eq_score]
      congr 1
      exact le_antisymm (hmax x hz _) (le_argmax _ (f x))
  · intro τ hτ x
    change _ ≤ (collect (decisionStep (id.action d) s.valuations)).weight x
    rw [compl_erase]
    have hc := decision_marginal κ Rᶜ τ hinj d hn hinfo (τ d)
      (fun y => L y * totalUtility u y) x
    simp only [Function.update_eq_self] at hc
    rw [hc]
    calc
      _ ≤ ∑ a, (τ d).kernel x a * (collect (decisionStep (id.action d) s.valuations)).weight x :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          ((h.dominates τ hτ _).trans (decisionStep_dominates _ _ hp x a)) (hτ d x a)
      _ = _ := by rw [← Finset.sum_mul, (τ d).normalised x, one_mul]

theorem Inv.decisionWith {κ : id.Kernel ℝ} {u : Utility id ℝ} {L : id.Assignment → ℝ}
    {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ} (h : Inv κ u L s σ)
    (hind : Independent κ L) (hclosed : id.Closed) (sel : Selector id)
    (d : id.D) (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d) :
    Inv κ u L (s.decision d) (Function.update σ d (s.policyWith sel d hi)) :=
  h.decisionOf hind hclosed d hd hi _
    (fun x => sel.pick d (bucketScore s.valuations (id.action d) x)) (fun _ _ => rfl)
    (fun _ _ b => sel.maximizes d _ b)

theorem runWith_inv (sel : Selector id) {κ : id.Kernel ℝ} {u : Utility id ℝ}
    {L : id.Assignment → ℝ} (hind : Independent κ L) (hclosed : id.Closed)
    {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ)
    (h : Inv κ u L s σ) : Inv κ u L (runWith sel plan s σ).1 (runWith sel plan s σ).2 := by
  induction plan generalizing σ with
  | done => exact h
  | chance v hv hc next ih => exact ih (s.chance v) σ (h.chance v hv hc)
  | decision d hd hi next ih =>
    exact ih (s.decision d) _ (h.decisionWith hind hclosed sel d hd hi)

/-! ## Solvers for an arbitrary selector -/

def solveWith (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) : Solution id :=
  let result := runWith sel (nf.plan ord.no_self_info) (initial κ hloc hnonneg u hu)
    defaultStrategy
  ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩

theorem solveWith_classical (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) :
    solveWith (Selector.classical id) κ hloc hnonneg u hu ord nf =
      solve κ hloc hnonneg u hu ord nf := by
  unfold solveWith solve solvePlan
  rw [runWith_classical]

/-- The reported value does not depend on the selector. -/
theorem solveWith_value (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) :
    (solveWith sel κ hloc hnonneg u hu ord nf).value = (solve κ hloc hnonneg u hu ord nf).value := by
  show (collect (runWith sel _ _ _).1.valuations).util _ =
    (collect (run _ _ _).1.valuations).util _
  rw [runWith_state, run_state]

/-- **DVE correctness for every maximizing selector**, in particular the first-label one:
the same guarantees as `solve_spec`. -/
theorem solveWith_spec (sel : Selector id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) :
    let sol := solveWith sel κ hloc hnonneg u hu ord nf
    sol.strategy.Deterministic ∧ expectedUtility κ sol.strategy u = sol.value ∧
      sol.value = optimalValue κ u := by
  intro sol
  let result := runWith sel (nf.plan ord.no_self_info) (initial κ hloc hnonneg u hu)
    (defaultStrategy (id := id))
  have hc : Inv κ u (fun _ => 1) result.1 result.2 :=
    runWith_inv sel (independent_one κ hclosed ord hloc hnorm) hclosed _ _ _
      (Inv.ofCorrect (initial_correct κ hloc hnonneg u hu _))
  have hp : (collect result.1.valuations).prob (baseAssignment id) = 1 := by
    rw [hc.mass, Finset.compl_empty, freeJoint_univ, marg_univ]
    simpa only [mul_one] using sum_joint_instantiate_eq_one κ result.2 hclosed ord hloc hnorm
  have hr : expectedUtility κ result.2 u =
      (collect result.1.valuations).util (baseAssignment id) := by
    have h := hc.realizes (baseAssignment id)
    rw [weight, hp, one_mul, Finset.compl_empty, freeJoint_univ, marg_univ] at h
    simp only [one_mul] at h
    exact h.symm
  refine ⟨runWith_deterministic sel _ _ _ defaultStrategy_deterministic, hr, ?_⟩
  rw [show sol.value = (solveWith sel κ hloc hnonneg u hu ord nf).value from rfl,
    solveWith_value]
  exact (solve_spec κ hclosed ord nf hloc hnorm hnonneg u hu).2.2

def solveEvidenceWith (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (e : Evidence id) : Solution id :=
  let result := runWith sel (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e)
    defaultStrategy
  ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩

theorem solveEvidenceWith_value (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (e : Evidence id) :
    (solveEvidenceWith sel κ hloc hnonneg u hu ord nf e).value =
      (solveEvidence κ hloc hnonneg u hu ord nf e).value := by
  show (collect (runWith sel _ _ _).1.valuations).util _ =
    (collect (run _ _ _).1.valuations).util _
  rw [runWith_state, run_state]

theorem runWithEvidence_mass (sel : Selector id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (e : Evidence id) :
    (collect (runWith sel (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e)
      defaultStrategy).1.valuations).prob (baseAssignment id) =
        evidenceMass κ defaultStrategy e := by
  rw [runWith_state, ← run_state _ _ defaultStrategy]
  exact runEvidence_mass κ hclosed ord nf hloc hnorm hnonneg u hu e

/-- **DVE with action-independent evidence, for every maximizing selector.** At positive
evidence mass the returned deterministic strategy realizes the reported conditional value,
which is the independent conditional optimum. -/
theorem solveEvidenceWith_spec (sel : Selector id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (e : Evidence id)
    (hpositive : 0 < evidenceMass κ defaultStrategy e) :
    let sol := solveEvidenceWith sel κ hloc hnonneg u hu ord nf e
    sol.strategy.Deterministic ∧ conditionalEU κ sol.strategy u e = sol.value ∧
      sol.value = conditionalOptimalValue κ u e := by
  intro sol
  let result := runWith sel (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e)
    (defaultStrategy (id := id))
  have hc : Inv κ u e.likelihood result.1 result.2 :=
    runWith_inv sel (independent_evidence e κ hclosed ord hloc hnorm) hclosed _ _ _
      (Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu e _))
  let Z := evidenceMass κ defaultStrategy e
  have hp : (collect result.1.valuations).prob (baseAssignment id) = Z :=
    runWithEvidence_mass sel κ hclosed ord nf hloc hnorm hnonneg u hu e
  have hr : evidenceNumerator κ result.2 u e =
      Z * (collect result.1.valuations).util (baseAssignment id) := by
    have h := hc.realizes (baseAssignment id)
    rw [weight, hp, Finset.compl_empty, freeJoint_univ, marg_univ] at h
    simpa only [evidenceNumerator, mul_assoc] using h.symm
  refine ⟨runWith_deterministic sel _ _ _ defaultStrategy_deterministic, ?_, ?_⟩
  · change conditionalEU κ result.2 u e = (collect result.1.valuations).util (baseAssignment id)
    unfold conditionalEU
    rw [hr, evidenceMass_independent e κ hclosed ord hloc hnorm result.2 defaultStrategy]
    exact mul_div_cancel_left₀ _ (ne_of_gt hpositive)
  · rw [show sol.value = (solveEvidenceWith sel κ hloc hnonneg u hu ord nf e).value from rfl,
      solveEvidenceWith_value]
    exact solveEvidence_eq_optimal κ hclosed ord nf hloc hnorm hnonneg u hu e hpositive

/-! ## Checked drivers for an arbitrary selector -/

/-- `checkedRun` with the selector as a parameter; the diagnostic reads only valuations. -/
def checkedRunWith (sel : Selector id) {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (σ : Strategy id ℝ) : Option (State id ∅ × Strategy id ℝ) := by
  classical
  exact match plan with
  | .done => some (s, σ)
  | .chance v _ _ next => checkedRunWith sel next (s.chance v) σ
  | .decision d _ hi next =>
    if 0 < diagnosticSpread (id.action d) s.valuations then none
    else checkedRunWith sel next (s.decision d) (Function.update σ d (s.policyWith sel d hi))

theorem checkedRunWith_eq_runWith (sel : Selector id) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) (h : AllGuards plan s.valuations) :
    checkedRunWith sel plan s σ = some (runWith sel plan s σ) := by
  classical
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih => exact ih (s.chance v) σ h
  | decision d _ hi next ih =>
    change (if 0 < diagnosticSpread (id.action d) s.valuations then none else _) = _
    rw [if_neg (not_lt.mpr ((exactGuard_iff_diagnostic _ _).1 h.1))]
    exact ih (s.decision d) _ h.2

def solveGuardedWith (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) : Option (Solution id) :=
  (checkedRunWith sel (nf.plan ord.no_self_info) (initial κ hloc hnonneg u hu)
    defaultStrategy).map
    (fun result => ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩)

theorem solveGuardedWith_eq (sel : Selector id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) :
    solveGuardedWith sel κ hloc hnonneg u hu ord nf =
      some (solveWith sel κ hloc hnonneg u hu ord nf) := by
  unfold solveGuardedWith
  rw [checkedRunWith_eq_runWith sel _ _ _
    (all_guards_complete κ hclosed ord hloc hnorm hnonneg u hu _)]
  rfl

/-- **The checked driver with any maximizing selector**, in particular the first-label one,
has the guarantees of `solveGuarded_spec`: the exact all-row guard never rejects, and the
returned deterministic strategy realizes the reported value and attains the global optimum. -/
theorem solveGuardedWith_spec (sel : Selector id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) :
    ∃ sol : Solution id, solveGuardedWith sel κ hloc hnonneg u hu ord nf = some sol ∧
      sol.strategy.Deterministic ∧ expectedUtility κ sol.strategy u = sol.value ∧
      sol.value = optimalValue κ u :=
  ⟨_, solveGuardedWith_eq sel κ hclosed ord nf hloc hnorm hnonneg u hu,
    solveWith_spec sel κ hclosed ord nf hloc hnorm hnonneg u hu⟩

def solveEvidenceGuardedWith (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (e : Evidence id) : Option (Solution id) :=
  (checkedRunWith sel (nf.plan ord.no_self_info) (initialEvidence κ hloc hnonneg u hu e)
    defaultStrategy).bind
    (fun result => if 0 < (collect result.1.valuations).prob (baseAssignment id) then
      some ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩ else none)

/-- The checked evidence driver with any selector answers exactly at positive mass. -/
theorem solveEvidenceGuardedWith_eq (sel : Selector id) (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (e : Evidence id) :
    solveEvidenceGuardedWith sel κ hloc hnonneg u hu ord nf e =
      if 0 < evidenceMass κ defaultStrategy e then
        some (solveEvidenceWith sel κ hloc hnonneg u hu ord nf e) else none := by
  unfold solveEvidenceGuardedWith
  rw [checkedRunWith_eq_runWith sel _ _ _
    (all_guards_complete_evidence κ hclosed ord hloc hnorm hnonneg u hu e _), Option.bind_some]
  show (if 0 < (collect (runWith sel (nf.plan ord.no_self_info)
      (initialEvidence κ hloc hnonneg u hu e) defaultStrategy).1.valuations).prob
        (baseAssignment id) then _ else none) = _
  rw [runWithEvidence_mass sel κ hclosed ord nf hloc hnorm hnonneg u hu e]
  rfl

/-! ## First-label tables -/

/-- The bucket-utility score of `d` at the moment the plan eliminates its action. -/
def decisionScore {R : Finset id.V} (plan : Plan id R) (s : State id R) (d : id.D) :
    id.Assignment → id.states (id.action d) → ℝ :=
  match plan with
  | .done => fun _ _ => 0
  | .chance v _ _ next => decisionScore next (s.chance v) d
  | .decision d' _ _ next =>
    if d' = d then bucketScore s.valuations (id.action d)
    else decisionScore next (s.decision d') d

theorem decisionScore_local (hinj : Function.Injective id.action) {R : Finset id.V}
    (plan : Plan id R) (s : State id R) (d : id.D) (hd : id.action d ∈ R) :
    LocalOn (id.info d) (decisionScore plan s d) := by
  induction plan with
  | done => simp at hd
  | chance v _ hc next ih =>
    exact ih (s.chance v) (Finset.mem_erase.2 ⟨hc d, hd⟩)
  | decision d' hd' hi next ih =>
    by_cases hdd : d' = d
    · subst hdd
      intro x y h
      show (if d' = d' then bucketScore s.valuations (id.action d')
          else decisionScore next (s.decision d') d') x =
        (if d' = d' then bucketScore s.valuations (id.action d')
          else decisionScore next (s.decision d') d') y
      rw [if_pos rfl]
      exact bucketScore_local s d' hi x y h
    · intro x y h
      show (if d' = d then bucketScore s.valuations (id.action d)
          else decisionScore next (s.decision d') d) x =
        (if d' = d then bucketScore s.valuations (id.action d)
          else decisionScore next (s.decision d') d) y
      rw [if_neg hdd]
      exact ih (s.decision d') (Finset.mem_erase.2 ⟨fun he => hdd (hinj he).symm, hd⟩) x y h

/-- Every returned policy row is the selector's choice on the recorded bucket score. -/
theorem runWith_kernel (sel : Selector id) (hinj : Function.Injective id.action)
    {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ) (d : id.D)
    (hd : id.action d ∈ R) (x : id.Assignment) (a : id.states (id.action d)) :
    ((runWith sel plan s σ).2 d).kernel x a =
      if a = sel.pick d (decisionScore plan s d x) then 1 else 0 := by
  induction plan generalizing σ with
  | done => simp at hd
  | chance v _ hc next ih =>
    exact ih (s.chance v) σ (Finset.mem_erase.2 ⟨hc d, hd⟩)
  | decision d' hd' hi next ih =>
    by_cases hdd : d' = d
    · subst hdd
      rw [runWith_policy_at_step]
      show (if a = sel.pick d' (bucketScore s.valuations (id.action d') x) then (1 : ℝ) else 0) =
        if a = sel.pick d' ((if d' = d' then bucketScore s.valuations (id.action d')
          else decisionScore next (s.decision d') d') x) then 1 else 0
      rw [if_pos rfl]
    · have hne : id.action d ≠ id.action d' := fun he => hdd (hinj he).symm
      refine (ih (s.decision d') (Function.update σ d' (s.policyWith sel d' hi))
        (Finset.mem_erase.2 ⟨hne, hd⟩)).trans ?_
      show (if a = sel.pick d (decisionScore next (s.decision d') d x) then (1 : ℝ) else 0) =
        if a = sel.pick d ((if d' = d then bucketScore s.valuations (id.action d)
          else decisionScore next (s.decision d') d) x) then 1 else 0
      rw [if_neg hdd]

/-- The score row the solver maximizes for `d`: the bucket utility when `d` is eliminated. -/
def solveScore (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (d : id.D) : id.Assignment → id.states (id.action d) → ℝ :=
  decisionScore (nf.plan ord.no_self_info) (initial κ hloc hnonneg u hu) d

theorem solveScore_local (κ : id.Kernel ℝ) (hclosed : id.Closed) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (d : id.D) :
    LocalOn (id.info d) (solveScore κ hloc hnonneg u hu ord nf d) :=
  decisionScore_local (id.closed_iff.1 hclosed).2.1 _ _ d (Finset.mem_univ _)

section Ordered

variable [∀ d : id.D, LinearOrder (id.states (id.action d))]

/-- **First-label table identity.** On every information row, reachable or not, the ordered
solver's policy is the least maximizing action of its bucket-utility row, read from the
finite table over exactly the information variables. The table is therefore unique. -/
theorem solveOrdered_table (κ : id.Kernel ℝ) (hclosed : id.Closed) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) (d : id.D) (x : id.Assignment)
    (a : id.states (id.action d)) :
    ((solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d).kernel x a =
      if a = orderedTable (solveScore κ hloc hnonneg u hu ord nf d) (infoAssignment d x)
      then 1 else 0 := by
  rw [orderedTable_reconstruct _ (solveScore_local κ hclosed hloc hnonneg u hu ord nf d)]
  exact runWith_kernel _ (id.closed_iff.1 hclosed).2.1 _ _ _ d (Finset.mem_univ _) x a

end Ordered

/-! ## The semantic score on reachable rows -/

/-- The weighted probability of the information row of `d` at `x`: every variable outside
`d`'s information set and action is summed, with the later policies of `σ` active. -/
def reach (κ : id.Kernel ℝ) (L : id.Assignment → ℝ) (σ : Strategy id ℝ) (d : id.D)
    (x : id.Assignment) : ℝ :=
  marg (insert (id.action d) (id.info d))ᶜ
    (fun y => freeJoint κ (insert (id.action d) (id.info d))ᶜ σ y * L y) x

/-- The unnormalized expected utility of choosing `b` at `d` on the information row of `x`
and following the later policies of `σ`. It is a semantic quantity: it mentions no bucket,
scope or utility representative. -/
def continuation (κ : id.Kernel ℝ) (u : Utility id ℝ) (L : id.Assignment → ℝ)
    (σ : Strategy id ℝ) (d : id.D) (x : id.Assignment) (b : id.states (id.action d)) : ℝ :=
  marg (insert (id.action d) (id.info d))ᶜ
    (fun y => freeJoint κ (insert (id.action d) (id.info d))ᶜ σ y * (L y * totalUtility u y))
    (Function.update x (id.action d) b)

theorem freeJoint_nonneg (κ : id.Kernel ℝ) (hκ : ∀ m x a, 0 ≤ κ m x a) (E : Finset id.V)
    (σ : Strategy id ℝ) (hσ : σ.Nonneg) (x : id.Assignment) : 0 ≤ freeJoint κ E σ x := by
  unfold freeJoint
  refine mul_nonneg (Finset.prod_nonneg fun m _ => hκ m x _) (Finset.prod_nonneg fun d _ => ?_)
  split_ifs
  · exact hσ d x _
  · exact zero_le_one

/-- `reach` is a probability weight, so "nonzero" and "positive" coincide. -/
theorem reach_nonneg (κ : id.Kernel ℝ) (hκ : ∀ m x a, 0 ≤ κ m x a) (L : id.Assignment → ℝ)
    (hL : ∀ x, 0 ≤ L x) (σ : Strategy id ℝ) (hσ : σ.Nonneg) (d : id.D) (x : id.Assignment) :
    0 ≤ reach κ L σ d x := by
  unfold reach marg
  exact Finset.sum_nonneg fun y _ => mul_nonneg (freeJoint_nonneg κ hκ _ σ hσ y) (hL y)

theorem freeJoint_congr (κ : id.Kernel ℝ) (E : Finset id.V) {σ τ : Strategy id ℝ}
    (h : ∀ e, id.action e ∈ E → σ e = τ e) : freeJoint κ E σ = freeJoint κ E τ := by
  funext x
  unfold freeJoint
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases he : id.action e ∈ E
  · simp only [he, if_true, h e he]
  · simp only [he, if_false]

/-- A final strategy agrees with the strategy at `d`'s step on every decision already
eliminated, so `reach` and `continuation` may be computed with either; at that step they are
the probability and the weighted valuation of the state. -/
theorem reach_continuation_at_step {κ : id.Kernel ℝ} {u : Utility id ℝ}
    {L : id.Assignment → ℝ} {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ}
    (h : Inv κ u L s σ) (d : id.D) (hd : id.action d ∈ R)
    (hi : R.erase (id.action d) = id.info d) (τ : Strategy id ℝ)
    (hτ : ∀ e, id.action e ∉ R → τ e = σ e) (x : id.Assignment) :
    reach κ L τ d x = (collect s.valuations).prob x ∧
      continuation κ u L τ d x =
        fun b => (collect s.valuations).weight (Function.update x (id.action d) b) := by
  have hR : insert (id.action d) (id.info d) = R := by rw [← hi, Finset.insert_erase hd]
  have hJ : freeJoint κ Rᶜ τ = freeJoint κ Rᶜ σ :=
    freeJoint_congr κ Rᶜ fun e he => hτ e (Finset.mem_compl.1 he)
  constructor
  · unfold reach
    rw [hR, hJ, h.mass]
  · funext b
    unfold continuation
    rw [hR, hJ, h.realizes]

/-- **Semantic first-label rule.** On every row of positive reach probability, the ordered
driver chooses the least action maximizing the continuation value computed with its own final
strategy. This is a representation-independent characterization of those table entries. -/
theorem runWith_ordered_semantic [∀ d : id.D, LinearOrder (id.states (id.action d))]
    {κ : id.Kernel ℝ} {u : Utility id ℝ} {L : id.Assignment → ℝ}
    (hind : Independent κ L) (hclosed : id.Closed) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) (h : Inv κ u L s σ) (d : id.D)
    (hd : id.action d ∈ R) (x : id.Assignment)
    (hx : reach κ L (runWith (Selector.ordered id) plan s σ).2 d x ≠ 0)
    (a : id.states (id.action d)) :
    ((runWith (Selector.ordered id) plan s σ).2 d).kernel x a =
      if a = firstArgmax (continuation κ u L (runWith (Selector.ordered id) plan s σ).2 d x)
      then 1 else 0 := by
  have hinj := (id.closed_iff.1 hclosed).2.1
  induction plan generalizing σ with
  | done => simp at hd
  | chance v hv hc next ih =>
    exact ih (s.chance v) σ (h.chance v hv hc) (Finset.mem_erase.2 ⟨hc d, hd⟩) hx
  | @decision R' d' hd' hi next ih =>
    by_cases hdd : d' = d
    · subst hdd
      have hτ : ∀ e, id.action e ∉ R' →
          (runWith (Selector.ordered id) (.decision d' hd' hi next) s σ).2 e = σ e := by
        intro e he
        refine (runWith_snd_of_notMem _ next (s.decision d')
          (Function.update σ d' (s.policyWith (Selector.ordered id) d' hi)) e
          (fun h' => he (Finset.mem_of_mem_erase h'))).trans ?_
        exact Function.update_of_ne (fun h' : e = d' => he (by rw [h']; exact hd')) _ _
      obtain ⟨hreach, hcont⟩ := reach_continuation_at_step h d' hd' hi _ hτ x
      have hpos : 0 < (collect s.valuations).prob x :=
        lt_of_le_of_ne ((collect s.valuations).nonneg x) (fun h0 => hx (hreach.trans h0.symm))
      rw [hcont, runWith_policy_at_step,
        ← firstArgmax_score_eq_weight s.valuations (id.action d') x
          (h.prob_update hind d' hd' hi x) hpos]
      rfl
    · have hne : id.action d ≠ id.action d' := fun he => hdd (hinj he).symm
      exact ih (s.decision d') _ (h.decisionWith hind hclosed (Selector.ordered id) d' hd' hi)
        (Finset.mem_erase.2 ⟨hne, hd⟩) hx

/-- **First-label policies are determined on reachable rows (no evidence).** -/
theorem solveOrdered_semantic [∀ d : id.D, LinearOrder (id.states (id.action d))]
    (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder) (nf : NoForgettingOrder id)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (d : id.D) (x : id.Assignment)
    (hx : reach κ (fun _ => 1)
      (solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d x ≠ 0)
    (a : id.states (id.action d)) :
    ((solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d).kernel x a =
      if a = firstArgmax (continuation κ u (fun _ => 1)
        (solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d x)
      then 1 else 0 :=
  runWith_ordered_semantic (independent_one κ hclosed ord hloc hnorm) hclosed _ _ _
    (Inv.ofCorrect (initial_correct κ hloc hnonneg u hu _)) d (Finset.mem_univ _) x hx a

/-- **First-label policies are determined on reachable rows (with evidence).** Rows
inconsistent with hard evidence, and all other zero-reach rows, are excluded. -/
theorem solveEvidenceOrdered_semantic [∀ d : id.D, LinearOrder (id.states (id.action d))]
    (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder) (nf : NoForgettingOrder id)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (e : Evidence id) (d : id.D)
    (x : id.Assignment)
    (hx : reach κ e.likelihood
      (solveEvidenceWith (Selector.ordered id) κ hloc hnonneg u hu ord nf e).strategy d x ≠ 0)
    (a : id.states (id.action d)) :
    ((solveEvidenceWith (Selector.ordered id) κ hloc hnonneg u hu ord nf e).strategy d).kernel
        x a =
      if a = firstArgmax (continuation κ u e.likelihood
        (solveEvidenceWith (Selector.ordered id) κ hloc hnonneg u hu ord nf e).strategy d x)
      then 1 else 0 :=
  runWith_ordered_semantic (independent_evidence e κ hclosed ord hloc hnorm) hclosed _ _ _
    (Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu e _)) d (Finset.mem_univ _) x
    hx a

end
end InfluenceDiagramsProofs.DVE
