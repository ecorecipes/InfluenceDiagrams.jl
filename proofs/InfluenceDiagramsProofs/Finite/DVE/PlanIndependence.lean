import InfluenceDiagramsProofs.Finite.DVE.Conditioning

/-!
# First-label tables do not depend on the elimination plan

The headline first-label theorems of `Selector.lean` and `Conditioning.lean` run the bucket
driver on the plan `NoForgettingOrder.plan` builds, whose chance blocks are enumerated in an
arbitrary but fixed order. Julia orders each chance block by min-fill on the current factors.
This module removes that dependence: **any two plans** — any interleaving of chance
eliminations and decisions that `Plan` accepts, in particular two min-fill choices inside the
same strong blocks — give the first-label (`Selector.ordered`) solver the same policy entry on
every information row of positive reach.

The proof is not a backward induction over tables. A `Plan` can maximize `d` only when the
remaining variables are exactly `insert (id.action d) (id.info d)`, so every plan reaches `d`
with the same eliminated set. There the invariant `Inv` says that the weighted valuation is
realized by some nonnegative strategy and dominates every nonnegative strategy; it is
therefore the plan-independent **optimal continuation value** `optimalContinuation`, a
supremum over strategies that mentions no bucket or plan. The probability potential at that
step is the reach probability, which is the same under every strategy (`MassAll`,
`reach_strategy_independent`). On a row of positive reach the first-label entry is the least
maximizer of the optimal continuation value (`runWith_ordered_optimal`), for every plan.

Consequences: `solvePlanOrdered_table_eq` (no evidence), `solveEvidencePlanOrdered_table_eq`
(action-independent likelihood evidence) and `solveConditionedPlan_table_eq` (Julia's sliced
hard-evidence path, where observed variables are skipped wherever the plan lists them).
`solveOrdered_table_plan_independent` restates the first for two perfect-recall orders.

Rows of zero reach are excluded. There no semantic score exists and the entry is fixed by the
bucket representatives, which do depend on the elimination order; this module claims nothing
about them.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

variable {id : FinInfluenceDiagram}

/-! ## The mass invariant under every strategy -/

/-- The probability potential is the weighted marginal of the eliminated variables under
**every** strategy, not only the one being built. -/
def MassAll (κ : id.Kernel ℝ) (L : id.Assignment → ℝ) {R : Finset id.V} (s : State id R) :
    Prop :=
  ∀ (σ : Strategy id ℝ) (x : id.Assignment),
    (collect s.valuations).prob x = marg Rᶜ (fun y => freeJoint κ Rᶜ σ y * L y) x

theorem MassAll.chance {κ : id.Kernel ℝ} {L : id.Assignment → ℝ} {R : Finset id.V}
    {s : State id R} (h : MassAll κ L s) (v : id.V) (hv : v ∈ R) (hc : ∀ d, id.action d ≠ v) :
    MassAll κ L (s.chance v) := by
  have hn : v ∉ Rᶜ := by simpa using hv
  intro σ x
  change (collect (chanceStep v s.valuations)).prob x = _
  rw [chanceStep_prob, compl_erase, freeJoint_insert_chance κ Rᶜ σ v hc, marg_insert hn]
  exact Finset.sum_congr rfl fun b _ => h σ _

theorem MassAll.prob_update {κ : id.Kernel ℝ} {L : id.Assignment → ℝ} {R : Finset id.V}
    {s : State id R} (h : MassAll κ L s) (hind : Independent κ L) (d : id.D)
    (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d) (x : id.Assignment)
    (a : id.states (id.action d)) :
    (collect s.valuations).prob (Function.update x (id.action d) a) =
      (collect s.valuations).prob x := by
  rw [h defaultStrategy, h defaultStrategy]
  exact hind Rᶜ defaultStrategy d (by simpa using hd)
    (by simpa using information_boundary d hi) x a

/-- A decision step keeps the mass identity for every strategy: every normalised policy for
`d` sums an action-constant marginal to itself. -/
theorem MassAll.decision {κ : id.Kernel ℝ} {L : id.Assignment → ℝ} {R : Finset id.V}
    {s : State id R} (h : MassAll κ L s) (hind : Independent κ L) (hclosed : id.Closed)
    (d : id.D) (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d) :
    MassAll κ L (s.decision d) := by
  have hn : id.action d ∉ Rᶜ := by simpa using hd
  have hinj := (id.closed_iff.1 hclosed).2.1
  have hp := h.prob_update hind d hd hi
  intro σ x
  change (collect (decisionStep (id.action d) s.valuations)).prob x = _
  rw [(decisionStep_eval _ _ hp x).1, hp, compl_erase]
  have hc := decision_marginal κ Rᶜ σ hinj d hn (info_disjoint d hi) (σ d) L x
  simp only [Function.update_eq_self] at hc
  rw [hc]
  simp_rw [← h σ, hp]
  rw [← Finset.sum_mul, (σ d).normalised x, one_mul]

theorem MassAll.ofInv {κ : id.Kernel ℝ} {u : Utility id ℝ} {L : id.Assignment → ℝ}
    {s : State id Finset.univ} (h : ∀ σ : Strategy id ℝ, Inv κ u L s σ) : MassAll κ L s :=
  fun σ x => (h σ).mass x

theorem massAll_initial (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) :
    MassAll κ (fun _ => 1) (initial κ hloc hnonneg u hu) :=
  MassAll.ofInv (u := u) fun σ => Inv.ofCorrect (initial_correct κ hloc hnonneg u hu σ)

theorem massAll_initialEvidence (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) :
    MassAll κ e.likelihood (initialEvidence κ hloc hnonneg u hu e) :=
  MassAll.ofInv (u := u) fun σ => Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu e σ)

/-- **Reach does not depend on the strategy.** Whenever some plan eliminates `d` from a state
whose mass identity holds for every strategy, the weighted probability of each information
row of `d` is the same under every strategy. -/
theorem reach_strategy_independent {κ : id.Kernel ℝ} {L : id.Assignment → ℝ}
    (hind : Independent κ L) (hclosed : id.Closed) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (hs : MassAll κ L s) (d : id.D) (hd : id.action d ∈ R)
    (σ τ : Strategy id ℝ) (x : id.Assignment) : reach κ L σ d x = reach κ L τ d x := by
  have hinj := (id.closed_iff.1 hclosed).2.1
  induction plan with
  | done => simp at hd
  | chance v hv hc next ih =>
    exact ih (s.chance v) (hs.chance v hv hc) (Finset.mem_erase.2 ⟨hc d, hd⟩)
  | @decision R' d' hd' hi next ih =>
    by_cases hdd : d' = d
    · subst hdd
      have hR : insert (id.action d') (id.info d') = R' := by
        rw [← hi, Finset.insert_erase hd']
      unfold reach
      rw [hR, ← hs σ, ← hs τ]
    · have hne : id.action d ≠ id.action d' := fun he => hdd (hinj he).symm
      exact ih (s.decision d') (hs.decision hind hclosed d' hd' hi)
        (Finset.mem_erase.2 ⟨hne, hd⟩)

/-! ## The optimal continuation value -/

/-- The largest unnormalized expected utility of choosing `b` at `d` on the information row of
`x` and then following any nonnegative strategy. It mentions no plan, bucket or selector. -/
def optimalContinuation (κ : id.Kernel ℝ) (u : Utility id ℝ) (L : id.Assignment → ℝ)
    (d : id.D) (x : id.Assignment) (b : id.states (id.action d)) : ℝ :=
  sSup ((fun τ : Strategy id ℝ => continuation κ u L τ d x b) '' {τ | τ.Nonneg})

/-- At the step that maximizes `d`, the weighted valuation is the optimal continuation value,
whatever plan led there: it is attained by the final strategy and dominates every other. -/
theorem weight_eq_optimalContinuation {κ : id.Kernel ℝ} {u : Utility id ℝ}
    {L : id.Assignment → ℝ} {R : Finset id.V} {s : State id R} {σ : Strategy id ℝ}
    (h : Inv κ u L s σ) (d : id.D) (hd : id.action d ∈ R)
    (hi : R.erase (id.action d) = id.info d) (τ : Strategy id ℝ) (hτn : τ.Nonneg)
    (hτ : ∀ e, id.action e ∉ R → τ e = σ e) (x : id.Assignment) :
    (fun b => (collect s.valuations).weight (Function.update x (id.action d) b)) =
      optimalContinuation κ u L d x := by
  have hR : insert (id.action d) (id.info d) = R := by rw [← hi, Finset.insert_erase hd]
  funext b
  symm
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨τ, hτn, ?_⟩
    show continuation κ u L τ d x b = _
    rw [(reach_continuation_at_step h d hd hi τ hτ x).2]
  · rintro c ⟨ρ, hρ, rfl⟩
    unfold continuation
    rw [hR]
    exact h.dominates ρ hρ _

/-- **First-label entries are least maximizers of the optimal continuation value.** For every
plan, on every row of positive reach (under any strategy), the ordered driver's entry is the
least action maximizing `optimalContinuation`. -/
theorem runWith_ordered_optimal [∀ d : id.D, LinearOrder (id.states (id.action d))]
    {κ : id.Kernel ℝ} {u : Utility id ℝ} {L : id.Assignment → ℝ}
    (hind : Independent κ L) (hclosed : id.Closed) {R : Finset id.V} (plan : Plan id R)
    (s : State id R) (σ : Strategy id ℝ) (hσ : σ.Deterministic) (h : Inv κ u L s σ)
    (hs : MassAll κ L s) (d : id.D) (hd : id.action d ∈ R) (x : id.Assignment)
    (ρ : Strategy id ℝ) (hx : reach κ L ρ d x ≠ 0) (a : id.states (id.action d)) :
    ((runWith (Selector.ordered id) plan s σ).2 d).kernel x a =
      if a = firstArgmax (optimalContinuation κ u L d x) then 1 else 0 := by
  have hinj := (id.closed_iff.1 hclosed).2.1
  induction plan generalizing σ with
  | done => simp at hd
  | chance v hv hc next ih =>
    exact ih (s.chance v) σ hσ (h.chance v hv hc) (hs.chance v hv hc)
      (Finset.mem_erase.2 ⟨hc d, hd⟩)
  | @decision R' d' hd' hi next ih =>
    by_cases hdd : d' = d
    · subst hdd
      have hR : insert (id.action d') (id.info d') = R' := by
        rw [← hi, Finset.insert_erase hd']
      let τ := (runWith (Selector.ordered id) (.decision d' hd' hi next) s σ).2
      have hτ : ∀ e, id.action e ∉ R' → τ e = σ e := by
        intro e he
        refine (runWith_snd_of_notMem _ next (s.decision d')
          (Function.update σ d' (s.policyWith (Selector.ordered id) d' hi)) e
          (fun h' => he (Finset.mem_of_mem_erase h'))).trans ?_
        exact Function.update_of_ne (fun h' : e = d' => he (by rw [h']; exact hd')) _ _
      have hτn : τ.Nonneg :=
        deterministic_nonneg _ (runWith_deterministic _ _ _ _ hσ)
      have hprob : (collect s.valuations).prob x = reach κ L ρ d' x := by
        unfold reach
        rw [hR, hs ρ]
      have hpos : 0 < (collect s.valuations).prob x :=
        lt_of_le_of_ne ((collect s.valuations).nonneg x) (fun h0 => hx (hprob.symm.trans h0.symm))
      rw [← weight_eq_optimalContinuation h d' hd' hi τ hτn hτ x, runWith_policy_at_step,
        ← firstArgmax_score_eq_weight s.valuations (id.action d') x
          (h.prob_update hind d' hd' hi x) hpos]
      rfl
    · have hne : id.action d ≠ id.action d' := fun he => hdd (hinj he).symm
      refine ih (s.decision d') _ ?_ (h.decisionWith hind hclosed (Selector.ordered id) d' hd' hi)
        (hs.decision hind hclosed d' hd' hi) (Finset.mem_erase.2 ⟨hne, hd⟩)
      intro e
      by_cases he : e = d'
      · subst e
        simp only [Function.update_self]
        exact ⟨_, fun y z hyz => congrArg ((Selector.ordered id).pick d')
          (bucketScore_local s d' hi y z hyz), rfl⟩
      · rw [Function.update_of_ne he]
        exact hσ e

/-! ## Solvers on an arbitrary plan -/

/-- `solveWith` on an arbitrary plan: any enumeration of the chance blocks, for example the
one min-fill chooses. -/
def solvePlanWith (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) : Solution id :=
  let result := runWith sel plan (initial κ hloc hnonneg u hu) defaultStrategy
  ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩

theorem solveWith_eq_solvePlanWith (sel : Selector id) (κ : id.Kernel ℝ)
    (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (ord : id.IDOrder) (nf : NoForgettingOrder id) :
    solveWith sel κ hloc hnonneg u hu ord nf =
      solvePlanWith sel κ hloc hnonneg u hu (nf.plan ord.no_self_info) := rfl

def solveEvidencePlanWith (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) (e : Evidence id) : Solution id :=
  let result := runWith sel plan (initialEvidence κ hloc hnonneg u hu e) defaultStrategy
  ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩

theorem solveEvidenceWith_eq_solveEvidencePlanWith (sel : Selector id) (κ : id.Kernel ℝ)
    (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (ord : id.IDOrder) (nf : NoForgettingOrder id)
    (e : Evidence id) :
    solveEvidenceWith sel κ hloc hnonneg u hu ord nf e =
      solveEvidencePlanWith sel κ hloc hnonneg u hu (nf.plan ord.no_self_info) e := rfl

/-- Julia's evidence path (slice every factor, skip absent chance variables) on any plan. -/
def solveConditionedPlan (sel : Selector id) (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (plan : Plan id Finset.univ) (O : Finset id.V) (o : id.Assignment) : Solution id :=
  let result := runSkipWith sel plan (initialConditioned κ hloc hnonneg u hu O o) defaultStrategy
  ⟨(collect result.1.valuations).util (baseAssignment id), result.2⟩

theorem solveConditioned_eq_solveConditionedPlan (sel : Selector id) (κ : id.Kernel ℝ)
    (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (ord : id.IDOrder) (nf : NoForgettingOrder id)
    (O : Finset id.V) (o : id.Assignment) :
    solveConditioned sel κ hloc hnonneg u hu ord nf O o =
      solveConditionedPlan sel κ hloc hnonneg u hu (nf.plan ord.no_self_info) O o := rfl

section Ordered

variable [∀ d : id.D, LinearOrder (id.states (id.action d))]

/-- The ordered solver on any plan chooses, on every row of positive reach, the least
maximizer of the optimal continuation value (no evidence). -/
theorem solvePlanOrdered_optimal (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (plan : Plan id Finset.univ) (d : id.D)
    (x : id.Assignment) (ρ : Strategy id ℝ) (hx : reach κ (fun _ => 1) ρ d x ≠ 0)
    (a : id.states (id.action d)) :
    ((solvePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan).strategy d).kernel x a =
      if a = firstArgmax (optimalContinuation κ u (fun _ => 1) d x) then 1 else 0 :=
  runWith_ordered_optimal (independent_one κ hclosed ord hloc hnorm) hclosed plan _ _
    defaultStrategy_deterministic (Inv.ofCorrect (initial_correct κ hloc hnonneg u hu _))
    (massAll_initial κ hloc hnonneg u hu) d (Finset.mem_univ _) x ρ hx a

/-- **Plan independence of first-label tables (no evidence).** Any two elimination plans —
in particular two enumerations of the chance variables inside the strong blocks, such as
different min-fill choices — give the same first-label policy entry on every information row
whose reach probability is positive. Reach is the same under every strategy
(`reach_strategy_independent`), so `ρ` is arbitrary. -/
theorem solvePlanOrdered_table_eq (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (plan₁ plan₂ : Plan id Finset.univ)
    (d : id.D) (x : id.Assignment) (ρ : Strategy id ℝ) (hx : reach κ (fun _ => 1) ρ d x ≠ 0) :
    ((solvePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan₁).strategy d).kernel x =
      ((solvePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan₂).strategy d).kernel x := by
  funext a
  rw [solvePlanOrdered_optimal κ hclosed ord hloc hnorm hnonneg u hu plan₁ d x ρ hx,
    solvePlanOrdered_optimal κ hclosed ord hloc hnorm hnonneg u hu plan₂ d x ρ hx]

/-- The headline `solveWith` tables for two perfect-recall orders agree on positive reach. -/
theorem solveOrdered_table_plan_independent (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord₁ ord₂ : id.IDOrder) (nf₁ nf₂ : NoForgettingOrder id) (hloc : ∀ m, Local κ m)
    (hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ)
    (hu : ∀ j, Utility.Local u j) (d : id.D) (x : id.Assignment) (ρ : Strategy id ℝ)
    (hx : reach κ (fun _ => 1) ρ d x ≠ 0) :
    ((solveWith (Selector.ordered id) κ hloc hnonneg u hu ord₁ nf₁).strategy d).kernel x =
      ((solveWith (Selector.ordered id) κ hloc hnonneg u hu ord₂ nf₂).strategy d).kernel x :=
  solvePlanOrdered_table_eq κ hclosed ord₁ hloc hnorm hnonneg u hu _ _ d x ρ hx

/-- The ordered likelihood-evidence solver on any plan chooses, on every row of positive
weighted reach, the least maximizer of the optimal weighted continuation value. -/
theorem solveEvidencePlanOrdered_optimal (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) (plan : Plan id Finset.univ) (d : id.D) (x : id.Assignment)
    (ρ : Strategy id ℝ) (hx : reach κ e.likelihood ρ d x ≠ 0) (a : id.states (id.action d)) :
    ((solveEvidencePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan e).strategy d).kernel
        x a =
      if a = firstArgmax (optimalContinuation κ u e.likelihood d x) then 1 else 0 :=
  runWith_ordered_optimal (independent_evidence e κ hclosed ord hloc hnorm) hclosed plan _ _
    defaultStrategy_deterministic
    (Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu e _))
    (massAll_initialEvidence κ hloc hnonneg u hu e) d (Finset.mem_univ _) x ρ hx a

/-- **Plan independence of first-label tables (likelihood evidence).** -/
theorem solveEvidencePlanOrdered_table_eq (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) (plan₁ plan₂ : Plan id Finset.univ) (d : id.D) (x : id.Assignment)
    (ρ : Strategy id ℝ) (hx : reach κ e.likelihood ρ d x ≠ 0) :
    ((solveEvidencePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan₁ e).strategy
        d).kernel x =
      ((solveEvidencePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan₂ e).strategy
        d).kernel x := by
  funext a
  rw [solveEvidencePlanOrdered_optimal κ hclosed ord hloc hnorm hnonneg u hu e plan₁ d x ρ hx,
    solveEvidencePlanOrdered_optimal κ hclosed ord hloc hnorm hnonneg u hu e plan₂ d x ρ hx]

/-- On any plan, Julia's sliced evidence path has the likelihood driver's first-label entry
at `clamp O o x` whenever that clamped row has positive reach. -/
theorem solveConditionedPlan_policy_eq (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (H : HardEvidence id) (plan : Plan id Finset.univ) (d : id.D) (x : id.Assignment)
    (ρ : Strategy id ℝ)
    (hx : reach κ H.toEvidence.likelihood ρ d (clamp H.observed H.value x) ≠ 0) :
    ((solveConditionedPlan (Selector.ordered id) κ hloc hnonneg u hu plan H.observed
        H.value).strategy d).kernel x =
      ((solveEvidencePlanWith (Selector.ordered id) κ hloc hnonneg u hu plan
        H.toEvidence).strategy d).kernel (clamp H.observed H.value x) := by
  have hind := independent_evidence H.toEvidence κ hclosed ord hloc hnorm
  refine (conditioned_policy H hind hclosed plan
    (initialConditioned κ hloc hnonneg u hu H.observed H.value)
    (initialEvidence κ hloc hnonneg u hu H.toEvidence) defaultStrategy defaultStrategy
    (initial_coupled κ hclosed hloc hnonneg u hu H)
    (Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu H.toEvidence _))
    (Inv.ofWeighted (initialEvidence_correct κ hloc hnonneg u hu H.toEvidence _))
    d (Finset.mem_univ _) x).1 ?_
  rwa [reach_strategy_independent hind hclosed plan _
    (massAll_initialEvidence κ hloc hnonneg u hu H.toEvidence) d (Finset.mem_univ _) _ ρ]

/-- **Plan independence of Julia's conditioned first-label tables.** With hard evidence on an
action-free chance-ancestral set, the sliced, variable-skipping driver gives the same entry at
`x` for any two plans whenever the clamped information row has positive reach. -/
theorem solveConditionedPlan_table_eq (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (H : HardEvidence id) (plan₁ plan₂ : Plan id Finset.univ) (d : id.D) (x : id.Assignment)
    (ρ : Strategy id ℝ)
    (hx : reach κ H.toEvidence.likelihood ρ d (clamp H.observed H.value x) ≠ 0) :
    ((solveConditionedPlan (Selector.ordered id) κ hloc hnonneg u hu plan₁ H.observed
        H.value).strategy d).kernel x =
      ((solveConditionedPlan (Selector.ordered id) κ hloc hnonneg u hu plan₂ H.observed
        H.value).strategy d).kernel x := by
  rw [solveConditionedPlan_policy_eq κ hclosed ord hloc hnorm hnonneg u hu H plan₁ d x ρ hx,
    solveConditionedPlan_policy_eq κ hclosed ord hloc hnorm hnonneg u hu H plan₂ d x ρ hx,
    solveEvidencePlanOrdered_table_eq κ hclosed ord hloc hnorm hnonneg u hu H.toEvidence
      plan₁ plan₂ d _ ρ hx]

end Ordered

end
end InfluenceDiagramsProofs.DVE
