import InfluenceDiagramsProofs.Finite.DVE.SolutionRun

/-!
# Checking Julia's recorded solution against the exact run

A version-2 certificate records the policy tables, scores and value of one Julia DVE run
(`Finite/DVE/SolutionJson.lean`). This module compares them with the exact run of
`Finite/DVE/SolutionRun.lean` on the certificate's data, the run `certificate_tables` speaks about,
on Julia's own elimination order (`solutionPlan`), with Julia's representative choice
(`keepOfT`) and the first-label selector `r.selector`.

**The comparison** reads entry `e` of the policy of decision `d` at the assignment of its
coordinates (`entryAssignment`); `rowScore` is the exact run's score row there (`scoreT` through
`bucketAt`), and `entryIndex` the recorded action's position among the action's states.

* `EntryAction f i`: `i` maximizes `f` and is the least maximizer (the first-label rule);
  `EntryScore f i q`: the score at `i` is `q`; `EntryWithin f i τ`: `f b ≤ f i + τ` for every `b`.
* **Exact runs** (`arithmetic = "exact_rational"`): `solutionMatches` (decidable, `Bool`) holds when
  there is no evidence row, the run read the certificate's own numbers (`DataConsistent`: data `q`
  for `rational_exact`, `f64` for `binary64_exact`), Julia's order is a plan, every recorded action
  is the least-position maximizer of the exact score row, every recorded score is that row's
  maximum exactly, and the recorded value is the exact value.
* **Binary64 runs**: `solutionWithin τ τv` holds when every recorded action is within `τ` of its
  exact row maximum and the recorded value within `τv` of the exact value; `actionsAgree` when every
  recorded action is exactly the exact run's.

**Theorems.**

* `recorded_eq_run`: if the recorded actions agree with the exact run (`actionsAgree`), Julia's
  recorded strategy `recordedStrategy` (deterministic, reading each recorded table at the
  information coordinates) **is** the exact run's strategy, for the representative `keepOfT` and
  the plan of Julia's order.
* `recorded_solution_optimal` (the headline for exact runs): if `solutionMatches` holds, the
  recorded tables are the run's, on every information row the recorded action is the
  least-position maximizer of the run's own score, and the recorded value is the run's value;
  if moreover every CPT row sums to exactly one, the recorded strategy is optimal and the recorded
  value is the optimum (`optimalValue`).
* `recorded_solution_approx_optimal`: under `solutionMatches` and `certificateEpsilon c < 1`, the
  recorded strategy and value carry the bounds of `certificate_approx_optimal`: within `2 e` and
  `e` of the optimum of the row-normalised model, `e = approxError ε n Umax`.
* `recorded_binary64_approx_optimal` (binary64 runs): under `solutionWithin τ τv`, every recorded
  action is within `τ` of the maximum of the run's score row on every information row, and the
  recorded value is within `τv + e` of the optimum of the row-normalised model; if moreover
  `actionsAgree`, the recorded strategy is the run's and is within `2 e` of that optimum.

**Not proved.** That a binary64 run whose actions differ from the exact ones at near-ties (each
within `τ` of its row maximum) loses at most a function of `τ` in expected utility: the loss
bound needs a step-by-step invariant through the driver that is not formalized, so for such a
run only the per-row `τ` statement and the value bound are theorems. Evidence is not modelled:
the checks require that the certificate has no evidence row. Trusted: `Lean.Json.parse`,
Julia's exporter and its Float64 run, which is compared, not proved.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVECertificate

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram
open BayesianNetworksProofs.Raw InfluenceDiagramsProofs.Records Spec

variable (r : Diagram) (h : r.Valid)

/-! ## The bucket of a decision -/

/-- The bucket of `d`'s action when the plan eliminates it. -/
def bucketAt : {R : Finset (Fin r.nv)} → DVE.Plan (r.compile h) R → List (TVal r) → Fin r.nd →
    Option (List (TVal r))
  | _, .done, _, _ => none
  | _, .chance v _ _ next, ts, d => bucketAt next (chanceStepT r h v ts) d
  | _, .decision d' _ _ next, ts, d =>
    if d' = d then some (bucketT r (r.decisions d).action ts)
    else bucketAt next (decisionStepT r h (r.decisions d').action ts) d

theorem scoreT_of_bucketAt {R : Finset (r.compile h).V} (plan : DVE.Plan (r.compile h) R)
    (ts : List (TVal r)) (d : Fin r.nd) (B : List (TVal r)) (hB : bucketAt r h plan ts d = some B)
    (x : (r.compile h).Assignment) (b : Fin (r.stateCount (r.decisions d).action)) :
    scoreT r h plan ts d x b =
      (qcollect (B.map (view r h))).util (Function.update x (r.decisions d).action b) := by
  induction plan generalizing ts with
  | done => simp [bucketAt] at hB
  | @chance R v hv hc next ih => exact ih _ hB
  | @decision R d' hd hi next ih =>
    simp only [bucketAt] at hB
    simp only [scoreT]
    by_cases hdd : d' = d
    · subst hdd
      rw [if_pos rfl] at hB ⊢
      cases hB
      rfl
    · rw [if_neg hdd] at hB ⊢
      exact ih _ hB

/-! ## Entries -/

/-- The assignment of an entry: the coordinates `coords` along `axes`, state `0` elsewhere. -/
def entryAssignment (axes coords : List Nat) : (r.compile h).Assignment := fun v =>
  if hk : coords.getD (axes.idxOf v.val) 0 < r.stateCount v then ⟨_, hk⟩ else ⟨0, h.nonempty_states v⟩

/-- The recorded action's position among the action variable's states (its zero-based
`state_position`). -/
def entryIndex (c : Certificate) (p : PolicyRecord) (e : PolicyEntry) : Nat :=
  (stateIds c p.action).idxOf e.action

/-- The exact run's score row at entry `e` of the policy of `d`, from the bucket `B`. -/
def rowScore (B : List (TVal r)) (d : Fin r.nd) (p : PolicyRecord) (e : PolicyEntry)
    (b : Fin (r.stateCount (r.decisions d).action)) : ℚ :=
  (qcollect (B.map (view r h))).util
    (Function.update (entryAssignment r h p.axes e.coords) (r.decisions d).action b)

/-- `i` is the least maximizer of `f`. -/
def EntryAction {n : Nat} (f : Fin n → ℚ) (i : Nat) : Prop :=
  ∃ hi : i < n, (∀ b, f b ≤ f ⟨i, hi⟩) ∧ ∀ b : Fin n, (∀ c, f c ≤ f b) → i ≤ b.val

/-- The score at `i` is `q`. -/
def EntryScore {n : Nat} (f : Fin n → ℚ) (i : Nat) (q : ℚ) : Prop :=
  ∃ hi : i < n, f ⟨i, hi⟩ = q

/-- `i` is within `τ` of the maximum of `f`. -/
def EntryWithin {n : Nat} (f : Fin n → ℚ) (i : Nat) (τ : ℚ) : Prop :=
  ∃ hi : i < n, ∀ b, f b ≤ f ⟨i, hi⟩ + τ

instance {n : Nat} (f : Fin n → ℚ) (i : Nat) : Decidable (EntryAction f i) := by
  unfold EntryAction; infer_instance

instance {n : Nat} (f : Fin n → ℚ) (i : Nat) (q : ℚ) : Decidable (EntryScore f i q) := by
  unfold EntryScore; infer_instance

instance {n : Nat} (f : Fin n → ℚ) (i : Nat) (τ : ℚ) : Decidable (EntryWithin f i τ) := by
  unfold EntryWithin; infer_instance

variable (c : Certificate) (s : Solution)

/-- Every entry of every decision's policy satisfies `P` against the exact score row. -/
def AllEntries {R : Finset (Fin r.nv)} (plan : DVE.Plan (r.compile h) R)
    (P : (d : Fin r.nd) → PolicyRecord → PolicyEntry →
      (Fin (r.stateCount (r.decisions d).action) → ℚ) → Prop) : Prop :=
  ∀ d : Fin r.nd, OptHolds (fun p => OptHolds (fun B => ∀ e ∈ p.entries, P d p e (rowScore r h B d p e))
    (bucketAt r h plan (initT r h c) d)) s.policies[d.val]?

instance {R : Finset (Fin r.nv)} (plan : DVE.Plan (r.compile h) R)
    (P : (d : Fin r.nd) → PolicyRecord → PolicyEntry →
      (Fin (r.stateCount (r.decisions d).action) → ℚ) → Prop)
    [∀ d p e f, Decidable (P d p e f)] : Decidable (AllEntries r h c s plan P) := by
  unfold AllEntries; infer_instance

/-- The plan of Julia's recorded elimination order. -/
def solutionPlan : Option (DVE.Plan (r.compile h) Finset.univ) :=
  (toFinList r s.eliminationOrder).bind fun o => planOf r h o Finset.univ

/-- The run read the certificate's own numbers: the rationals of a `rational_exact` certificate,
the binary64 words of a `binary64_exact` one. -/
def DataConsistent : Prop :=
  (s.data = .q ∧ c.numeric.mode = "rational_exact") ∨
    (s.data = .f64 ∧ c.numeric.mode = "binary64_exact")

instance : Decidable (DataConsistent c s) := by unfold DataConsistent; infer_instance

/-- **Every recorded action is the exact run's** (least-position maximizer of its score row). -/
def ActionsAgreeWith (plan : DVE.Plan (r.compile h) Finset.univ) : Prop :=
  c.hard = [] ∧ AllEntries r h c s plan fun _ p e f => EntryAction f (entryIndex c p e)

/-- **The exact comparison**, on a plan. -/
def SolutionMatchesWith (plan : DVE.Plan (r.compile h) Finset.univ) : Prop :=
  ActionsAgreeWith r h c s plan ∧ s.arithmetic = .exactRational ∧ DataConsistent c s ∧
    AllEntries r h c s plan (fun _ p e f => EntryScore f (entryIndex c p e) e.score.toRat) ∧
    s.value.toRat = valueT r h plan (initT r h c)

/-- **The binary64 comparison**, on a plan, with tolerances `τ` (actions) and `τv` (value). -/
def SolutionWithinWith (τ τv : ℚ) (plan : DVE.Plan (r.compile h) Finset.univ) : Prop :=
  c.hard = [] ∧ AllEntries r h c s plan (fun _ p e f => EntryWithin f (entryIndex c p e) τ) ∧
    |s.value.toRat - valueT r h plan (initT r h c)| ≤ τv

instance (plan : DVE.Plan (r.compile h) Finset.univ) : Decidable (ActionsAgreeWith r h c s plan) := by
  unfold ActionsAgreeWith; infer_instance

instance (plan : DVE.Plan (r.compile h) Finset.univ) :
    Decidable (SolutionMatchesWith r h c s plan) := by
  unfold SolutionMatchesWith; infer_instance

instance (τ τv : ℚ) (plan : DVE.Plan (r.compile h) Finset.univ) :
    Decidable (SolutionWithinWith r h c s τ τv plan) := by
  unfold SolutionWithinWith; infer_instance

/-- **The checker for exact runs** (decidable). -/
def solutionMatches : Bool :=
  match solutionPlan r h s with
  | some plan => decide (SolutionMatchesWith r h c s plan)
  | none => false

/-- Every recorded action is the exact run's. -/
def actionsAgree : Bool :=
  match solutionPlan r h s with
  | some plan => decide (ActionsAgreeWith r h c s plan)
  | none => false

/-- **The checker for binary64 runs** (decidable), with tolerances `τ` and `τv`. -/
def solutionWithin (τ τv : ℚ) : Bool :=
  match solutionPlan r h s with
  | some plan => decide (SolutionWithinWith r h c s τ τv plan)
  | none => false

theorem solutionMatches_spec (hsm : solutionMatches r h c s = true) :
    ∃ plan, solutionPlan r h s = some plan ∧ SolutionMatchesWith r h c s plan := by
  unfold solutionMatches at hsm
  split at hsm
  · rename_i plan hp
    exact ⟨plan, hp, of_decide_eq_true hsm⟩
  · cases hsm

theorem actionsAgree_spec (hsm : actionsAgree r h c s = true) :
    ∃ plan, solutionPlan r h s = some plan ∧ ActionsAgreeWith r h c s plan := by
  unfold actionsAgree at hsm
  split at hsm
  · rename_i plan hp
    exact ⟨plan, hp, of_decide_eq_true hsm⟩
  · cases hsm

theorem solutionWithin_spec {τ τv : ℚ} (hsm : solutionWithin r h c s τ τv = true) :
    ∃ plan, solutionPlan r h s = some plan ∧ SolutionWithinWith r h c s τ τv plan := by
  unfold solutionWithin at hsm
  split at hsm
  · rename_i plan hp
    exact ⟨plan, hp, of_decide_eq_true hsm⟩
  · cases hsm

/-! ## Julia's recorded strategy -/

/-- `x` on the information set of `d`, state `0` elsewhere. -/
def infoProject (d : Fin r.nd) (x : (r.compile h).Assignment) : (r.compile h).Assignment :=
  fun v => if v ∈ (r.compile h).info d then x v else ⟨0, h.nonempty_states v⟩

/-- The recorded entry of `d` at the coordinates of `x`, and its action position. -/
def recordedIndex (d : Fin r.nd) (x : (r.compile h).Assignment) : Option Nat :=
  (s.policies[d.val]?).bind fun p =>
    (p.entries.find? fun e => decide (e.coords = coordsOf r h x p.axes)).map (entryIndex c p)

/-- The action Julia recorded for `d` on the information row of `x`. -/
def recordedAction (d : Fin r.nd) (x : (r.compile h).Assignment) :
    Fin (r.stateCount (r.decisions d).action) :=
  match recordedIndex r h c s d (infoProject r h d x) with
  | some i => if hi : i < r.stateCount (r.decisions d).action then ⟨i, hi⟩
    else ⟨0, h.nonempty_states _⟩
  | none => ⟨0, h.nonempty_states _⟩

theorem infoProject_local (d : Fin r.nd) (x x' : (r.compile h).Assignment)
    (hx : ∀ p ∈ (r.compile h).info d, x p = x' p) : infoProject r h d x = infoProject r h d x' := by
  funext v
  unfold infoProject
  split_ifs with hv
  · exact hx v hv
  · rfl

/-- **Julia's recorded strategy**: each decision deterministically reads its recorded table at
the coordinates of its information variables. -/
def recordedStrategy : Strategy (r.compile h) ℝ := fun d =>
  Policy.ofFun (recordedAction r h c s d) fun x x' hx => by
    unfold recordedAction
    rw [infoProject_local r h d x x' hx]

theorem recordedStrategy_deterministic : (recordedStrategy r h c s).Deterministic :=
  fun _ => ⟨_, _, rfl⟩

/-! ## Information sets are the recorded axes -/

theorem certDim_lt {c : Certificate} (hm : Matches r c) (v : Fin r.nv) (x : (r.compile h).Assignment) :
    (x v).val < certDim c v.val := by
  rw [certDim_eq hm, dim, dif_pos v.isLt]
  exact (x v).isLt

/-- Every information variable of `d` is one of the recorded axes. -/
theorem info_mem_axes {r : Diagram} (hf : r.FullValid) {c : Certificate} (hm : Matches r c)
    (d : Fin r.nd) {axes : List Nat} (hax : infoVars c d.val = some axes) (v : Fin r.nv)
    (hv : v ∈ (r.compile hf.valid).info d) : v.val ∈ axes := by
  obtain ⟨f, hf1, rfl⟩ := Finset.mem_image.1 hv
  have hfd : (r.information f).decision = d := (Finset.mem_filter.1 hf1).2
  have hinfo := hm.information hf d
  have hdec := hm.decisions d
  unfold infoVars at hax
  cases hc : c.decisions[d.val]? with
  | none => rw [hc] at hax; cases hax
  | some e =>
    rw [hc] at hax hinfo hdec
    simp only [Option.map_some, Option.some.injEq] at hax
    subst hax
    change DecisionOk r d e at hdec
    have hlen := hdec.2.2.1
    have hpos := hf.information_positions.1 f
    have hcard : Fintype.card {f' : Fin r.nf // (r.information f').decision = (r.information f).decision} =
        (Finset.univ.filter fun f' => (r.information f').decision = d).card := by
      rw [Fintype.card_subtype, hfd]
    have hj : (r.information f).position < e.information.length := by
      rw [hlen, ← hcard]
      exact hpos
    have := hinfo _ hj f hfd rfl
    rw [← this]
    exact List.mem_map.2 ⟨_, List.getElem_mem hj, rfl⟩

theorem entryAssignment_coordsOf (axes : List Nat) (x : (r.compile h).Assignment) (v : Fin r.nv)
    (hv : v.val ∈ axes) : entryAssignment r h axes (coordsOf r h x axes) v = x v := by
  have hi : axes.idxOf v.val < axes.length := List.idxOf_lt_length_of_mem hv
  have hget : axes[axes.idxOf v.val] = v.val := List.getElem_idxOf hi
  have hk : (coordsOf r h x axes).getD (axes.idxOf v.val) 0 = (x v).val := by
    have hlen : axes.idxOf v.val < (coordsOf r h x axes).length := by simpa [coordsOf] using hi
    rw [getD_of_lt hlen]
    simp only [coordsOf, List.getElem_map]
    have hlt : axes[axes.idxOf v.val] < r.nv := by rw [hget]; exact v.isLt
    rw [dif_pos hlt]
    have : (⟨axes[axes.idxOf v.val], hlt⟩ : Fin r.nv) = v := Fin.ext hget
    rw [this]
  unfold entryAssignment
  rw [dif_pos (by rw [hk]; exact (x v).isLt)]
  exact Fin.ext hk

/-! ## The run's tables at the recorded entries -/

section Run

variable {r : Diagram} (hf : r.FullValid) {c : Certificate} (s : Solution)

/-- The exact run on Julia's plan. -/
noncomputable abbrev runOf (hm : Matches r c) (hn : Nonneg c)
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ) :=
  DVE.solveRepPlanWith (r.selector hf.valid) (keepOfT r hf.valid plan (initT r hf.valid c))
    (certKernel r hf.valid c) (certKernel_local hm hf.valid) (certKernel_nonneg hn hf.valid)
    (certUtility r hf.valid c) (certUtility_local hm hf.valid) plan

/-- The exact run's score rows on Julia's plan. -/
noncomputable abbrev scoreOf (hm : Matches r c) (hn : Nonneg c)
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ) :=
  DVE.solveRepPlanScore (keepOfT r hf.valid plan (initT r hf.valid c))
    (certKernel r hf.valid c) (certKernel_local hm hf.valid) (certKernel_nonneg hn hf.valid)
    (certUtility r hf.valid c) (certUtility_local hm hf.valid) plan

/-- **At every information row, the recorded entry and the exact score row.** For every decision
`d` and assignment `x`, the entry of `d`'s recorded table at the coordinates of `x` exists,
`recordedIndex` reads it, and the run's score row at `x` is that entry's `rowScore`. -/
theorem entry_of_row (hm : Matches r c) (hn : Nonneg c) (hs : s.WellFormed c)
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ) (d : Fin r.nd) (p : PolicyRecord)
    (hp : s.policies[d.val]? = some p) (B : List (TVal r))
    (hB : bucketAt r hf.valid plan (initT r hf.valid c) d = some B)
    (x : (r.compile hf.valid).Assignment) :
    ∃ e ∈ p.entries, recordedIndex r hf.valid c s d (infoProject r hf.valid d x) =
        some (entryIndex c p e) ∧
      ∀ b, scoreOf hf hm hn plan d x b = (rowScore r hf.valid B d p e b : ℝ) := by
  have hd : d.val < s.policies.length := by
    rw [hs.length, hm.decisions_length]
    exact d.isLt
  have hpk : s.policies[d.val] = p := by
    rw [List.getElem?_eq_getElem hd, Option.some.injEq] at hp
    exact hp
  have hwf := hs.policies d.val hd
  rw [hpk] at hwf
  set x' := infoProject r hf.valid d x
  have hmem : coordsOf r hf.valid x' p.axes ∈ p.entries.map PolicyEntry.coords := by
    rw [hwf.coverage, mem_lexCoords, coordsOf, List.forall₂_map_left_iff,
      List.forall₂_map_right_iff, List.forall₂_same]
    intro v hv
    have hlt : v < r.nv := by
      have := hwf.axes.1 v hv
      rwa [hm.vars_length] at this
    rw [dif_pos hlt]
    exact certDim_lt r hf.valid hm ⟨v, hlt⟩ x'
  obtain ⟨e0, he0, he0c⟩ := List.mem_map.1 hmem
  have hfind : (p.entries.find? fun e => decide (e.coords = coordsOf r hf.valid x' p.axes)).isSome := by
    rw [List.find?_isSome]
    exact ⟨e0, he0, by simpa using he0c⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hfind
  have hemem : e ∈ p.entries := List.mem_of_find?_eq_some he
  have hec : e.coords = coordsOf r hf.valid x' p.axes := by simpa using List.find?_some he
  refine ⟨e, hemem, ?_, fun b => ?_⟩
  · unfold recordedIndex
    rw [hp, Option.bind_some, he, Option.map_some]
  · -- the run's score row is local on the information set
    have hinj := ((r.compile hf.valid).closed_iff.1 hf.closed).2.1
    have hloc := DVE.decisionScoreRep_local (keepOfT r hf.valid plan (initT r hf.valid c)) hinj plan
      (DVE.initial (certKernel r hf.valid c) (certKernel_local hm hf.valid)
        (certKernel_nonneg hn hf.valid) (certUtility r hf.valid c) (certUtility_local hm hf.valid))
      d (Finset.mem_univ _)
    have hax : infoVars c d.val = some p.axes := hwf.axes.2
    have hxy : DVE.decisionScoreRep (keepOfT r hf.valid plan (initT r hf.valid c)) plan
        (DVE.initial (certKernel r hf.valid c) (certKernel_local hm hf.valid)
          (certKernel_nonneg hn hf.valid) (certUtility r hf.valid c)
          (certUtility_local hm hf.valid)) d x =
        DVE.decisionScoreRep (keepOfT r hf.valid plan (initT r hf.valid c)) plan
        (DVE.initial (certKernel r hf.valid c) (certKernel_local hm hf.valid)
          (certKernel_nonneg hn hf.valid) (certUtility r hf.valid c)
          (certUtility_local hm hf.valid)) d (entryAssignment r hf.valid p.axes e.coords) := by
      apply hloc
      intro v hv
      rw [hec, entryAssignment_coordsOf r hf.valid p.axes x' v (info_mem_axes hf hm d hax v hv)]
      change x v = if v ∈ (r.compile hf.valid).info d then x v else _
      rw [if_pos hv]
    change DVE.decisionScoreRep _ plan _ d x b = _
    rw [hxy]
    have := (exactRun_spec r hf.valid c hm hn (r.selector hf.valid) plan).2 d
      (entryAssignment r hf.valid p.axes e.coords) b
    unfold DVE.solveRepPlanScore at this
    rw [this, scoreT_of_bucketAt r hf.valid plan _ d B hB]
    rfl

theorem policy_ext {id : FinInfluenceDiagram} {d : id.D} {p q : Policy id ℝ d}
    (hk : p.kernel = q.kernel) : p = q := by
  cases p
  cases q
  cases hk
  rfl

/-- **The recorded strategy is the exact run's**, when the recorded actions agree. -/
theorem recorded_eq_run (hm : Matches r c) (hn : Nonneg c) (hs : s.WellFormed c)
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ)
    (hagree : ActionsAgreeWith r hf.valid c s plan) :
    recordedStrategy r hf.valid c s = (runOf hf hm hn plan).strategy := by
  funext d
  apply policy_ext
  funext x a
  obtain ⟨t, hkt, hmax, hleast⟩ := certificate_tables r hf c hm hn
    (keepOfT r hf.valid plan (initT r hf.valid c)) plan d x
  have hag := hagree.2 d
  cases hp : s.policies[d.val]? with
  | none => rw [hp] at hag; exact hag.elim
  | some p =>
    rw [hp] at hag
    change OptHolds _ _ at hag
    cases hB : bucketAt r hf.valid plan (initT r hf.valid c) d with
    | none => rw [hB] at hag; exact hag.elim
    | some B =>
      rw [hB] at hag
      change ∀ e ∈ p.entries, _ at hag
      obtain ⟨e, he, hidx, hscore⟩ := entry_of_row hf s hm hn hs plan d p hp B hB x
      simp only [scoreOf] at hscore
      obtain ⟨hi, hfmax, hfleast⟩ := hag e he
      have hrec : recordedAction r hf.valid c s d x = ⟨entryIndex c p e, hi⟩ := by
        unfold recordedAction
        rw [hidx]
        simp only [dif_pos hi]
      have hti : t = ⟨entryIndex c p e, hi⟩ := by
        have h1 : t.val ≤ entryIndex c p e := by
          have := hleast ⟨entryIndex c p e, hi⟩ fun b => by
            rw [hscore, hscore]
            exact_mod_cast hfmax b
          rw [Records.Diagram.statePosition_eq, Records.Diagram.statePosition_eq] at this
          exact this
        have h2 : entryIndex c p e ≤ t.val := hfleast t fun b => by
          have := hmax b
          rw [hscore, hscore] at this
          exact_mod_cast this
        exact Fin.ext (le_antisymm h1 h2)
      change (if a = recordedAction r hf.valid c s d x then (1 : ℝ) else 0) = _
      rw [hkt a, hrec, hti]

/-- The recorded action is within `τ` of the maximum of the run's score row, when the binary64
comparison holds. -/
theorem recorded_within (hm : Matches r c) (hn : Nonneg c) (hs : s.WellFormed c) {τ : ℚ}
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ)
    (hw : AllEntries r hf.valid c s plan (fun _ p e f => EntryWithin f (entryIndex c p e) τ))
    (d : Fin r.nd) (x : (r.compile hf.valid).Assignment) (b) :
    scoreOf hf hm hn plan d x b ≤
      scoreOf hf hm hn plan d x (recordedAction r hf.valid c s d x) + τ := by
  have hag := hw d
  cases hp : s.policies[d.val]? with
  | none => rw [hp] at hag; exact hag.elim
  | some p =>
    rw [hp] at hag
    change OptHolds _ _ at hag
    cases hB : bucketAt r hf.valid plan (initT r hf.valid c) d with
    | none => rw [hB] at hag; exact hag.elim
    | some B =>
      rw [hB] at hag
      change ∀ e ∈ p.entries, _ at hag
      obtain ⟨e, he, hidx, hscore⟩ := entry_of_row hf s hm hn hs plan d p hp B hB x
      obtain ⟨hi, hfw⟩ := hag e he
      have hrec : recordedAction r hf.valid c s d x = ⟨entryIndex c p e, hi⟩ := by
        unfold recordedAction
        rw [hidx]
        simp only [dif_pos hi]
      rw [hrec, hscore, hscore]
      exact_mod_cast hfw b

end Run

/-! ## The headline theorems -/

section Headline

variable {r : Diagram} (h : r.FullValid) {c : Certificate} {s : Solution}

/-- **Julia's recorded solution of an exact run is the exact run's, hence optimal.** If the
certificate matches the checked diagram (`certificateMatches`), its cells are nonnegative, its
solution decodes (`Solution.WellFormed`) and `solutionMatches` holds, then Julia's elimination
order is a plan (`solutionPlan`) and, for that plan and the representative choice `keepOfT` (the
branch of Julia's `sum_out`):

* Julia's recorded strategy is the exact DVE run's strategy on the certificate's data, and the
  recorded value is that run's value (exactly, as a rational);
* on every information row the recorded action is the action of least `state_position` among the
  maximizers of the run's own score (`certificate_tables`);
* if every CPT row sums to exactly one (`ExactNormalised`), the recorded strategy is
  deterministic and optimal and the recorded value is the optimum. -/
theorem recorded_solution_optimal (hm : certificateMatches r h c) (hn : Nonneg c)
    (hs : s.WellFormed c) (hsm : solutionMatches r h.valid c s = true) :
    (∃ plan : DVE.Plan (r.compile h.valid) Finset.univ, solutionPlan r h.valid s = some plan ∧
      let keep := keepOfT r h.valid plan (initT r h.valid c)
      let sol := DVE.solveRepPlanWith (r.selector h.valid) keep (certKernel r h.valid c)
        (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
        (certUtility_local hm h.valid) plan
      recordedStrategy r h.valid c s = sol.strategy ∧ (s.value.toRat : ℝ) = sol.value ∧
        ∀ (d : (r.compile h.valid).D) (x : (r.compile h.valid).Assignment),
          (∀ b, DVE.solveRepPlanScore keep (certKernel r h.valid c) (certKernel_local hm h.valid)
              (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
              (certUtility_local hm h.valid) plan d x b ≤
            DVE.solveRepPlanScore keep (certKernel r h.valid c) (certKernel_local hm h.valid)
              (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
              (certUtility_local hm h.valid) plan d x (recordedAction r h.valid c s d x)) ∧
          ∀ b, (∀ c', DVE.solveRepPlanScore keep (certKernel r h.valid c)
                (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid)
                (certUtility r h.valid c) (certUtility_local hm h.valid) plan d x c' ≤
              DVE.solveRepPlanScore keep (certKernel r h.valid c) (certKernel_local hm h.valid)
                (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
                (certUtility_local hm h.valid) plan d x b) →
            r.statePosition h.valid _ (recordedAction r h.valid c s d x) ≤
              r.statePosition h.valid _ b) ∧
    (ExactNormalised r c →
      (recordedStrategy r h.valid c s).Deterministic ∧
        expectedUtility (certKernel r h.valid c) (recordedStrategy r h.valid c s)
          (certUtility r h.valid c) = optimalValue (certKernel r h.valid c) (certUtility r h.valid c) ∧
        (s.value.toRat : ℝ) = optimalValue (certKernel r h.valid c) (certUtility r h.valid c)) := by
  obtain ⟨plan, hplan, hagree, -, -, -, hval⟩ := solutionMatches_spec r h.valid c s hsm
  have hrec := recorded_eq_run h s hm hn hs plan hagree
  have hv : (s.value.toRat : ℝ) = (runOf h hm hn plan).value := by
    rw [(exactRun_spec r h.valid c hm hn (r.selector h.valid) plan).1, hval]
  refine ⟨⟨plan, hplan, hrec, hv, fun d x => ?_⟩, fun hex => ?_⟩
  · obtain ⟨t, hkt, hmax, hleast⟩ := certificate_tables r h c hm hn
      (keepOfT r h.valid plan (initT r h.valid c)) plan d x
    have hta : recordedAction r h.valid c s d x = t := by
      have := congrFun (congrArg (fun σ : Strategy (r.compile h.valid) ℝ => (σ d).kernel x) hrec) t
      simp only [recordedStrategy, Policy.ofFun_kernel] at this
      rw [hkt t, if_pos rfl] at this
      by_contra hne
      rw [if_neg (Ne.symm hne)] at this
      exact absurd this (by norm_num)
    rw [hta]
    exact ⟨hmax, hleast⟩
  · have hspec := DVE.solveRepPlanWith_spec (r.selector h.valid)
      (keepOfT r h.valid plan (initT r h.valid c)) (certKernel r h.valid c) h.closed h.idOrder
      (certKernel_local hm h.valid) (certKernel_normalised hm hex h.valid)
      (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid) plan
    refine ⟨recordedStrategy_deterministic r h.valid c s, ?_, ?_⟩
    · rw [hrec, hspec.2.1, hspec.2.2]
    · rw [hv, hspec.2.2]

/-- **Near-optimality of Julia's recorded solution of an exact run**, for a certificate whose
rows sum to one only up to `ε = certificateEpsilon c < 1`: the recorded strategy and value carry
the bounds of `certificate_approx_optimal` against the row-normalised model `certNormKernel`, with
`e = approxError ε n Umax`. -/
theorem recorded_solution_approx_optimal (hm : certificateMatches r h c) (hn : Nonneg c)
    (hs : s.WellFormed c) (hsm : solutionMatches r h.valid c s = true)
    (hε : certificateEpsilon c < 1) :
    let e : ℝ := approxError (certificateEpsilon c) (certChanceCount c) (certUmax c)
    (recordedStrategy r h.valid c s).Deterministic ∧
      (∀ τ : Strategy (r.compile h.valid) ℝ, τ.Nonneg →
        expectedUtility (certNormKernel r h.valid c) τ (certUtility r h.valid c) ≤
          expectedUtility (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
            (certUtility r h.valid c) + 2 * e) ∧
      optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) - 2 * e ≤
        expectedUtility (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
          (certUtility r h.valid c) ∧
      expectedUtility (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
          (certUtility r h.valid c) ≤
        optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) ∧
      |(s.value.toRat : ℝ) - optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c)| ≤
        e := by
  intro e
  obtain ⟨plan, -, hagree, -, -, -, hval⟩ := solutionMatches_spec r h.valid c s hsm
  have hrec := recorded_eq_run h s hm hn hs plan hagree
  have hv : (s.value.toRat : ℝ) = (runOf h hm hn plan).value := by
    rw [(exactRun_spec r h.valid c hm hn (r.selector h.valid) plan).1, hval]
  have ha := certificate_approx_optimal r h c hm hn hε (r.selector h.valid)
    (keepOfT r h.valid plan (initT r h.valid c)) plan
  rw [hrec, hv]
  exact ha

/-- **Julia's recorded solution of a binary64 run.** Under `solutionWithin τ τv` and
`certificateEpsilon c < 1`, for the plan of Julia's order (`solutionPlan`) and the representative
choice `keepOfT`:

* on every information row, the recorded action is within `τ` of the maximum of the exact run's
  score row;
* the recorded value is within `τv + e` of the optimum of the row-normalised model;
* if moreover the recorded actions agree with the exact run's (`actionsAgree`), the recorded
  strategy is the exact run's and is within `2 e` of that optimum. -/
theorem recorded_binary64_approx_optimal (hm : certificateMatches r h c) (hn : Nonneg c)
    (hs : s.WellFormed c) {τ τv : ℚ} (hw : solutionWithin r h.valid c s τ τv = true)
    (hε : certificateEpsilon c < 1) :
    let e : ℝ := approxError (certificateEpsilon c) (certChanceCount c) (certUmax c)
    (∃ plan : DVE.Plan (r.compile h.valid) Finset.univ, solutionPlan r h.valid s = some plan ∧
      let keep := keepOfT r h.valid plan (initT r h.valid c)
      ∀ (d : (r.compile h.valid).D) (x : (r.compile h.valid).Assignment) b,
        DVE.solveRepPlanScore keep (certKernel r h.valid c) (certKernel_local hm h.valid)
            (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid)
            plan d x b ≤
          DVE.solveRepPlanScore keep (certKernel r h.valid c) (certKernel_local hm h.valid)
            (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid)
            plan d x (recordedAction r h.valid c s d x) + τ) ∧
      |(s.value.toRat : ℝ) - optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c)| ≤
        τv + e ∧
      (actionsAgree r h.valid c s = true →
        (recordedStrategy r h.valid c s).Deterministic ∧
        (∀ τ' : Strategy (r.compile h.valid) ℝ, τ'.Nonneg →
          expectedUtility (certNormKernel r h.valid c) τ' (certUtility r h.valid c) ≤
            expectedUtility (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
              (certUtility r h.valid c) + 2 * e) ∧
        optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) - 2 * e ≤
          expectedUtility (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
            (certUtility r h.valid c)) := by
  intro e
  obtain ⟨plan, hplan, -, hwe, hval⟩ := solutionWithin_spec r h.valid c s hw
  have ha := certificate_approx_optimal r h c hm hn hε (r.selector h.valid)
    (keepOfT r h.valid plan (initT r h.valid c)) plan
  refine ⟨⟨plan, hplan, fun d x b => recorded_within h s hm hn hs plan hwe d x b⟩, ?_,
    fun hag => ?_⟩
  · have hv := (exactRun_spec r h.valid c hm hn (r.selector h.valid) plan).1
    have hval' : |(s.value.toRat : ℝ) - (valueT r h.valid plan (initT r h.valid c) : ℝ)| ≤ τv := by
      exact_mod_cast hval
    have hrun := ha.2.2.2.2
    change |(runOf h hm hn plan).value - _| ≤ e at hrun
    rw [hv] at hrun
    calc |(s.value.toRat : ℝ) - optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c)|
        ≤ |(s.value.toRat : ℝ) - (valueT r h.valid plan (initT r h.valid c) : ℝ)| +
          |(valueT r h.valid plan (initT r h.valid c) : ℝ) -
            optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c)| :=
          abs_sub_le _ _ _
      _ ≤ τv + e := add_le_add hval' hrun
  · obtain ⟨plan', hplan', hagree⟩ := actionsAgree_spec r h.valid c s hag
    rw [hplan] at hplan'
    cases hplan'
    have hrec := recorded_eq_run h s hm hn hs plan hagree
    rw [hrec]
    exact ⟨ha.1, ha.2.1, ha.2.2.1⟩

end Headline

end InfluenceDiagramsProofs.DVECertificate
