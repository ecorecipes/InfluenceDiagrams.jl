import InfluenceDiagramsProofs.Finite.DVE.SolutionCheck
import InfluenceDiagramsProofs.Finite.DVE.SolutionEvidence

/-!
# Checking Julia's recorded solution of a run with hard evidence

`Finite/DVE/SolutionCheck.lean` compares Julia's recorded solution with the exact run when the
certificate has no evidence row. This module drops that restriction: the comparison is with the
exact run of `Finite/DVE/SolutionEvidence.lean` on the certificate's data sliced at its hard
rows, which is what Julia's run conditions on (`conditioned_on = "evidence.hard"`).

* `solutionPlanE`: Julia's recorded order with the observed variables put back
  (`withObserved`), as a plan of all variables (`planOf`);
* `solutionMatchesE` (decidable, exact runs): every recorded action is the least-position
  maximizer of the exact sliced run's score row, every recorded score that row's maximum, the
  recorded value the run's value, and the run's final mass (Julia's evidence probability,
  `massST`) is positive;
* `solutionWithinE τ τv` (decidable, binary64 runs): every recorded action within `τ` of its
  exact row maximum, the value within `τv`, the final mass positive.

Without evidence rows these are the run of `SolutionCheck.lean` up to the positivity check (the
sliced run skips no variable then).

**Theorems**, writing `ev = certHardEvidence` for the certificate's hard rows as hard evidence
of the compiled diagram, and the conditional problem of `Evidence.lean` for it
(`conditionalEU`, `conditionalOptimalValue`, the evidence mass `Z`):

* `recorded_solution_optimal_evidence`: under `solutionMatchesE`, Julia's recorded strategy and
  value are the exact sliced run's, and on every information row the recorded action is the
  least-position maximizer of the run's own score; if every CPT row sums to exactly one, the
  evidence mass is positive and the recorded strategy (deterministic) and value are
  conditionally optimal;
* `recorded_solution_approx_optimal_evidence`: under `solutionMatchesE` and
  `certificateEpsilon c < 1`, the recorded strategy is within `2 e` of the conditional optimum of
  the row-normalised model and the recorded value within `e`;
* `recorded_binary64_near_optimal_evidence`: under `solutionWithinE τ τv` and
  `certificateEpsilon c < 1`, every recorded action is within `τ` of its exact row maximum, the
  recorded value within `τv + e` of the conditional optimum of the row-normalised model, and the
  recorded strategy within `2 e + nd * τ` of every nonnegative strategy and of that optimum, with
  no agreement of actions assumed; `recorded_binary64_near_optimal_evidence_exact`: on an exactly
  normalised certificate, within `nd * τ` and `τv` of the certificate model's conditional optimum.

On rows that contradict the evidence the recorded table is Julia's sliced table (constant along
the observed coordinates); the bounds hold for it as recorded. Trusted: `Lean.Json.parse`,
Julia's exporter and its run, which is compared, not proved.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVECertificate

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram
open BayesianNetworksProofs.Raw InfluenceDiagramsProofs.Records Spec

variable (r : Diagram) (h : r.Valid) (c : Certificate) (s : Solution)

/-! ## The comparison -/

/-- Every entry of every decision's policy satisfies `P` against the score row of the exact run
with evidence. -/
def AllEntriesE {R : Finset (Fin r.nv)} (plan : DVE.Plan (r.compile h) R)
    (P : (d : Fin r.nd) → PolicyRecord → PolicyEntry →
      (Fin (r.stateCount (r.decisions d).action) → ℚ) → Prop) : Prop :=
  ∀ d : Fin r.nd, OptHolds (fun p => OptHolds
    (fun B => ∀ e ∈ p.entries, P d p e (rowScore r h B d p e))
    (bucketAtS r h plan (initCT r h c) d)) s.policies[d.val]?

instance {R : Finset (Fin r.nv)} (plan : DVE.Plan (r.compile h) R)
    (P : (d : Fin r.nd) → PolicyRecord → PolicyEntry →
      (Fin (r.stateCount (r.decisions d).action) → ℚ) → Prop)
    [∀ d p e f, Decidable (P d p e f)] : Decidable (AllEntriesE r h c s plan P) := by
  unfold AllEntriesE; infer_instance

/-- The plan of Julia's recorded order, with the observed variables put back. -/
def solutionPlanE : Option (DVE.Plan (r.compile h) Finset.univ) :=
  (toFinList r s.eliminationOrder).bind fun o =>
    planOf r h (withObserved r h (finsetList (certObserved r c)) o) Finset.univ

/-- Every recorded action is the exact sliced run's. -/
def ActionsAgreeWithE (plan : DVE.Plan (r.compile h) Finset.univ) : Prop :=
  AllEntriesE r h c s plan fun _ p e f => EntryAction f (entryIndex c p e)

/-- **The exact comparison with evidence**, on a plan. -/
def SolutionMatchesWithE (plan : DVE.Plan (r.compile h) Finset.univ) : Prop :=
  ActionsAgreeWithE r h c s plan ∧ s.arithmetic = .exactRational ∧ DataConsistent c s ∧
    AllEntriesE r h c s plan (fun _ p e f => EntryScore f (entryIndex c p e) e.score.toRat) ∧
    s.value.toRat = valueST r h plan (initCT r h c) ∧ 0 < massST r h plan (initCT r h c)

/-- **The binary64 comparison with evidence**, on a plan, with tolerances `τ` and `τv`. -/
def SolutionWithinWithE (τ τv : ℚ) (plan : DVE.Plan (r.compile h) Finset.univ) : Prop :=
  AllEntriesE r h c s plan (fun _ p e f => EntryWithin f (entryIndex c p e) τ) ∧
    |s.value.toRat - valueST r h plan (initCT r h c)| ≤ τv ∧ 0 < massST r h plan (initCT r h c)

instance (plan : DVE.Plan (r.compile h) Finset.univ) :
    Decidable (ActionsAgreeWithE r h c s plan) := by
  unfold ActionsAgreeWithE; infer_instance

instance (plan : DVE.Plan (r.compile h) Finset.univ) :
    Decidable (SolutionMatchesWithE r h c s plan) := by
  unfold SolutionMatchesWithE; infer_instance

instance (τ τv : ℚ) (plan : DVE.Plan (r.compile h) Finset.univ) :
    Decidable (SolutionWithinWithE r h c s τ τv plan) := by
  unfold SolutionWithinWithE; infer_instance

/-- **The checker for exact runs with evidence** (decidable). -/
def solutionMatchesE : Bool :=
  match solutionPlanE r h c s with
  | some plan => decide (SolutionMatchesWithE r h c s plan)
  | none => false

/-- Every recorded action is the exact sliced run's. -/
def actionsAgreeE : Bool :=
  match solutionPlanE r h c s with
  | some plan => decide (ActionsAgreeWithE r h c s plan)
  | none => false

/-- **The checker for binary64 runs with evidence** (decidable), with tolerances `τ` and `τv`. -/
def solutionWithinE (τ τv : ℚ) : Bool :=
  match solutionPlanE r h c s with
  | some plan => decide (SolutionWithinWithE r h c s τ τv plan)
  | none => false

theorem solutionMatchesE_spec (hsm : solutionMatchesE r h c s = true) :
    ∃ plan, solutionPlanE r h c s = some plan ∧ SolutionMatchesWithE r h c s plan := by
  unfold solutionMatchesE at hsm
  split at hsm
  · rename_i plan hp
    exact ⟨plan, hp, of_decide_eq_true hsm⟩
  · cases hsm

theorem actionsAgreeE_spec (hsm : actionsAgreeE r h c s = true) :
    ∃ plan, solutionPlanE r h c s = some plan ∧ ActionsAgreeWithE r h c s plan := by
  unfold actionsAgreeE at hsm
  split at hsm
  · rename_i plan hp
    exact ⟨plan, hp, of_decide_eq_true hsm⟩
  · cases hsm

theorem solutionWithinE_spec {τ τv : ℚ} (hsm : solutionWithinE r h c s τ τv = true) :
    ∃ plan, solutionPlanE r h c s = some plan ∧ SolutionWithinWithE r h c s τ τv plan := by
  unfold solutionWithinE at hsm
  split at hsm
  · rename_i plan hp
    exact ⟨plan, hp, of_decide_eq_true hsm⟩
  · cases hsm

/-! ## The run's tables at the recorded entries -/

section Run

variable {r : Diagram} (hf : r.FullValid) {c : Certificate} (s : Solution)

/-- The exact sliced run on a plan. -/
noncomputable abbrev runOfE (hm : Matches r c) (hn : Nonneg c)
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ) :=
  DVE.solveCondRepPlanWith (r.selector hf.valid) (keepOfST r hf.valid plan (initCT r hf.valid c))
    (certKernel r hf.valid c) (certKernel_local hm hf.valid) (certKernel_nonneg hn hf.valid)
    (certUtility r hf.valid c) (certUtility_local hm hf.valid) (certObserved r c)
    (certObservedValue r hf.valid c) plan

/-- The exact sliced run's score rows on a plan. -/
noncomputable abbrev scoreOfE (hm : Matches r c) (hn : Nonneg c)
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ) :=
  DVE.solveCondRepPlanScore (keepOfST r hf.valid plan (initCT r hf.valid c))
    (certKernel r hf.valid c) (certKernel_local hm hf.valid) (certKernel_nonneg hn hf.valid)
    (certUtility r hf.valid c) (certUtility_local hm hf.valid) (certObserved r c)
    (certObservedValue r hf.valid c) plan

/-- **The first-label table of the sliced run**, on every information row. -/
theorem tablesE (hm : Matches r c) (hn : Nonneg c)
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ) (d : (r.compile hf.valid).D)
    (x : (r.compile hf.valid).Assignment) :
    ∃ t, (∀ a, ((runOfE hf hm hn plan).strategy d).kernel x a = if a = t then 1 else 0) ∧
      (∀ b, scoreOfE hf hm hn plan d x b ≤ scoreOfE hf hm hn plan d x t) ∧
      ∀ b, (∀ c', scoreOfE hf hm hn plan d x c' ≤ scoreOfE hf hm hn plan d x b) →
        r.statePosition hf.valid _ t ≤ r.statePosition hf.valid _ b := by
  have hinj := ((r.compile hf.valid).closed_iff.1 hf.closed).2.1
  refine ⟨_, fun a => @DVE.runRepSkipWith_kernel (r.compile hf.valid) (r.selector hf.valid)
    (keepOfST r hf.valid plan (initCT r hf.valid c)) hinj _ _ _ _ d (Finset.mem_univ _) x a, ?_⟩
  exact @firstArgmax_least_position _ ((r.compile hf.valid).fintypeS _)
    ((r.compile hf.valid).nonemptyS _) _ (r.statePosition_injective hf.valid _) _

/-- **At every information row, the recorded entry and the exact sliced score row.** -/
theorem entry_of_rowE (hm : Matches r c) (hn : Nonneg c) (hs : s.WellFormed c)
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ) (d : Fin r.nd) (p : PolicyRecord)
    (hp : s.policies[d.val]? = some p) (B : List (TVal r))
    (hB : bucketAtS r hf.valid plan (initCT r hf.valid c) d = some B)
    (x : (r.compile hf.valid).Assignment) :
    ∃ e ∈ p.entries, recordedIndex r hf.valid c s d (infoProject r hf.valid d x) =
        some (entryIndex c p e) ∧
      ∀ b, scoreOfE hf hm hn plan d x b = (rowScore r hf.valid B d p e b : ℝ) := by
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
  have hfind :
      (p.entries.find? fun e => decide (e.coords = coordsOf r hf.valid x' p.axes)).isSome := by
    rw [List.find?_isSome]
    exact ⟨e0, he0, by simpa using he0c⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hfind
  have hemem : e ∈ p.entries := List.mem_of_find?_eq_some he
  have hec : e.coords = coordsOf r hf.valid x' p.axes := by simpa using List.find?_some he
  refine ⟨e, hemem, ?_, fun b => ?_⟩
  · unfold recordedIndex
    rw [hp, Option.bind_some, he, Option.map_some]
  · have hinj := ((r.compile hf.valid).closed_iff.1 hf.closed).2.1
    have hloc := DVE.decisionScoreRepSkip_local (keepOfST r hf.valid plan (initCT r hf.valid c))
      hinj plan
      (DVE.initialConditioned (certKernel r hf.valid c) (certKernel_local hm hf.valid)
        (certKernel_nonneg hn hf.valid) (certUtility r hf.valid c)
        (certUtility_local hm hf.valid) (certObserved r c) (certObservedValue r hf.valid c))
      d (Finset.mem_univ _)
    have hax : infoVars c d.val = some p.axes := hwf.axes.2
    have hxy : DVE.decisionScoreRepSkip (keepOfST r hf.valid plan (initCT r hf.valid c)) plan
        (DVE.initialConditioned (certKernel r hf.valid c) (certKernel_local hm hf.valid)
          (certKernel_nonneg hn hf.valid) (certUtility r hf.valid c)
          (certUtility_local hm hf.valid) (certObserved r c) (certObservedValue r hf.valid c))
          d x =
        DVE.decisionScoreRepSkip (keepOfST r hf.valid plan (initCT r hf.valid c)) plan
        (DVE.initialConditioned (certKernel r hf.valid c) (certKernel_local hm hf.valid)
          (certKernel_nonneg hn hf.valid) (certUtility r hf.valid c)
          (certUtility_local hm hf.valid) (certObserved r c) (certObservedValue r hf.valid c))
          d (entryAssignment r hf.valid p.axes e.coords) := by
      apply hloc
      intro v hv
      rw [hec, entryAssignment_coordsOf r hf.valid p.axes x' v (info_mem_axes hf hm d hax v hv)]
      change x v = if v ∈ (r.compile hf.valid).info d then x v else _
      rw [if_pos hv]
    change DVE.decisionScoreRepSkip _ plan _ d x b = _
    rw [hxy]
    have := (exactRunC_spec r hf.valid c hm hn (r.selector hf.valid) plan).2.1 d
      (entryAssignment r hf.valid p.axes e.coords) b
    unfold DVE.solveCondRepPlanScore at this
    rw [this, scoreST_of_bucketAtS r hf.valid plan _ d B hB]
    rfl

/-- **The recorded strategy is the exact sliced run's**, when the recorded actions agree. -/
theorem recorded_eq_runE (hm : Matches r c) (hn : Nonneg c) (hs : s.WellFormed c)
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ)
    (hagree : ActionsAgreeWithE r hf.valid c s plan) :
    recordedStrategy r hf.valid c s = (runOfE hf hm hn plan).strategy := by
  funext d
  apply policy_ext
  funext x a
  obtain ⟨t, hkt, hmax, hleast⟩ := tablesE hf hm hn plan d x
  have hag := hagree d
  cases hp : s.policies[d.val]? with
  | none => rw [hp] at hag; exact hag.elim
  | some p =>
    rw [hp] at hag
    change OptHolds _ _ at hag
    cases hB : bucketAtS r hf.valid plan (initCT r hf.valid c) d with
    | none => rw [hB] at hag; exact hag.elim
    | some B =>
      rw [hB] at hag
      change ∀ e ∈ p.entries, _ at hag
      obtain ⟨e, he, hidx, hscore⟩ := entry_of_rowE hf s hm hn hs plan d p hp B hB x
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

/-- The recorded action is within `τ` of the maximum of the exact sliced run's score row. -/
theorem recorded_withinE (hm : Matches r c) (hn : Nonneg c) (hs : s.WellFormed c) {τ : ℚ}
    (plan : DVE.Plan (r.compile hf.valid) Finset.univ)
    (hw : AllEntriesE r hf.valid c s plan (fun _ p e f => EntryWithin f (entryIndex c p e) τ))
    (d : Fin r.nd) (x : (r.compile hf.valid).Assignment) (b) :
    scoreOfE hf hm hn plan d x b ≤
      scoreOfE hf hm hn plan d x (recordedAction r hf.valid c s d x) + τ := by
  have hag := hw d
  cases hp : s.policies[d.val]? with
  | none => rw [hp] at hag; exact hag.elim
  | some p =>
    rw [hp] at hag
    change OptHolds _ _ at hag
    cases hB : bucketAtS r hf.valid plan (initCT r hf.valid c) d with
    | none => rw [hB] at hag; exact hag.elim
    | some B =>
      rw [hB] at hag
      change ∀ e ∈ p.entries, _ at hag
      obtain ⟨e, he, hidx, hscore⟩ := entry_of_rowE hf s hm hn hs plan d p hp B hB x
      obtain ⟨hi, hfw⟩ := hag e he
      have hrec : recordedAction r hf.valid c s d x = ⟨entryIndex c p e, hi⟩ := by
        unfold recordedAction
        rw [hidx]
        simp only [dif_pos hi]
      rw [hrec, hscore, hscore]
      exact_mod_cast hfw b

/-- The evidence mass of the row-normalised model is positive when the exact sliced run's final
mass is. -/
theorem evidenceMass_pos (hm : certificateMatches r hf c) (hn : Nonneg c)
    (hε : certificateEpsilon c < 1) (plan : DVE.Plan (r.compile hf.valid) Finset.univ)
    (hpos : 0 < massST r hf.valid plan (initCT r hf.valid c)) :
    0 < DVE.evidenceMass (certNormKernel r hf.valid c) DVE.defaultStrategy
      (certHardEvidence r c hm hf).toEvidence := by
  have hε1 : (certificateEpsilon c : ℝ) < 1 := by exact_mod_cast hε
  have hε0 : (0 : ℝ) ≤ certificateEpsilon c := by exact_mod_cast certificateEpsilon_nonneg c
  have hL : 0 < (1 - (certificateEpsilon c : ℝ)) ^ certChanceCount c := pow_pos (by linarith) _
  have hLH : (1 - (certificateEpsilon c : ℝ)) ^ certChanceCount c ≤
      (1 + (certificateEpsilon c : ℝ)) ^ certChanceCount c :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hU : (0 : ℝ) ≤ certUmax c := by exact_mod_cast certUmax_nonneg c
  have hmass := DVE.solveCondRepPlan_mass (keepOfST r hf.valid plan (initCT r hf.valid c))
    (certNormKernel r hf.valid c) (certKernel r hf.valid c) hf.closed hf.idOrder
    (certNormKernel_local hm hf.valid) (certNormKernel_normalised hm hε hf.valid)
    (certNormKernel_nonneg hn hf.valid) (certKernel_local hm hf.valid)
    (certKernel_nonneg hn hf.valid) (certUtility r hf.valid c) (certUtility_local hm hf.valid)
    (certHardEvidence r c hm hf) plan _ _ _ hL hLH hU (certKernel_envelope hm hn hε hf.valid)
    (certUtility_total_le hm hf.valid)
  have hval := (exactRunC_spec r hf.valid c hm hn (r.selector hf.valid) plan).2.2
  have hp : (0 : ℝ) < massST r hf.valid plan (initCT r hf.valid c) := by exact_mod_cast hpos
  have hH : 0 < (1 + (certificateEpsilon c : ℝ)) ^ certChanceCount c := pow_pos (by linarith) _
  have h2 := hmass.2
  change DVE.solveCondRepPlanMass _ _ _ _ _ _ (certObserved r c) (certObservedValue r hf.valid c)
    plan ≤ _ at h2
  rw [hval] at h2
  exact pos_of_mul_pos_right (lt_of_lt_of_le hp h2) hH.le

end Run

/-! ## The headline theorems -/

section Headline

variable {r : Diagram} (h : r.FullValid) {c : Certificate} {s : Solution}

/-- **Julia's recorded solution of an exact run with hard evidence is the exact sliced run's,
hence conditionally optimal.** If the certificate matches the checked diagram, its cells are
nonnegative, its solution decodes and `solutionMatchesE` holds, then for the plan of Julia's
order with the observed variables put back (`solutionPlanE`) and the representative `keepOfST`:

* Julia's recorded strategy is the exact sliced run's strategy and the recorded value its value;
* on every information row the recorded action is the action of least `state_position` among
  the maximizers of the run's own score;
* if every CPT row sums to exactly one, the evidence mass of the certificate's model is positive
  and the recorded strategy is deterministic, its conditional expected utility given the hard
  rows is the conditional optimum, and so is the recorded value. -/
theorem recorded_solution_optimal_evidence (hm : certificateMatches r h c) (hn : Nonneg c)
    (hs : s.WellFormed c) (hsm : solutionMatchesE r h.valid c s = true) :
    (∃ plan : DVE.Plan (r.compile h.valid) Finset.univ, solutionPlanE r h.valid c s = some plan ∧
      recordedStrategy r h.valid c s = (runOfE h hm hn plan).strategy ∧
      (s.value.toRat : ℝ) = (runOfE h hm hn plan).value ∧
      ∀ (d : (r.compile h.valid).D) (x : (r.compile h.valid).Assignment),
        (∀ b, scoreOfE h hm hn plan d x b ≤
          scoreOfE h hm hn plan d x (recordedAction r h.valid c s d x)) ∧
        ∀ b, (∀ c', scoreOfE h hm hn plan d x c' ≤ scoreOfE h hm hn plan d x b) →
          r.statePosition h.valid _ (recordedAction r h.valid c s d x) ≤
            r.statePosition h.valid _ b) ∧
    (ExactNormalised r c →
      (recordedStrategy r h.valid c s).Deterministic ∧
      0 < DVE.evidenceMass (certKernel r h.valid c) DVE.defaultStrategy
        (certHardEvidence r c hm h).toEvidence ∧
      DVE.conditionalEU (certKernel r h.valid c) (recordedStrategy r h.valid c s)
          (certUtility r h.valid c) (certHardEvidence r c hm h).toEvidence =
        DVE.conditionalOptimalValue (certKernel r h.valid c) (certUtility r h.valid c)
          (certHardEvidence r c hm h).toEvidence ∧
      (s.value.toRat : ℝ) = DVE.conditionalOptimalValue (certKernel r h.valid c)
        (certUtility r h.valid c) (certHardEvidence r c hm h).toEvidence) := by
  obtain ⟨plan, hplan, hagree, -, -, -, hval, hpos⟩ := solutionMatchesE_spec r h.valid c s hsm
  have hrec := recorded_eq_runE h s hm hn hs plan hagree
  have hv : (s.value.toRat : ℝ) = (runOfE h hm hn plan).value := by
    rw [(exactRunC_spec r h.valid c hm hn (r.selector h.valid) plan).1, hval]
  refine ⟨⟨plan, hplan, hrec, hv, fun d x => ?_⟩, fun hex => ?_⟩
  · obtain ⟨t, hkt, hmax, hleast⟩ := tablesE h hm hn plan d x
    have hta : recordedAction r h.valid c s d x = t := by
      have := congrFun (congrArg (fun σ : Strategy (r.compile h.valid) ℝ => (σ d).kernel x) hrec) t
      simp only [recordedStrategy, Policy.ofFun_kernel] at this
      rw [hkt t, if_pos rfl] at this
      by_contra hne
      rw [if_neg (Ne.symm hne)] at this
      exact absurd this (by norm_num)
    rw [hta]
    exact ⟨hmax, hleast⟩
  · obtain ⟨h0, hk, -, -⟩ := certificate_approx_exact r h c hm hex
    have hε : certificateEpsilon c < 1 := by rw [h0]; norm_num
    have hZ := evidenceMass_pos h hm hn hε plan hpos
    rw [hk] at hZ
    have hspec := DVE.solveCondRepPlan_spec (r.selector h.valid)
      (keepOfST r h.valid plan (initCT r h.valid c)) (certKernel r h.valid c) h.closed h.idOrder
      (certKernel_local hm h.valid) (certKernel_normalised hm hex h.valid)
      (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid)
      (certHardEvidence r c hm h) plan hZ
    obtain ⟨-, hreal, hopt, -, -⟩ := hspec
    refine ⟨recordedStrategy_deterministic r h.valid c s, hZ, ?_, ?_⟩
    · rw [hrec]
      exact hreal.trans hopt
    · rw [hv]
      exact hopt

/-- **Near-optimality of Julia's recorded solution of an exact run with hard evidence**, for a
certificate whose rows sum to one only up to `ε = certificateEpsilon c < 1`: against the
conditional problem of the row-normalised model `certNormKernel`, the recorded strategy is
within `2 e` of every nonnegative strategy and of the conditional optimum, and the recorded
value within `e` of it, `e = approxError ε n Umax`. -/
theorem recorded_solution_approx_optimal_evidence (hm : certificateMatches r h c) (hn : Nonneg c)
    (hs : s.WellFormed c) (hsm : solutionMatchesE r h.valid c s = true)
    (hε : certificateEpsilon c < 1) :
    let e : ℝ := approxError (certificateEpsilon c) (certChanceCount c) (certUmax c)
    let ev := (certHardEvidence r c hm h).toEvidence
    (recordedStrategy r h.valid c s).Deterministic ∧
      0 < DVE.evidenceMass (certNormKernel r h.valid c) DVE.defaultStrategy ev ∧
      (∀ τ : Strategy (r.compile h.valid) ℝ, τ.Nonneg →
        DVE.conditionalEU (certNormKernel r h.valid c) τ (certUtility r h.valid c) ev ≤
          DVE.conditionalEU (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
            (certUtility r h.valid c) ev + 2 * e) ∧
      DVE.conditionalOptimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) ev -
          2 * e ≤
        DVE.conditionalEU (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
          (certUtility r h.valid c) ev ∧
      DVE.conditionalEU (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
          (certUtility r h.valid c) ev ≤
        DVE.conditionalOptimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) ev ∧
      |(s.value.toRat : ℝ) -
          DVE.conditionalOptimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) ev| ≤
        e := by
  intro e ev
  obtain ⟨plan, -, hagree, -, -, -, hval, hpos⟩ := solutionMatchesE_spec r h.valid c s hsm
  have hrec := recorded_eq_runE h s hm hn hs plan hagree
  have hv : (s.value.toRat : ℝ) = (runOfE h hm hn plan).value := by
    rw [(exactRunC_spec r h.valid c hm hn (r.selector h.valid) plan).1, hval]
  have hZ := evidenceMass_pos h hm hn hε plan hpos
  have hε1 : (certificateEpsilon c : ℝ) < 1 := by exact_mod_cast hε
  have hL : 0 < (1 - (certificateEpsilon c : ℝ)) ^ certChanceCount c := pow_pos (by linarith) _
  have hε0 : (0 : ℝ) ≤ certificateEpsilon c := by exact_mod_cast certificateEpsilon_nonneg c
  have hLH : (1 - (certificateEpsilon c : ℝ)) ^ certChanceCount c ≤
      (1 + (certificateEpsilon c : ℝ)) ^ certChanceCount c :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hU : (0 : ℝ) ≤ certUmax c := by exact_mod_cast certUmax_nonneg c
  have ha := DVE.solveCondRepPlan_approx_optimal (r.selector h.valid)
    (keepOfST r h.valid plan (initCT r h.valid c)) (certNormKernel r h.valid c)
    (certKernel r h.valid c) h.closed h.idOrder (certNormKernel_local hm h.valid)
    (certNormKernel_normalised hm hε h.valid) (certNormKernel_nonneg hn h.valid)
    (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
    (certUtility_local hm h.valid) (certHardEvidence r c hm h) plan _ _ _ hL hLH hU
    (certKernel_envelope hm hn hε h.valid) (certUtility_total_le hm h.valid) hZ
  rw [approxGap_eq r h c hm hε plan] at ha
  rw [hrec, hv]
  exact ⟨ha.1, hZ, ha.2⟩

/-- **Julia's recorded solution of a binary64 run with hard evidence.** Under `solutionWithinE τ τv`
and `certificateEpsilon c < 1`, for the plan of Julia's order with the observed variables put back
and the representative `keepOfST`, writing `κ̂` for the row-normalised model, `e = approxError ε n
Umax` and `nd` for the number of decisions:

* on every information row the recorded action is within `τ` of the maximum of the exact sliced
  run's score row;
* the evidence mass of `κ̂` is positive and the recorded value is within `τv + e` of the
  conditional optimum of `κ̂` given the hard rows;
* the recorded strategy (deterministic) is within `2 e + nd * τ` of every nonnegative strategy and
  of that conditional optimum (from below; it never exceeds it), whatever its actions at
  near-ties. -/
theorem recorded_binary64_near_optimal_evidence (hm : certificateMatches r h c) (hn : Nonneg c)
    (hs : s.WellFormed c) {τ τv : ℚ} (hw : solutionWithinE r h.valid c s τ τv = true)
    (hε : certificateEpsilon c < 1) :
    let e : ℝ := approxError (certificateEpsilon c) (certChanceCount c) (certUmax c)
    let ev := (certHardEvidence r c hm h).toEvidence
    (∃ plan : DVE.Plan (r.compile h.valid) Finset.univ, solutionPlanE r h.valid c s = some plan ∧
      ∀ (d : (r.compile h.valid).D) (x : (r.compile h.valid).Assignment) b,
        scoreOfE h hm hn plan d x b ≤
          scoreOfE h hm hn plan d x (recordedAction r h.valid c s d x) + τ) ∧
      0 < DVE.evidenceMass (certNormKernel r h.valid c) DVE.defaultStrategy ev ∧
      |(s.value.toRat : ℝ) -
          DVE.conditionalOptimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) ev| ≤
        τv + e ∧
      (recordedStrategy r h.valid c s).Deterministic ∧
      (∀ τ' : Strategy (r.compile h.valid) ℝ, τ'.Nonneg →
        DVE.conditionalEU (certNormKernel r h.valid c) τ' (certUtility r h.valid c) ev ≤
          DVE.conditionalEU (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
            (certUtility r h.valid c) ev + 2 * e + r.nd * (τ : ℝ)) ∧
      DVE.conditionalOptimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) ev -
          2 * e - r.nd * (τ : ℝ) ≤
        DVE.conditionalEU (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
          (certUtility r h.valid c) ev ∧
      DVE.conditionalEU (certNormKernel r h.valid c) (recordedStrategy r h.valid c s)
          (certUtility r h.valid c) ev ≤
        DVE.conditionalOptimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) ev := by
  intro e ev
  obtain ⟨plan, hplan, hwe, hval, hpos⟩ := solutionWithinE_spec r h.valid c s hw
  have hZ := evidenceMass_pos h hm hn hε plan hpos
  have hε1 : (certificateEpsilon c : ℝ) < 1 := by exact_mod_cast hε
  have hL : 0 < (1 - (certificateEpsilon c : ℝ)) ^ certChanceCount c := pow_pos (by linarith) _
  have hε0 : (0 : ℝ) ≤ certificateEpsilon c := by exact_mod_cast certificateEpsilon_nonneg c
  have hLH : (1 - (certificateEpsilon c : ℝ)) ^ certChanceCount c ≤
      (1 + (certificateEpsilon c : ℝ)) ^ certChanceCount c :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hU : (0 : ℝ) ≤ certUmax c := by exact_mod_cast certUmax_nonneg c
  have ha := DVE.solveCondRepPlan_approx_optimal (r.selector h.valid)
    (keepOfST r h.valid plan (initCT r h.valid c)) (certNormKernel r h.valid c)
    (certKernel r h.valid c) h.closed h.idOrder (certNormKernel_local hm h.valid)
    (certNormKernel_normalised hm hε h.valid) (certNormKernel_nonneg hn h.valid)
    (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
    (certUtility_local hm h.valid) (certHardEvidence r c hm h) plan _ _ _ hL hLH hU
    (certKernel_envelope hm hn hε h.valid) (certUtility_total_le hm h.valid) hZ
  have hnear := DVE.solveCondRepPlan_near_optimal (r.selector h.valid)
    (keepOfST r h.valid plan (initCT r h.valid c)) (certNormKernel r h.valid c)
    (certKernel r h.valid c) h.closed h.idOrder (certNormKernel_local hm h.valid)
    (certNormKernel_normalised hm hε h.valid) (certNormKernel_nonneg hn h.valid)
    (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
    (certUtility_local hm h.valid) (certHardEvidence r c hm h) plan _ _ _ hL hLH hU
    (certKernel_envelope hm hn hε h.valid) (certUtility_total_le hm h.valid) hZ
    (recordedStrategy r h.valid c s) (recordedAction r h.valid c s)
    (fun d x a => by simp [recordedStrategy]) (τ : ℝ)
    (fun d x b => recorded_withinE h s hm hn hs plan hwe d x b)
  rw [approxGap_eq r h c hm hε plan] at ha hnear
  rw [card_decisions] at hnear
  have hrun := ha.2.2.2.2
  have hrv : (DVE.solveCondRepPlanWith (r.selector h.valid)
      (keepOfST r h.valid plan (initCT r h.valid c)) (certKernel r h.valid c)
      (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
      (certUtility_local hm h.valid) (certHardEvidence r c hm h).observed
      (certHardEvidence r c hm h).value plan).value =
      (valueST r h.valid plan (initCT r h.valid c) : ℝ) :=
    (exactRunC_spec r h.valid c hm hn (r.selector h.valid) plan).1
  rw [hrv] at hrun
  have hval' : |(s.value.toRat : ℝ) - (valueST r h.valid plan (initCT r h.valid c) : ℝ)| ≤ τv := by
    exact_mod_cast hval
  have hdet := recordedStrategy_deterministic r h.valid c s
  have hle := DVE.conditionalEU_le_optimal (certNormKernel r h.valid c) h.closed h.idOrder
    (certNormKernel_local hm h.valid) (certNormKernel_normalised hm hε h.valid)
    (certUtility r h.valid c) ev hZ _ (DVE.deterministic_nonneg _ hdet)
  refine ⟨⟨plan, hplan, fun d x b => recorded_withinE h s hm hn hs plan hwe d x b⟩, hZ, ?_,
    hdet, hnear.1, hnear.2, hle⟩
  calc |(s.value.toRat : ℝ) - DVE.conditionalOptimalValue (certNormKernel r h.valid c)
        (certUtility r h.valid c) ev|
      ≤ |(s.value.toRat : ℝ) - (valueST r h.valid plan (initCT r h.valid c) : ℝ)| +
        |(valueST r h.valid plan (initCT r h.valid c) : ℝ) -
          DVE.conditionalOptimalValue (certNormKernel r h.valid c) (certUtility r h.valid c) ev| :=
        abs_sub_le _ _ _
    _ ≤ τv + e := add_le_add hval' hrun

/-- **The exactly normalised case with hard evidence.** On a certificate whose CPT rows sum to
exactly one, under `solutionWithinE τ τv`, the evidence mass is positive, Julia's recorded
strategy is within `nd * τ` of every nonnegative strategy and of the conditional optimum of the
certificate's own model, and the recorded value within `τv` of that optimum. -/
theorem recorded_binary64_near_optimal_evidence_exact (hm : certificateMatches r h c)
    (hn : Nonneg c) (hs : s.WellFormed c) {τ τv : ℚ}
    (hw : solutionWithinE r h.valid c s τ τv = true) (hex : ExactNormalised r c) :
    let ev := (certHardEvidence r c hm h).toEvidence
    0 < DVE.evidenceMass (certKernel r h.valid c) DVE.defaultStrategy ev ∧
      (∀ τ' : Strategy (r.compile h.valid) ℝ, τ'.Nonneg →
        DVE.conditionalEU (certKernel r h.valid c) τ' (certUtility r h.valid c) ev ≤
          DVE.conditionalEU (certKernel r h.valid c) (recordedStrategy r h.valid c s)
            (certUtility r h.valid c) ev + r.nd * (τ : ℝ)) ∧
      DVE.conditionalOptimalValue (certKernel r h.valid c) (certUtility r h.valid c) ev -
          r.nd * (τ : ℝ) ≤
        DVE.conditionalEU (certKernel r h.valid c) (recordedStrategy r h.valid c s)
          (certUtility r h.valid c) ev ∧
      |(s.value.toRat : ℝ) -
          DVE.conditionalOptimalValue (certKernel r h.valid c) (certUtility r h.valid c) ev| ≤
        τv := by
  intro ev
  obtain ⟨h0, hk, he, -⟩ := certificate_approx_exact r h c hm hex
  have hε : certificateEpsilon c < 1 := by rw [h0]; norm_num
  have hnear := recorded_binary64_near_optimal_evidence h hm hn hs hw hε
  simp only [hk, he, Rat.cast_zero, mul_zero, add_zero, sub_zero] at hnear
  exact ⟨hnear.2.1, hnear.2.2.2.2.1, hnear.2.2.2.2.2.1, hnear.2.2.1⟩

end Headline

end InfluenceDiagramsProofs.DVECertificate
