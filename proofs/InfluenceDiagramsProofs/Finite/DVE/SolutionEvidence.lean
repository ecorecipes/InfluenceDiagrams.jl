import InfluenceDiagramsProofs.Finite.DVE.SolutionRun
import InfluenceDiagramsProofs.Finite.DVE.NearOptimalEvidence

/-!
# A computable exact run of the certificate's DVE with hard evidence

Julia's `_decision_elimination` conditions on the model's hard evidence before eliminating
anything: every chance factor and every utility potential is sliced at the observed states and
the observed axes are dropped (`condition`), and a chance block orders only the variables some
current factor mentions, so the observed variables are never summed and do not appear in the
recorded `elimination_order` (`sum_out` of an absent variable is also the identity). The
recorded solution says `conditioned_on = "evidence.hard"`: the certificate's `evidence.hard`
rows, and nothing else, are what the run conditioned on.

This module computes that run exactly over `ℚ`, as `Finite/DVE/SolutionRun.lean` does without
evidence:

* `certObserved r c` and `certObservedValue r h c` read the observed variables and states off
  the certificate's hard rows; `qcondition O o` slices a rational valuation at `clamp O o`
  (`rel_condition`: it is `Valuation.condition` read in `ℚ`);
* `initCT` tabulates the sliced initial valuations; `runST` runs a plan on tables, skipping a
  chance variable that no table mentions (`chanceStepTS`), and `scoreST`, `valueST`, `massST`
  (Julia's evidence probability) and `keepOfST` (Julia's `sum_out` branch) are read off it;
* `withObserved O order` puts the observed variables back into Julia's order, each just before
  the first decision whose information set does not contain it (at the end when every one
  does), so that `planOf` can rebuild a plan of all variables; where they go does not matter to
  the run, which skips them.

**Result.** `exactRunC_spec`: for a matching certificate with nonnegative cells and any plan, the
real run `DVE.solveCondRepPlanWith` of `Finite/DVE/NearOptimalEvidence.lean` on the sliced data,
with `keep := keepOfST plan`, has value `valueST`, score rows `scoreST` and final mass `massST`,
read in `ℝ`. `certHardEvidence` packages the certificate's rows as `HardEvidence` of the compiled
diagram: the observed set is action-free and chance-ancestral because `certificateMatches` puts
every evidence variable before every action in `topological_order`, so the conditional problem
of `Evidence.lean` (`conditionalEU`, `conditionalOptimalValue`) is defined for it.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVECertificate

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram
open BayesianNetworksProofs.Raw InfluenceDiagramsProofs.Records Spec

/-! ## Sliced rational valuations -/

section Condition

variable {bn : FinBayesNet}

/-- Julia's `condition` on a rational valuation: both potentials read at `clamp O o`, the
observed variables dropped from the scope and from the utility variables. -/
def qcondition (O : Finset bn.V) (o : bn.Assignment) (q : QVal bn) : QVal bn :=
  ⟨q.scope \ O, q.uvars \ O, fun x => q.prob (clamp O o x), fun x => q.util (clamp O o x)⟩

theorem rel_condition {q : QVal bn} {v : DVE.Valuation bn} (h : Rel q v) (O : Finset bn.V)
    (o : bn.Assignment) : Rel (qcondition O o q) (DVE.Valuation.condition O o v) := by
  refine ⟨?_, fun x => h.2.1 _, fun x => h.2.2 _⟩
  change q.scope \ O = v.scope \ O
  rw [h.1]

theorem udep_condition {q : QVal bn} (hu : UDep q) (O : Finset bn.V) (o : bn.Assignment) :
    UDep (qcondition O o q) := by
  intro x y hxy
  apply hu
  intro w hw
  by_cases hwO : w ∈ O
  · simp [clamp, hwO]
  · simp only [clamp, hwO, if_false]
    exact hxy w (Finset.mem_sdiff.2 ⟨hw, hwO⟩)

end Condition

/-! ## The certificate's evidence -/

variable (r : Diagram) (h : r.Valid) (c : Certificate)

/-- The observed variables of the certificate's hard rows. -/
def certObserved : Finset (Fin r.nv) :=
  (c.hard.filterMap fun e => if hv : e.var < r.nv then some ⟨e.var, hv⟩ else none).toFinset

/-- The observed states of the certificate's hard rows (state `0` off the observed variables). -/
def certObservedValue : (r.compile h).Assignment := fun v =>
  match c.hard.find? (fun e => decide (e.var = v.val)) with
  | some e => if hk : e.stateIndex < r.stateCount v then ⟨e.stateIndex, hk⟩
    else ⟨0, h.nonempty_states v⟩
  | none => ⟨0, h.nonempty_states v⟩

theorem mem_certObserved {v : Fin r.nv} : v ∈ certObserved r c ↔ ∃ e ∈ c.hard, e.var = v.val := by
  unfold certObserved
  rw [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hv⟩
    split_ifs at hv with hlt
    cases hv
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, hev⟩
    refine ⟨e, he, ?_⟩
    rw [dif_pos (hev ▸ v.isLt)]
    exact congrArg some (Fin.ext hev)

/-! ## The run on tables, with skipped variables -/

/-- **The sliced initial tables**: the mechanisms, then the utilities, each conditioned on the
certificate's hard rows. -/
def initCT : List (TVal r) :=
  (List.finRange r.nm).map (fun m => tab r h
      (qcondition (certObserved r c) (certObservedValue r h c) (chanceQ r h c m))) ++
    (List.finRange r.nu).map (fun j => tab r h
      (qcondition (certObserved r c) (certObservedValue r h c) (utilityQ r h c j)))

/-- Julia's chance step on tables: skip a variable that no table mentions. -/
def chanceStepTS (a : Fin r.nv) (ts : List (TVal r)) : List (TVal r) :=
  if bucketT r a ts = [] then ts else chanceStepT r h a ts

/-- **The run on tables, with skipped variables.** -/
def runST : {R : Finset (Fin r.nv)} → DVE.Plan (r.compile h) R → List (TVal r) → List (TVal r)
  | _, .done, ts => ts
  | _, .chance v _ _ next, ts => runST next (chanceStepTS r h v ts)
  | _, .decision d _ _ next, ts => runST next (decisionStepT r h (r.decisions d).action ts)

/-- The representative choice of the run with skipped variables. -/
def keepOfST : {R : Finset (Fin r.nv)} → DVE.Plan (r.compile h) R → List (TVal r) →
    Fin r.nv → Bool
  | _, .done, _ => fun _ => false
  | _, .chance v _ _ next, ts =>
    Function.update (keepOfST next (chanceStepTS r h v ts)) v
      (decide (v ∉ (bucketQ r h v ts).uvars))
  | _, .decision d _ _ next, ts => keepOfST next (decisionStepT r h (r.decisions d).action ts)

/-- The score row the run with skipped variables maximizes for `d`. -/
def scoreST : {R : Finset (Fin r.nv)} → DVE.Plan (r.compile h) R → List (TVal r) →
    (d : Fin r.nd) → (r.compile h).Assignment →
      Fin (r.stateCount (r.decisions d).action) → ℚ
  | _, .done, _, _ => fun _ _ => 0
  | _, .chance v _ _ next, ts, d => scoreST next (chanceStepTS r h v ts) d
  | _, .decision d' _ _ next, ts, d =>
    if d' = d then fun x b =>
      (bucketQ r h (r.decisions d).action ts).util
        (Function.update x (r.decisions d).action b)
    else scoreST next (decisionStepT r h (r.decisions d').action ts) d

/-- The value of the run with skipped variables. -/
def valueST {R : Finset (Fin r.nv)} (plan : DVE.Plan (r.compile h) R) (ts : List (TVal r)) : ℚ :=
  (qcollect ((runST r h plan ts).map (view r h))).util (zeroAssignment r h)

/-- The final mass of the run with skipped variables: Julia's `evidence_probability`. -/
def massST {R : Finset (Fin r.nv)} (plan : DVE.Plan (r.compile h) R) (ts : List (TVal r)) : ℚ :=
  (qcollect ((runST r h plan ts).map (view r h))).prob (zeroAssignment r h)

/-- The bucket of `d`'s action when the run with skipped variables eliminates it. -/
def bucketAtS : {R : Finset (Fin r.nv)} → DVE.Plan (r.compile h) R → List (TVal r) → Fin r.nd →
    Option (List (TVal r))
  | _, .done, _, _ => none
  | _, .chance v _ _ next, ts, d => bucketAtS next (chanceStepTS r h v ts) d
  | _, .decision d' _ _ next, ts, d =>
    if d' = d then some (bucketT r (r.decisions d).action ts)
    else bucketAtS next (decisionStepT r h (r.decisions d').action ts) d

theorem scoreST_of_bucketAtS {R : Finset (r.compile h).V} (plan : DVE.Plan (r.compile h) R)
    (ts : List (TVal r)) (d : Fin r.nd) (B : List (TVal r))
    (hB : bucketAtS r h plan ts d = some B) (x : (r.compile h).Assignment)
    (b : Fin (r.stateCount (r.decisions d).action)) :
    scoreST r h plan ts d x b =
      (qcollect (B.map (view r h))).util (Function.update x (r.decisions d).action b) := by
  induction plan generalizing ts with
  | done => simp [bucketAtS] at hB
  | @chance R v hv hc next ih => exact ih _ hB
  | @decision R d' hd hi next ih =>
    simp only [bucketAtS] at hB
    simp only [scoreST]
    by_cases hdd : d' = d
    · subst hdd
      rw [if_pos rfl] at hB ⊢
      cases hB
      rfl
    · rw [if_neg hdd] at hB ⊢
      exact ih _ hB

/-! ## Putting the observed variables back into the order -/

/-- Julia's recorded order omits the observed variables. Each one is put just before the first
decision of the order whose information set does not contain it, or at the end. -/
def withObserved : List (Fin r.nv) → List (Fin r.nv) → List (Fin r.nv)
  | pending, [] => pending
  | pending, v :: vs =>
    match (List.finRange r.nd).find? (fun d => decide ((r.decisions d).action = v)) with
    | some d => pending.filter (fun o => decide (o ∉ (r.compile h).info d)) ++
        v :: withObserved (pending.filter fun o => decide (o ∈ (r.compile h).info d)) vs
    | none => v :: withObserved pending vs

/-! ## Simulation -/

theorem Sim.bucket_nil_iff {ts : List (TVal r)}
    {vs : List (DVE.Valuation (r.compile h).toFinBayesNet)} (hs : Sim r h ts vs) (a : Fin r.nv) :
    bucketT r a ts = [] ↔ DVE.Valuation.bucket a vs = [] := by
  obtain ⟨⟨ws, hperm, hf⟩, -⟩ := hs
  have hfB : List.Forall₂ (fun t v => Rel (view r h t) v) (bucketT r a ts)
      (DVE.Valuation.bucket a ws) :=
    forall₂_filter hf fun t v hr => by
      change decide (a ∈ (view r h t).scope) = _
      rw [hr.1]
  have h1 := hfB.length_eq
  have h2 : (DVE.Valuation.bucket a ws).length = (DVE.Valuation.bucket a vs).length :=
    (hperm.filter _).length_eq
  rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff (l := DVE.Valuation.bucket a vs), h1, h2]

theorem Sim.chanceSkip {R : Finset (r.compile h).V} {ts : List (TVal r)}
    {s : DVE.State (r.compile h) R} (hs : Sim r h ts s.valuations) (a : Fin r.nv)
    (keep : Fin r.nv → Bool) (hk : keep a = decide (a ∉ (bucketQ r h a ts).uvars)) :
    Sim r h (chanceStepTS r h a ts) (s.chanceRepSkip keep a).valuations := by
  by_cases hnil : bucketT r a ts = []
  · have hnil' := (hs.bucket_nil_iff r h a).1 hnil
    rw [DVE.State.chanceRepSkip_of_nil keep a s hnil']
    unfold chanceStepTS
    rw [if_pos hnil]
    exact hs
  · have hne : DVE.Valuation.bucket a s.valuations ≠ [] :=
      fun h' => hnil ((hs.bucket_nil_iff r h a).2 h')
    rw [DVE.State.chanceRepSkip_of_ne keep a s hne]
    unfold chanceStepTS
    rw [if_neg hnil]
    exact hs.chance r h a (keep a) hk

/-- **The simulation theorem with skipped variables.** -/
theorem sim_runRepSkip {R : Finset (r.compile h).V} (plan : DVE.Plan (r.compile h) R)
    (s : DVE.State (r.compile h) R) (ts : List (TVal r)) (keep : Fin r.nv → Bool)
    (hs : Sim r h ts s.valuations) (hk : ∀ v ∈ R, keep v = keepOfST r h plan ts v) :
    Sim r h (runST r h plan ts) (DVE.runRepSkipState keep plan s).valuations ∧
      ∀ (d : Fin r.nd) x b, DVE.decisionScoreRepSkip keep plan s d x b =
        (scoreST r h plan ts d x b : ℝ) := by
  induction plan generalizing ts with
  | done => exact ⟨hs, fun _ _ _ => by simp [DVE.decisionScoreRepSkip, scoreST]⟩
  | @chance R v hv hc next ih =>
    have hkv : keep v = decide (v ∉ (bucketQ r h v ts).uvars) := by
      rw [hk v hv]
      simp only [keepOfST, Function.update_self]
    have hs' := hs.chanceSkip r h v keep hkv
    have hk' : ∀ w ∈ R.erase v, keep w = keepOfST r h next (chanceStepTS r h v ts) w := by
      intro w hw
      rw [hk w (Finset.mem_of_mem_erase hw)]
      simp only [keepOfST]
      exact Function.update_of_ne (Finset.ne_of_mem_erase hw) _ _
    exact ih (s.chanceRepSkip keep v) (chanceStepTS r h v ts) hs' hk'
  | @decision R d' hd hi next ih =>
    have hs' := hs.decision r h (r.decisions d').action
    have hk' : ∀ w ∈ R.erase ((r.compile h).action d'),
        keep w = keepOfST r h next (decisionStepT r h (r.decisions d').action ts) w := by
      intro w hw
      rw [hk w (Finset.mem_of_mem_erase hw)]
      rfl
    obtain ⟨hrun, hscore⟩ := ih (s.decision d') (decisionStepT r h (r.decisions d').action ts)
      hs' hk'
    refine ⟨hrun, fun d x b => ?_⟩
    simp only [DVE.decisionScoreRepSkip, scoreST]
    by_cases hdd : d' = d
    · subst hdd
      rw [if_pos rfl, if_pos rfl]
      exact (hs.bucket r h _).1.2.2 _
    · rw [if_neg hdd, if_neg hdd]
      exact hscore d x b

theorem sim_initialC (hm : Matches r c) (hn : Nonneg c) :
    Sim r h (initCT r h c) (DVE.initialConditioned (certKernel r h c) (certKernel_local hm h)
      (certKernel_nonneg hn h) (certUtility r h c) (certUtility_local hm h) (certObserved r c)
      (certObservedValue r h c)).valuations := by
  set O := certObserved r c
  set o := certObservedValue r h c
  have hrc : ∀ m, Rel (qcondition O o (chanceQ r h c m))
      (DVE.Valuation.condition O o (DVE.chanceValuation (certKernel r h c) (certKernel_local hm h)
        (certKernel_nonneg hn h) m)) := fun m =>
    rel_condition ⟨rfl, fun x => certKernel_eq_cast r h c m x _,
      fun x => by simp [chanceQ, DVE.chanceValuation]⟩ O o
  have hru : ∀ j, Rel (qcondition O o (utilityQ r h c j))
      (DVE.Valuation.condition O o (DVE.utilityValuation (certUtility r h c)
        (certUtility_local hm h) j)) := fun j =>
    rel_condition ⟨rfl, fun x => by simp [utilityQ, DVE.utilityValuation],
      fun x => certUtility_eq_cast r h c j x⟩ O o
  have hud : ∀ j, UDep (qcondition O o (utilityQ r h c j)) := by
    intro j
    apply udep_condition
    have hr : Rel (utilityQ r h c j) (DVE.utilityValuation (certUtility r h c)
        (certUtility_local hm h) j) :=
      ⟨rfl, fun x => by simp [utilityQ, DVE.utilityValuation],
        fun x => certUtility_eq_cast r h c j x⟩
    exact hr.depUtil
  refine ⟨⟨((List.finRange r.nm).map (DVE.chanceValuation (certKernel r h c)
      (certKernel_local hm h) (certKernel_nonneg hn h)) ++
    (List.finRange r.nu).map (DVE.utilityValuation (certUtility r h c)
      (certUtility_local hm h))).map (DVE.Valuation.condition O o), ?_, ?_⟩, ?_⟩
  · exact (List.Perm.append ((finRange_perm_toList r.nm).map _)
      ((finRange_perm_toList r.nu).map _)).map _
  · rw [List.map_append]
    refine List.rel_append ?_ ?_
    · rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro m _
      rw [view_tab r h _ (hrc m).depProb (hrc m).depUtil]
      exact hrc m
    · rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro j _
      rw [view_tab r h _ (hru j).depProb (hru j).depUtil]
      exact hru j
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 ht
      rw [view_tab r h _ (hrc m).depProb (hrc m).depUtil]
      exact udep_condition (q := chanceQ r h c m) (fun _ _ _ => rfl) O o
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
      rw [view_tab r h _ (hru j).depProb (hru j).depUtil]
      exact hud j

/-- **The exact run with hard evidence is computed.** For a certificate that matches the checked
diagram and has nonnegative cells, and for any plan, Julia's evidence run on the sliced data with
`keep := keepOfST plan` (Julia's `sum_out` branch) and any selector has the value `valueST`, the
score rows `scoreST` and the final mass `massST`, read in `ℝ`. -/
theorem exactRunC_spec (hm : Matches r c) (hn : Nonneg c) (sel : DVE.Selector (r.compile h))
    (plan : DVE.Plan (r.compile h) Finset.univ) :
    (DVE.solveCondRepPlanWith sel (keepOfST r h plan (initCT r h c)) (certKernel r h c)
        (certKernel_local hm h) (certKernel_nonneg hn h) (certUtility r h c)
        (certUtility_local hm h) (certObserved r c) (certObservedValue r h c) plan).value =
        (valueST r h plan (initCT r h c) : ℝ) ∧
      (∀ (d : Fin r.nd) x b, DVE.solveCondRepPlanScore (keepOfST r h plan (initCT r h c))
          (certKernel r h c) (certKernel_local hm h) (certKernel_nonneg hn h)
          (certUtility r h c) (certUtility_local hm h) (certObserved r c)
          (certObservedValue r h c) plan d x b =
        (scoreST r h plan (initCT r h c) d x b : ℝ)) ∧
      DVE.solveCondRepPlanMass (keepOfST r h plan (initCT r h c)) (certKernel r h c)
          (certKernel_local hm h) (certKernel_nonneg hn h) (certUtility r h c)
          (certUtility_local hm h) (certObserved r c) (certObservedValue r h c) plan =
        (massST r h plan (initCT r h c) : ℝ) := by
  obtain ⟨hsim, hscore⟩ := sim_runRepSkip r h plan _ (initCT r h c)
    (keepOfST r h plan (initCT r h c)) (sim_initialC r h c hm hn) (fun _ _ => rfl)
  obtain ⟨⟨ws, hperm, hf⟩, -⟩ := hsim
  have hrel := rel_collect (List.forall₂_map_left_iff.2 hf)
  rw [collect_perm hperm] at hrel
  have hempty : ∀ w ∈ (DVE.Valuation.collect (DVE.runRepSkipState
      (keepOfST r h plan (initCT r h c)) plan (DVE.initialConditioned (certKernel r h c)
        (certKernel_local hm h) (certKernel_nonneg hn h) (certUtility r h c)
        (certUtility_local hm h) (certObserved r c) (certObservedValue r h c))).valuations).scope,
      DVE.baseAssignment (r.compile h) w = zeroAssignment r h w := by
    intro w hw
    have := (DVE.runRepSkipState (keepOfST r h plan (initCT r h c)) plan
      (DVE.initialConditioned (certKernel r h c) (certKernel_local hm h)
        (certKernel_nonneg hn h) (certUtility r h c) (certUtility_local hm h) (certObserved r c)
        (certObservedValue r h c))).supported hw
    simp at this
  refine ⟨?_, hscore, ?_⟩
  · rw [DVE.solveCondRepPlanWith_value]
    unfold valueST
    rw [← hrel.2.2]
    exact DVE.Valuation.util_local _ _ _ hempty
  · unfold DVE.solveCondRepPlanMass massST
    rw [← hrel.2.1]
    exact DVE.Valuation.prob_local _ _ _ hempty

/-! ## The certificate's hard evidence -/

/-- **The certificate's hard rows as hard evidence of the compiled diagram.** The ancestral set
is every variable before every action in the certificate's `topological_order`: closed under
causal parents (`Arc`), free of actions, and containing every evidence variable, which
`certificateMatches` puts before every action (`EvidenceArc`). -/
def certHardEvidence (hm : Matches r c) (hf : r.FullValid) :
    DVE.HardEvidence (r.compile hf.valid) where
  ancestors := Finset.univ.filter fun w => ∀ d : Fin r.nd,
    (certOrder hm hf).order.idxOf w < (certOrder hm hf).order.idxOf ((r.compile hf.valid).action d)
  observed := certObserved r c
  sub := by
    intro v hv
    obtain ⟨e, he, hev⟩ := (mem_certObserved r c).1 hv
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun d => ?_⟩
    have hne : v ≠ (r.compile hf.valid).action d := fun hvd =>
      (hm.evidence_range e he).2 d (by rw [hev, hvd])
    apply DVE.idxOf_lt_of_no_reverse (certOrder hm hf).order ((certOrder hm hf).complete v)
      ((certOrder hm hf).complete _) hne
    refine (List.pairwise_pmap _).2 (hm.topo_order.imp fun {a b} hab ha hb hx hy => ?_)
    apply hab.2
    exact ⟨⟨e, he, by rw [hev]; exact (congrArg Fin.val hy).symm⟩, d,
      (congrArg Fin.val hx).symm⟩
  closed := by
    intro m hmt p hp
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun d => ?_⟩
    exact lt_trans ((DVE.RankedOrder.ofOrder (certOrder hm hf)).parents_lt m p hp)
      ((Finset.mem_filter.1 hmt).2 d)
  no_action := by
    intro d hd
    exact lt_irrefl _ ((Finset.mem_filter.1 hd).2 d)
  value := certObservedValue r hf.valid c

end InfluenceDiagramsProofs.DVECertificate
