import InfluenceDiagramsProofs.Finite.DVE.SolutionCheck

/-!
# SA-Pass shadow module: Julia's recorded solution is the exact run's

Claim `id.recorded-solution-optimal`, from `DVECertificate.recorded_solution_optimal`:
"`recorded_solution_optimal` proves that if a version-2 certificate matches, its CPT cells are
nonnegative, its solution is well formed and `solutionMatches` holds, then Julia's elimination
order is a plan and, for that plan and the representative choice `keepOfT`, Julia's recorded
strategy is the strategy of the exact DVE run on the certificate's numbers and the recorded
value is that run's value; on every information row the recorded action is the action of least
`state_position` among the maximizers of the run's own score; and if every CPT row sums to
exactly one, the recorded strategy is deterministic and optimal and the recorded value is the
optimum."

"The certificate matches", "nonnegative", "well formed" and "`solutionMatches` holds" are
`certificateMatches r h c`, `Nonneg c`, `s.WellFormed c` and `solutionMatches r h.valid c s =
true`; "the exact DVE run on the certificate's numbers" is `DVE.solveRepPlanWith (r.selector
h.valid) keep` on `certKernel` / `certUtility`, with `keep := keepOfT r h.valid plan (initT r
h.valid c)`; "Julia's elimination order is a plan" is `solutionPlan r h.valid s = some plan`, the
plan of `s.eliminationOrder`; "Julia's recorded
strategy" is `recordedStrategy r h.valid c s` and "the recorded action" `recordedAction`; "the
run's own score" is `DVE.solveRepPlanScore` of the same run; "every CPT row sums to exactly one"
is `ExactNormalised r c`; "optimal" and "the optimum" are `expectedUtility … = optimalValue …`.
The first shadow is the statement about the run (one plan, so the three statements are about the
same run); the next three split the exactly normalised case.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.RecordedSolution

open InfluenceDiagramsProofs FinInfluenceDiagram InfluenceDiagramsProofs.Records
open InfluenceDiagramsProofs.DVECertificate

/-- The exact representative DVE run on the certificate's numbers. -/
noncomputable abbrev Sol (r : Diagram) (h : r.FullValid) (c : Certificate)
    (hm : certificateMatches r h c) (hn : Nonneg c) (keep : (r.compile h.valid).V → Bool)
    (plan : DVE.Plan (r.compile h.valid) Finset.univ) :=
  DVE.solveRepPlanWith (r.selector h.valid) keep (certKernel r h.valid c)
    (certKernel_local hm h.valid) (certKernel_nonneg hn h.valid) (certUtility r h.valid c)
    (certUtility_local hm h.valid) plan

/-- The run's own score rows. -/
noncomputable abbrev Score (r : Diagram) (h : r.FullValid) (c : Certificate)
    (hm : certificateMatches r h c) (hn : Nonneg c) (keep : (r.compile h.valid).V → Bool)
    (plan : DVE.Plan (r.compile h.valid) Finset.univ) :=
  DVE.solveRepPlanScore keep (certKernel r h.valid c) (certKernel_local hm h.valid)
    (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid) plan

/-- The hypotheses, abstracted: a statement `P`, for every matching certificate and solution. -/
abbrev ForAll (P : ∀ (r : Diagram) (h : r.FullValid) (c : Certificate) (_ : Solution),
    certificateMatches r h c → Nonneg c → Prop) : Prop :=
  ∀ (r : Diagram) (h : r.FullValid) (c : Certificate) (s : Solution)
    (hm : certificateMatches r h c) (hn : Nonneg c), s.WellFormed c →
    solutionMatches r h.valid c s = true → P r h c s hm hn

/-- "Julia's elimination order is a plan and, for that plan and the representative choice
`keepOfT`, Julia's recorded strategy is the strategy of the exact DVE run … and the recorded value
is that run's value; on every information row the recorded action is the action of least
`state_position` among the maximizers of the run's own score". -/
abbrev Shadow1 : Prop := ForAll fun r h c s hm hn =>
  ∃ plan : DVE.Plan (r.compile h.valid) Finset.univ, solutionPlan r h.valid s = some plan ∧
    let keep := keepOfT r h.valid plan (initT r h.valid c)
    recordedStrategy r h.valid c s = (Sol r h c hm hn keep plan).strategy ∧
      (s.value.toRat : ℝ) = (Sol r h c hm hn keep plan).value ∧
      ∀ (d : (r.compile h.valid).D) (x : (r.compile h.valid).Assignment),
        (∀ b, Score r h c hm hn keep plan d x b ≤
          Score r h c hm hn keep plan d x (recordedAction r h.valid c s d x)) ∧
        ∀ b, (∀ c', Score r h c hm hn keep plan d x c' ≤ Score r h c hm hn keep plan d x b) →
          r.statePosition h.valid _ (recordedAction r h.valid c s d x) ≤
            r.statePosition h.valid _ b

/-- "if every CPT row sums to exactly one, the recorded strategy is deterministic". -/
abbrev Shadow2 : Prop := ForAll fun r h c s _ _ =>
  ExactNormalised r c → (recordedStrategy r h.valid c s).Deterministic

/-- "… and optimal". -/
abbrev Shadow3 : Prop := ForAll fun r h c s _ _ =>
  ExactNormalised r c →
    expectedUtility (certKernel r h.valid c) (recordedStrategy r h.valid c s)
      (certUtility r h.valid c) = optimalValue (certKernel r h.valid c) (certUtility r h.valid c)

/-- "… and the recorded value is the optimum". -/
abbrev Shadow4 : Prop := ForAll fun r h c s _ _ =>
  ExactNormalised r c →
    (s.value.toRat : ℝ) = optimalValue (certKernel r h.valid c) (certUtility r h.valid c)

/-- The cited theorem, restated abstractly. -/
abbrev Candidate : Prop := ForAll fun r h c s hm hn =>
  (∃ plan : DVE.Plan (r.compile h.valid) Finset.univ, solutionPlan r h.valid s = some plan ∧
    let keep := keepOfT r h.valid plan (initT r h.valid c)
    recordedStrategy r h.valid c s = (Sol r h c hm hn keep plan).strategy ∧
      (s.value.toRat : ℝ) = (Sol r h c hm hn keep plan).value ∧
      ∀ (d : (r.compile h.valid).D) (x : (r.compile h.valid).Assignment),
        (∀ b, Score r h c hm hn keep plan d x b ≤
          Score r h c hm hn keep plan d x (recordedAction r h.valid c s d x)) ∧
        ∀ b, (∀ c', Score r h c hm hn keep plan d x c' ≤ Score r h c hm hn keep plan d x b) →
          r.statePosition h.valid _ (recordedAction r h.valid c s d x) ≤
            r.statePosition h.valid _ b) ∧
  (ExactNormalised r c →
    (recordedStrategy r h.valid c s).Deterministic ∧
      expectedUtility (certKernel r h.valid c) (recordedStrategy r h.valid c s)
        (certUtility r h.valid c) = optimalValue (certKernel r h.valid c) (certUtility r h.valid c) ∧
      (s.value.toRat : ℝ) = optimalValue (certKernel r h.valid c) (certUtility r h.valid c))

theorem forward1 : Candidate → Shadow1 :=
  fun H r h c s hm hn hs hsm => (H r h c s hm hn hs hsm).1

theorem forward2 : Candidate → Shadow2 :=
  fun H r h c s hm hn hs hsm hex => ((H r h c s hm hn hs hsm).2 hex).1

theorem forward3 : Candidate → Shadow3 :=
  fun H r h c s hm hn hs hsm hex => ((H r h c s hm hn hs hsm).2 hex).2.1

theorem forward4 : Candidate → Shadow4 :=
  fun H r h c s hm hn hs hsm hex => ((H r h c s hm hn hs hsm).2 hex).2.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Candidate :=
  fun s1 s2 s3 s4 r h c s hm hn hs hsm =>
    ⟨s1 r h c s hm hn hs hsm, fun hex =>
      ⟨s2 r h c s hm hn hs hsm hex, s3 r h c s hm hn hs hsm hex, s4 r h c s hm hn hs hsm hex⟩⟩

/-- SA-Pass anchor: `recorded_solution_optimal` proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ h _ _ hm hn hs hsm =>
  recorded_solution_optimal h hm hn hs hsm

end InfluenceDiagramsProofs.Shadows.RecordedSolution
