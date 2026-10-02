import InfluenceDiagramsProofs.Finite.DVE.SolutionCheck

/-!
# SA-Pass shadow module: a recorded binary64 solution is near-optimal at near-ties

Claim `id.recorded-binary64-near-optimal`, from `DVECertificate.recorded_binary64_near_optimal`:
"`recorded_binary64_near_optimal` proves that if a version-2 certificate matches, its CPT cells
are nonnegative, its solution is well formed, `solutionWithin τ τv` holds and
`certificateEpsilon c < 1`, then Julia's recorded strategy is deterministic, its expected
utility under the row-normalised model is within `2 e + nd * τ` of that model's optimum and of
every nonnegative strategy, where `nd` is the number of decisions, and the recorded value is
within `τv + e` of that optimum, whether or not the recorded actions agree with the exact run's."

"The certificate matches", "nonnegative", "well formed", "`solutionWithin τ τv` holds" and
"`certificateEpsilon c < 1`" are `certificateMatches r h c`, `Nonneg c`, `s.WellFormed c`,
`solutionWithin r h.valid c s τ τv = true` and `certificateEpsilon c < 1`; "Julia's recorded
strategy" is `recordedStrategy r h.valid c s`; "the row-normalised model" is `certNormKernel`;
`e` is `approxError (certificateEpsilon c) (certChanceCount c) (certUmax c)` (the `e` of
`certificate_approx_optimal`) and `nd` is `r.nd`. "Within `2 e + nd * τ` of that model's
optimum" is the two-sided bracket `optimalValue - 2 e - nd τ ≤ EU ≤ optimalValue`; "of every
nonnegative strategy" is `EU τ' ≤ EU recorded + 2 e + nd τ`; "the recorded value is within
`τv + e`" is `|value - optimalValue| ≤ τv + e`. "Whether or not the recorded actions agree" is
the absence of an `actionsAgree` hypothesis. The shadows split the five conclusions.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.RecordedNearOptimal

open InfluenceDiagramsProofs FinInfluenceDiagram InfluenceDiagramsProofs.Records
open InfluenceDiagramsProofs.DVECertificate

/-- The reference expected utility (row-normalised model). -/
noncomputable abbrev EU (r : Diagram) (h : r.FullValid) (c : Certificate)
    (σ : Strategy (r.compile h.valid) ℝ) : ℝ :=
  expectedUtility (certNormKernel r h.valid c) σ (certUtility r h.valid c)

/-- The reference optimum. -/
noncomputable abbrev Opt (r : Diagram) (h : r.FullValid) (c : Certificate) : ℝ :=
  optimalValue (certNormKernel r h.valid c) (certUtility r h.valid c)

/-- `e`. -/
noncomputable abbrev E (c : Certificate) : ℝ :=
  approxError (certificateEpsilon c) (certChanceCount c) (certUmax c)

/-- The hypotheses, abstracted: a statement `P`, for every matching certificate, every well-formed
solution passing the binary64 comparison and every pair of tolerances. -/
abbrev ForAll (P : ∀ (r : Diagram) (_ : r.FullValid) (_ : Certificate) (_ : Solution) (_ _ : ℚ),
    Prop) : Prop :=
  ∀ (r : Diagram) (h : r.FullValid) (c : Certificate) (s : Solution),
    certificateMatches r h c → Nonneg c → s.WellFormed c → ∀ τ τv : ℚ,
    solutionWithin r h.valid c s τ τv = true → certificateEpsilon c < 1 → P r h c s τ τv

/-- The cited theorem, restated abstractly. -/
abbrev Candidate : Prop := ForAll fun r h c s τ τv =>
  (recordedStrategy r h.valid c s).Deterministic ∧
    (∀ τ' : Strategy (r.compile h.valid) ℝ, τ'.Nonneg →
      EU r h c τ' ≤ EU r h c (recordedStrategy r h.valid c s) + 2 * E c + r.nd * (τ : ℝ)) ∧
    Opt r h c - 2 * E c - r.nd * (τ : ℝ) ≤ EU r h c (recordedStrategy r h.valid c s) ∧
    EU r h c (recordedStrategy r h.valid c s) ≤ Opt r h c ∧
    |(s.value.toRat : ℝ) - Opt r h c| ≤ τv + E c

/-- "Julia's recorded strategy is deterministic". -/
abbrev Shadow1 : Prop := ForAll fun r h c s _ _ => (recordedStrategy r h.valid c s).Deterministic

/-- "within `2 e + nd * τ` … of every nonnegative strategy". -/
abbrev Shadow2 : Prop := ForAll fun r h c s τ _ =>
  ∀ τ' : Strategy (r.compile h.valid) ℝ, τ'.Nonneg →
    EU r h c τ' ≤ EU r h c (recordedStrategy r h.valid c s) + 2 * E c + r.nd * (τ : ℝ)

/-- "within `2 e + nd * τ` of that model's optimum", from below. -/
abbrev Shadow3 : Prop := ForAll fun r h c s τ _ =>
  Opt r h c - 2 * E c - r.nd * (τ : ℝ) ≤ EU r h c (recordedStrategy r h.valid c s)

/-- "within … of that model's optimum", from above. -/
abbrev Shadow4 : Prop := ForAll fun r h c s _ _ =>
  EU r h c (recordedStrategy r h.valid c s) ≤ Opt r h c

/-- "the recorded value is within `τv + e` of that optimum". -/
abbrev Shadow5 : Prop := ForAll fun r h c s _ τv =>
  |(s.value.toRat : ℝ) - Opt r h c| ≤ τv + E c

theorem forward1 : Candidate → Shadow1 :=
  fun H r h c s hm hn hs τ τv hw hε => (H r h c s hm hn hs τ τv hw hε).1

theorem forward2 : Candidate → Shadow2 :=
  fun H r h c s hm hn hs τ τv hw hε => (H r h c s hm hn hs τ τv hw hε).2.1

theorem forward3 : Candidate → Shadow3 :=
  fun H r h c s hm hn hs τ τv hw hε => (H r h c s hm hn hs τ τv hw hε).2.2.1

theorem forward4 : Candidate → Shadow4 :=
  fun H r h c s hm hn hs τ τv hw hε => (H r h c s hm hn hs τ τv hw hε).2.2.2.1

theorem forward5 : Candidate → Shadow5 :=
  fun H r h c s hm hn hs τ τv hw hε => (H r h c s hm hn hs τ τv hw hε).2.2.2.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Shadow5 → Candidate :=
  fun s1 s2 s3 s4 s5 r h c s hm hn hs τ τv hw hε =>
    ⟨s1 r h c s hm hn hs τ τv hw hε, s2 r h c s hm hn hs τ τv hw hε,
      s3 r h c s hm hn hs τ τv hw hε, s4 r h c s hm hn hs τ τv hw hε,
      s5 r h c s hm hn hs τ τv hw hε⟩

/-- SA-Pass anchor: `recorded_binary64_near_optimal` proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ h _ _ hm hn hs _ _ hw hε =>
  recorded_binary64_near_optimal h hm hn hs hw hε

end InfluenceDiagramsProofs.Shadows.RecordedNearOptimal
