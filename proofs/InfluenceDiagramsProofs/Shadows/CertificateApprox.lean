import InfluenceDiagramsProofs.Finite.DVE.CertificateApprox

/-!
# SA-Pass shadow module: approximate optimality on a certificate

Claim `id.certificate-approx-optimal`, from `DVECertificate.certificate_approx_optimal`:
"`certificate_approx_optimal` proves that if the certificate matches, its CPT cells are
nonnegative and `certificateEpsilon c < 1`, the exact DVE run on the certificate's numbers, with
any maximizing selector, representative choice and plan, returns a deterministic strategy whose
expected utility under the row-normalised model is within `2 e` of that model's optimum and of
every nonnegative strategy, and whose value is within `e` of that optimum, where
`e = n (((1 + ε) / (1 - ε)) ^ n - 1) Umax`."

"The certificate matches", "nonnegative" and "`certificateEpsilon c < 1`" are
`certificateMatches r h c`, `Nonneg c` and `certificateEpsilon c < 1`; "the exact DVE run on the
certificate's numbers" is `DVE.solveRepPlanWith sel keep` on `certKernel` / `certUtility`, for
every selector `sel`, representative choice `keep` and plan; "the row-normalised model" is
`certNormKernel`; `e` is `approxError (certificateEpsilon c) (certChanceCount c) (certUmax c)`,
whose definition is `n (((1 + ε) / (1 - ε)) ^ n - 1) U`. "Within `2 e` of that model's optimum"
is the two-sided bracket `optimalValue - 2 e ≤ EU ≤ optimalValue`; "within `2 e` of every
nonnegative strategy" is `EU τ ≤ EU σ* + 2 e`. The shadows split the five conclusions.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.CertificateApprox

open InfluenceDiagramsProofs FinInfluenceDiagram InfluenceDiagramsProofs.Records
open InfluenceDiagramsProofs.DVECertificate

/-- The exact representative DVE run on the certificate's numbers. -/
noncomputable abbrev Sol (r : Diagram) (h : r.FullValid) (c : Certificate)
    (hm : certificateMatches r h c) (hn : Nonneg c) (sel : DVE.Selector (r.compile h.valid))
    (keep : (r.compile h.valid).V → Bool) (plan : DVE.Plan (r.compile h.valid) Finset.univ) :=
  DVE.solveRepPlanWith sel keep (certKernel r h.valid c) (certKernel_local hm h.valid)
    (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid) plan

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

/-- The hypotheses, abstracted: a statement `P` about the run, for every certificate. -/
abbrev ForAll (P : ∀ (r : Diagram) (h : r.FullValid) (c : Certificate),
    certificateMatches r h c → Nonneg c → DVE.Selector (r.compile h.valid) →
      ((r.compile h.valid).V → Bool) → DVE.Plan (r.compile h.valid) Finset.univ → Prop) : Prop :=
  ∀ (r : Diagram) (h : r.FullValid) (c : Certificate) (hm : certificateMatches r h c)
    (hn : Nonneg c), certificateEpsilon c < 1 →
    ∀ sel keep plan, P r h c hm hn sel keep plan

/-- The cited theorem, restated abstractly. -/
abbrev Candidate : Prop := ForAll fun r h c hm hn sel keep plan =>
  (Sol r h c hm hn sel keep plan).strategy.Deterministic ∧
    (∀ τ : Strategy (r.compile h.valid) ℝ, τ.Nonneg →
      EU r h c τ ≤ EU r h c (Sol r h c hm hn sel keep plan).strategy + 2 * E c) ∧
    Opt r h c - 2 * E c ≤ EU r h c (Sol r h c hm hn sel keep plan).strategy ∧
    EU r h c (Sol r h c hm hn sel keep plan).strategy ≤ Opt r h c ∧
    |(Sol r h c hm hn sel keep plan).value - Opt r h c| ≤ E c

/-- "returns a deterministic strategy". -/
abbrev Shadow1 : Prop := ForAll fun r h c hm hn sel keep plan =>
  (Sol r h c hm hn sel keep plan).strategy.Deterministic

/-- "within `2 e` of every nonnegative strategy". -/
abbrev Shadow2 : Prop := ForAll fun r h c hm hn sel keep plan =>
  ∀ τ : Strategy (r.compile h.valid) ℝ, τ.Nonneg →
    EU r h c τ ≤ EU r h c (Sol r h c hm hn sel keep plan).strategy + 2 * E c

/-- "within `2 e` of that model's optimum", from below. -/
abbrev Shadow3 : Prop := ForAll fun r h c hm hn sel keep plan =>
  Opt r h c - 2 * E c ≤ EU r h c (Sol r h c hm hn sel keep plan).strategy

/-- "within `2 e` of that model's optimum", from above (the optimum is an upper bound). -/
abbrev Shadow4 : Prop := ForAll fun r h c hm hn sel keep plan =>
  EU r h c (Sol r h c hm hn sel keep plan).strategy ≤ Opt r h c

/-- "whose value is within `e` of that optimum". -/
abbrev Shadow5 : Prop := ForAll fun r h c hm hn sel keep plan =>
  |(Sol r h c hm hn sel keep plan).value - Opt r h c| ≤ E c

theorem forward1 : Candidate → Shadow1 :=
  fun H r h c hm hn hε sel keep plan => (H r h c hm hn hε sel keep plan).1

theorem forward2 : Candidate → Shadow2 :=
  fun H r h c hm hn hε sel keep plan => (H r h c hm hn hε sel keep plan).2.1

theorem forward3 : Candidate → Shadow3 :=
  fun H r h c hm hn hε sel keep plan => (H r h c hm hn hε sel keep plan).2.2.1

theorem forward4 : Candidate → Shadow4 :=
  fun H r h c hm hn hε sel keep plan => (H r h c hm hn hε sel keep plan).2.2.2.1

theorem forward5 : Candidate → Shadow5 :=
  fun H r h c hm hn hε sel keep plan => (H r h c hm hn hε sel keep plan).2.2.2.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Shadow5 → Candidate :=
  fun s1 s2 s3 s4 s5 r h c hm hn hε sel keep plan =>
    ⟨s1 r h c hm hn hε sel keep plan, s2 r h c hm hn hε sel keep plan,
      s3 r h c hm hn hε sel keep plan, s4 r h c hm hn hε sel keep plan,
      s5 r h c hm hn hε sel keep plan⟩

/-- SA-Pass anchor: `certificate_approx_optimal` proves `Candidate` as stated. -/
theorem anchor : Candidate := fun r h c hm hn hε sel keep plan =>
  certificate_approx_optimal r h c hm hn hε sel keep plan

end InfluenceDiagramsProofs.Shadows.CertificateApprox
