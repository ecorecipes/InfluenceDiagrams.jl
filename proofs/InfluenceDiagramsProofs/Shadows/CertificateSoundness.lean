import InfluenceDiagramsProofs.Finite.DVE.CertificateCheck

/-!
# SA-Pass shadow module: soundness of the DVE certificate checker

Claim `id.certificate-soundness`, from `DVECertificate.certificate_solve_spec`:
"`certificate_solve_spec` proves that if the certificate matches and its CPT cells are
nonnegative and every CPT row sums to exactly one, the DVE solution scheduled by the
certificate's own `decision_order` is deterministic, realizes its value and attains the optimum
of the model the certificate's exact numbers define."

"The certificate matches" is `certificateMatches r h c` for a fully valid decoded diagram `r`;
"nonnegative" and "sums to exactly one" are `Nonneg c` and `ExactNormalised r c`; "the model the
certificate's exact numbers define" is `certKernel` / `certUtility` on the compiled diagram;
"scheduled by the certificate's own `decision_order`" is `DVE.solve` with `certNoForgetting`
(and `certOrder`); "attains the optimum" is equality with `optimalValue`. The shadows split the
three conclusions.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.CertificateSoundness

open InfluenceDiagramsProofs FinInfluenceDiagram InfluenceDiagramsProofs.Records
open InfluenceDiagramsProofs.DVECertificate

/-- The DVE solution on the certificate's model, scheduled by its own orders. -/
noncomputable abbrev Sol (r : Diagram) (h : r.FullValid) (c : Certificate)
    (hm : certificateMatches r h c) (hn : Nonneg c) :=
  DVE.solve (certKernel r h.valid c) (certKernel_local hm h.valid)
    (certKernel_nonneg hn h.valid) (certUtility r h.valid c) (certUtility_local hm h.valid)
    (certOrder hm h) (certNoForgetting hm h)

/-- The cited theorem, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (r : Diagram) (h : r.FullValid) (c : Certificate) (hm : certificateMatches r h c)
    (hn : Nonneg c), ExactNormalised r c →
    (Sol r h c hm hn).strategy.Deterministic ∧
      expectedUtility (certKernel r h.valid c) (Sol r h c hm hn).strategy
        (certUtility r h.valid c) = (Sol r h c hm hn).value ∧
      (Sol r h c hm hn).value = optimalValue (certKernel r h.valid c) (certUtility r h.valid c)

/-- "is deterministic". -/
abbrev Shadow1 : Prop :=
  ∀ (r : Diagram) (h : r.FullValid) (c : Certificate) (hm : certificateMatches r h c)
    (hn : Nonneg c), ExactNormalised r c → (Sol r h c hm hn).strategy.Deterministic

/-- "realizes its value": the expected utility of the returned strategy is the reported value. -/
abbrev Shadow2 : Prop :=
  ∀ (r : Diagram) (h : r.FullValid) (c : Certificate) (hm : certificateMatches r h c)
    (hn : Nonneg c), ExactNormalised r c →
    expectedUtility (certKernel r h.valid c) (Sol r h c hm hn).strategy (certUtility r h.valid c) =
      (Sol r h c hm hn).value

/-- "attains the optimum of the model the certificate's exact numbers define". -/
abbrev Shadow3 : Prop :=
  ∀ (r : Diagram) (h : r.FullValid) (c : Certificate) (hm : certificateMatches r h c)
    (hn : Nonneg c), ExactNormalised r c →
    (Sol r h c hm hn).value = optimalValue (certKernel r h.valid c) (certUtility r h.valid c)

theorem forward1 : Candidate → Shadow1 := fun h r hv c hm hn hnorm => (h r hv c hm hn hnorm).1

theorem forward2 : Candidate → Shadow2 := fun h r hv c hm hn hnorm => (h r hv c hm hn hnorm).2.1

theorem forward3 : Candidate → Shadow3 := fun h r hv c hm hn hnorm => (h r hv c hm hn hnorm).2.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate :=
  fun s1 s2 s3 r hv c hm hn hnorm =>
    ⟨s1 r hv c hm hn hnorm, s2 r hv c hm hn hnorm, s3 r hv c hm hn hnorm⟩

/-- SA-Pass anchor: `certificate_solve_spec` proves `Candidate` as stated. -/
theorem anchor : Candidate := fun r hv c hm hn hnorm => certificate_solve_spec r hv c hm hn hnorm

end InfluenceDiagramsProofs.Shadows.CertificateSoundness
