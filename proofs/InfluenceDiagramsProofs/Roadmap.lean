import InfluenceDiagramsProofs.Finite.DVE.Evidence

/-!
# Roadmap and exact scope of the DVE theorem

The global optimum-existence result is now supplemented by an actual bucket solver:
`DVE.solve_spec` proves its deterministic policies realize the reported value and attain
the existing optimum. `NoForgettingOrder.plan` constructs its strong order from a complete
perfect-recall decision list. No semantic legality trace is assumed. Probability independence
is derived from the original finite diagram's topological order and kernel normalisation.

`DVE.solveEvidence_spec` and `DVE.solveEvidence_eq_optimal` extend this to likelihoods on an
action-free chance-ancestral set, with explicitly positive evidence mass.
`solveEvidenceChecked_eq` checks the driver-computed mass and rejects zero mass.

The formerly separate all-row diagnostic obligation is now closed:
`all_guards_complete` and `all_guards_complete_evidence` prove every bucket probability is
action-independent on **every** row, including zero outside probability. The checked driver
uses the source-style maximum of row maximum-minus-minimum at exact zero tolerance.
`solveGuarded_eq` returns the same verified optimum; `solveEvidenceGuarded_none_iff` shows
that the only remaining rejection for supported evidence is zero total evidence mass.
No strict-positivity premise was added: positive normalized smoothing is only a proof device,
and probability-expression continuity transfers the identities to zero.

This is **not** a byte-for-byte verification of Julia. Remaining refinements are:

* ordered arrays, state labels, reference resolution and the concrete min-fill scheduler;
* arbitrary finite local argmax ties versus Julia's first-label tie rule (the proved
  equivalence is realized optimal value, not identical policy tables or joint laws);
* explicit evidence conditioning versus a likelihood-factor representation, and
  zero-probability utility-table representatives (weighted valuations agree);
* Float64/tolerance behavior. Small action-dependent evidence probabilities can pass the
  source's tolerance guard and yield a wrong reported value; they are outside the theorem's
  action-independent evidence contract.

`Finite/OrderedPolicies.lean` now supplies an exact first-state local selector, an information
table reconstruction theorem and a strict-gap numerical stability contract. This does not
silently rewrite the existing DVE driver's selector or establish full first-label array
identity. The BN proof dependency now includes concrete checked records/references, repeated
slots, conditioned distributions, collect/distribute message correctness, moralized-ancestral
d-separation soundness and conditional numerical error bounds.

The implementation-facing boundaries above must accompany any claim of Proposition 7.
There are no unproved Lean declarations in this module.
-/
