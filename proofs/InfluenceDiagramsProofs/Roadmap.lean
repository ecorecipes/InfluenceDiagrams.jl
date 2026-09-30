import InfluenceDiagramsProofs.Finite.DVE.Conditioning

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

`Finite/DVE/Selector.lean` parameterises the bucket driver by its local maximizer without
editing `run` (`runWith_classical`); the computed valuations never depend on the selector.
`solveWith_spec`, `solveGuardedWith_spec`, `solveEvidenceWith_spec` and
`solveEvidenceGuardedWith_eq` give every maximizing selector the guarantees above. For the
least-state selector `Selector.ordered`, `solveOrdered_table` proves that the returned policy is
exactly `orderedTable` of the bucket-utility score on every information row, reachable or not,
and `solveOrdered_semantic` / `solveEvidenceOrdered_semantic` characterize the entry on every
row of positive reach as the least maximizer of a semantic continuation value.

`Finite/DVE/Conditioning.lean` models Julia's evidence path literally for hard evidence on an
action-free chance-ancestral set: every chance and utility valuation is sliced at the observed
states (`Valuation.condition`) and chance variables that no valuation mentions are skipped
(`runSkipWith`). `Coupled` proves that at every stage the sliced valuations at `x` and the
likelihood valuations at `clamp O o x` have equal probability and weighted utility on every
row. Hence `conditionedMass_eq` (the final mass is the evidence mass),
`solveConditioned_spec` (realized conditional optimum, equal to the likelihood driver's value),
`solveConditionedChecked_eq` (exactly zero mass is rejected) and, for the least-state
selector, `solveConditioned_policy_eq` (equal tables at `x` and `clamp O o x` whenever that row
has positive reach).

This is **not** a byte-for-byte verification of Julia. Remaining refinements are:

* ordered arrays, state labels, reference resolution and the concrete min-fill scheduler. In
  particular the linear order that `Selector.ordered` takes on each action space is supplied;
  that it is Julia's axis-label position is not derived from the ACSet or from the arrays;
* policy tables on zero-probability rows. There no semantic score exists, and the entry is
  fixed by the utility representative. The model's chance step stores utility `0` wherever the
  summed probability is zero, while Julia's `sum_out` keeps a utility table that does not
  contain the summed variable; the likelihood and sliced representations also differ there,
  including on rows that contradict the evidence. Only weighted valuations, values and
  positive-reach tables are proved to agree. The model's empty-bucket decision step adds a
  unit valuation that Julia omits; this changes no value and no table;
* Float64/tolerance behavior. Small action-dependent evidence probabilities can pass the
  source's tolerance guard and yield a wrong reported value; they are outside the theorem's
  action-independent evidence contract. Float64 comparison is not the real order used here:
  rounding can create or break ties, Julia's `argmax` distinguishes `-0.0` from `0.0`, and
  `NaN` compares as largest. `firstArgmax_stable` is only a strict-gap stability contract.

`Finite/OrderedPolicies.lean` supplies the local least-state selector, the information-table
reconstruction theorem and the strict-gap numerical stability contract used above. The BN proof
dependency now includes concrete checked records/references, repeated slots, conditioned
distributions, collect/distribute message correctness, moralized-ancestral d-separation
soundness and conditional numerical error bounds.

The implementation-facing boundaries above must accompany any claim of Proposition 7.
There are no unproved Lean declarations in this module.
-/
