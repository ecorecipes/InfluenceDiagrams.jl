import InfluenceDiagramsProofs.Finite.DVE.PlanIndependence

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

`Finite/DVE/PlanIndependence.lean` removes the dependence of those first-label results on
`NoForgettingOrder.plan`'s enumeration of the chance blocks. For **any two plans** (any
interleaving that `Plan` accepts, in particular two min-fill orders of the chance variables
inside the strong blocks), `solvePlanOrdered_table_eq`, `solveEvidencePlanOrdered_table_eq` and
`solveConditionedPlan_table_eq` prove equal first-label entries on every row of positive reach
(for the conditioned driver: every row whose clamped row has positive reach). Every plan maximizes
a decision with the same remaining set, where the weighted valuation is the plan-independent
`optimalContinuation` (a supremum over nonnegative strategies); the entry is its least maximizer
(`runWith_ordered_optimal`), and reach is the same under every strategy
(`reach_strategy_independent`). No counterexample exists on positive-reach rows.

This is **not** a byte-for-byte verification of Julia. Remaining refinements are:

* ordered arrays, state labels, reference resolution and the concrete min-fill scheduler. In
  particular the linear order that `Selector.ordered` takes on each action space is supplied;
  that it is Julia's axis-label position is not derived from the ACSet or from the arrays.
  That Julia's block schedule is a `Plan` is read off the source, not derived; given that,
  positive-reach tables do not depend on which min-fill order it chose;
* policy tables on zero-probability rows. There no semantic score exists, and the entry is
  fixed by the utility representative. The model's chance step stores utility `0` wherever the
  summed probability is zero, while Julia's `sum_out` keeps a utility table that does not
  contain the summed variable; the likelihood and sliced representations also differ there,
  including on rows that contradict the evidence. Only weighted valuations, values and
  positive-reach tables are proved to agree. Zero-reach entries are also not claimed to be
  independent of the elimination plan. The model's empty-bucket decision step adds a
  unit valuation that Julia omits; this changes no value and no table;
* Float64/tolerance behavior. Small action-dependent evidence probabilities can pass the
  source's tolerance guard and yield a wrong reported value; they are outside the theorem's
  action-independent evidence contract. Float64 rounding can create or break ties that the
  real order used here does not see. (Signed zeros and `NaN` no longer differ: Julia's
  `argmax_table` compares with `==` and every backend rejects non-finite utilities.)
  `firstArgmax_stable` is only a strict-gap stability contract.

`Finite/OrderedPolicies.lean` supplies the local least-state selector, the information-table
reconstruction theorem and the strict-gap numerical stability contract used above. The BN proof
dependency now includes concrete checked records/references, repeated slots, conditioned
distributions, collect/distribute message correctness, moralized-ancestral d-separation
soundness and conditional numerical error bounds.

The implementation-facing boundaries above must accompany any claim of Proposition 7.
There are no unproved Lean declarations in this module.
-/
