import InfluenceDiagramsProofs.Finite.DVE.LabelOrder

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

`Finite/DVE/Representative.lean` models Julia's chance step on zero-probability rows: when the
summed variable is not in the utility potential's scope, Julia's `sum_out` keeps the utility
unchanged where the model stores `0`. `sumOutKeep keep` covers both (`keep = false` is the model,
`sumOutKeep_false`; `keep = true` is literally Julia's `ψ′ = ψ` whenever the bucket utility does not
depend on the summed variable, `sumOutKeep_util_of_const`), and every theorem holds for every
`keep : id.V → Bool`. On any plan the two runs agree valuation by valuation in scope,
probability potential and weighted utility (`solveRepPlan_agrees`); the returned strategy
realizes the global optimum and the value is the model's (`solveRepPlanWith_spec`,
`solveRepPlanWith_value`); on every row of positive reach the scores and, for every selector,
the policy entries are the model's (`solveRepPlanScore_eq`, `solveRepPlanWith_kernel_eq`); and on
every row, reachable or not, the first-label table is `orderedTable` of the run's own score
(`solveRepPlanOrdered_table`). Julia's representative therefore cannot change a returned table
entry on a reachable row.

`Finite/DVE/LabelOrder.lean` derives the selector's order from checked records instead of
supplying it. `Records.Diagram` holds raw rows (state rows with `var`, `position`, `name`);
`Valid` checks bounded unique positions, nonempty spaces and unique labels; `compile` gives a
`FinInfluenceDiagram` with state spaces `Fin (stateCount v)`, and `actionOrder` orders each action
space by checked `position` (`actionOrder_le_iff`). With `Records.Diagram.selector`,
`solveRecords_table`, `solveRepRecords_table` and `solveRepRecords_optimal` prove that the returned
entry is the maximizer of least checked `state_position` (every row of the model's and Julia's
representative's score; every positive-reach row of `optimalContinuation`).

This is **not** a byte-for-byte verification of Julia. Remaining refinements are:

* the record-to-Julia link. `Records.Diagram` is produced from a parsed ACSet JSON tree by the
  proved decoder of `Finite/DVE/JsonRecords.lean` (faithful, `decodeDiagram_eq_ok`, with round
  trip and failure lemmas), but `Lean.Json.parse` and Julia's JSON3/ACSets writer are trusted.
  `Valid` checks only the state rows; `FullValid` (`Finite/DVE/RecordsValid.lean`) checks every
  table, including the decision-precedence rows as Julia's `validate` does (Julia's
  `information_graph` acyclic), and discharges closedness and the order of the compiled diagram,
  while no-forgetting stays a hypothesis; `NamesUnique` is the separate `unique_names = true`
  check. The DVE certificate of `export_dve_certificate` is decoded faithfully
  (`Finite/DVE/CertificateJson.lean`, `decodeCertificate_eq_ok`) and checked against the
  records (`Finite/DVE/CertificateCheck.lean`, `certificateMatches`); it carries model data and
  no policy, value or plan, so `certificate_solve_spec` and `certificate_tables_optimal` are
  about the model its exact numbers define (applicable only when its CPT rows sum to exactly
  one, which Julia's default binary64 words rarely do), not about Julia's computed solution.
  That Julia's action axis lists the
  states in `state_position` order is pinned by a Julia test, and the array layout is the
  `FiniteKernels` `Layout/` result; Julia's execution itself is not proved. That Julia's block
  schedule is a `Plan`, and which `keep` its run uses, are read off the source, not derived;
* zero-probability rows beyond the above. There no semantic score exists, so a zero-reach
  entry is fixed by the representatives and is not claimed independent of the elimination
  plan. Julia's hard-evidence path (sliced factors, absent variables skipped) is proved only
  against the model's representative (`Conditioning.lean`); combined with Julia's `keep`
  representative it is not modelled. The model's empty-bucket decision step adds a unit
  valuation that Julia omits; this changes no value and no table;
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
