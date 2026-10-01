# Algorithm guarantees and applicability

The mathematical question is whether a solver optimizes the **specified
influence diagram**, with its declared information, evidence and utilities.
This guide separates that question from numerical approximation and from
verification of the host computing platform.

## What is being optimized?

A strategy supplies one policy for every decision. A policy reads only its
declared information variables and selects an action. Substituting those
policies into the diagram gives a Bayesian network; [`expected_utility`](@ref)
evaluates the sum of the original utilities under that network, conditioned on
external evidence when present.

If ``w_\pi(x)`` is the product of the chance kernels and policy probabilities,
the conditional objective is

```math
EU(\pi\mid e)=
\frac{\sum_{x:\,x\models e}w_\pi(x)\sum_j u_j(x)}
     {\sum_{x:\,x\models e}w_\pi(x)}.
```

The denominator must be positive. Kernel normalization gives unconditional
mass one, not evidence mass one. Utilities are additive and may be signed;
constant utilities and disconnected likelihood factors still contribute.

[`optimize`](@ref) searches for a complete strategy; it does not treat the
model's currently installed strategy as a set of optimization constraints.
To evaluate a specified policy, use [`expected_utility`](@ref). Evidence on an
action variable is rejected: fixing an action or substituting a policy is not
conditioning a chance mechanism.

## Choosing the solver

| Situation | DVE | Exhaustive policy search |
|:--|:--|:--|
| Perfect recall, normalized kernels, supported action-free evidence | Intended exact-algebra domain | Independent small-model oracle |
| Some chance variables are hidden | Allowed; hidden variables are marginalized | Allowed |
| Later information depends on an earlier action | Allowed when the information graph is acyclic and perfect recall holds | Allowed |
| A later decision forgets earlier information or actions | Rejected by this backend | Evaluates the original limited-memory problem |
| External evidence has an action among its causal ancestors | Rejected by this backend | Evaluates the conditional objective separately for each supported policy |
| Evidence impossible under every policy | No conditional solution | No conditional solution |
| Too many legal policy tables to enumerate | Can remain tractable with small factors | Explicit policy-count/resource failure |

Perfect recall means remembering earlier **available information and actions**,
not observing every earlier chance variable. The
[hidden-state example](index.md#Perfect-recall-is-not-full-observation)
has perfect recall but success probability only one half; revealing the hidden
state changes the problem and raises the optimum to one.

[`validate`](@ref) deliberately accepts structurally valid diagrams that forget.
[`with_no_forgetting`](@ref) changes their information structure; it is not a
semantics-preserving numerical fix. Use exhaustive search if the original
information restrictions are intentional. Similarly, external observation
conditions the whole optimization problem; adding an information arc changes
what a policy may read. They are different operations.

## Why elimination preserves the objective

DVE keeps a list of valuations ``(\phi,\psi)`` whose combined weighted meaning
is the product of probability terms times the sum of utility terms.
Chance elimination sums probability and weighted utility; decision elimination
selects a utility-maximizing action only when probability is independent of
that action.

The strong order sums hidden chance variables before a decision could
incorrectly exploit them, but retains chance information needed by decisions
not yet eliminated. Decisions are eliminated in reverse chronological order.
At each replacement, **all and only** touching valuation occurrences are
consumed; untouched values and repeated equal factors are retained.

Correctness needs both the value calculation and policy reconstruction.
A reported optimum is insufficient if the returned policy reads unavailable
information or selects a different action. Local choices must be expanded into
complete tables in `information_position` order, and that returned strategy
must realize the reported expected utility.

The abstract finite-model Lean development already proves this kind of
arbitrary-decision correctness with its explicit structural/evidence
assumptions. Concrete array/trace refinement and cross-prover coverage have
additional boundaries. The [certificate guide](certificates.md) explains which
original tables and actual solver observations are retained; a trace is not
automatically a theorem about the implementation.

## Calculation order is a constrained choice

The ordering strategy may reorder chance variables **within** a source-derived
block. It may not change the reverse decision order or eliminate information
before the decision that uses it. Each block is ordered from the current
factors, so `strong_elimination_order` is a useful preview, not necessarily the
actual run order; use `solution.diagnostics.order` or an execution trace for that.

The driver checks every returned block order before using it. Duplicate,
omitted, unknown or out-of-block variables cause
`BayesianNetworkInference.ScopeError`, including for custom
`EliminationStrategy` implementations. In particular, a strategy cannot ask a
chance-elimination step to average over a decision variable.

The built-in graph strategies also validate their returned vertex permutations.
`UserOrder` is rechecked when used, including if its stored vector was mutated
after construction. Its graph-level contract remains strict: it lists exactly
the current non-kept variables. A single global `UserOrder` vector is not
automatically a separate valid order for every DVE chance block.

These checks protect the ordering boundary; they do not establish that a
heuristic finds the smallest possible intermediate factors. The formal
schedule question is whether **every permitted order** preserves the exact
optimal value and yields a legal optimal strategy. Equality of complete policy
tables at ties or unreachable rows is a different, stronger question.

## Ties and unreachable information rows

Equal optimal values do not require identical policy tables. The native DVE
selector breaks exact local ties by the first action label; exhaustive search
returns the first best strategy in its own enumeration. Ties are decided by
comparing with `==`, so `-0.0` and `0.0` tie as the equal reals they are and the
first label wins; a NaN or infinite utility is rejected by every backend. On the
Float64 path rounding can still create or break a tie that exact arithmetic would
see differently; `stable=true` compares exact rationals. An information row with zero
probability can also have several globally equivalent choices.

```@example policy_equivalence
using InfluenceDiagrams

id = influence_diagram(:Signal => [:common, :unreachable],
                       :Act => [:off, :on];
                       decisions=[:Act => :Signal],
                       utilities=[:Reward => (:Signal, :Act)])
model = bind_cpt(InfluenceDiagramModel(id), :Signal => [1.0, 0.0])
model = bind_utility(model, :Reward => [1.0 1.0; -5.0 9.0])

first_policy = Strategy(:Act => deterministic_policy(model, :Act, _ -> :off))
second_policy = Strategy(:Act => deterministic_policy(model, :Act, _ -> :on))
(expected_utility(model, first_policy), expected_utility(model, second_policy))
```

Both values are one: the common row is a genuine tie, and the other row is
unreachable. Nevertheless, every returned table must have the right signature
and contain valid actions, including on unreachable rows. Policy comparison
should check admissibility, attained value and reachability, rather than demand
whole-array identity. Changing other policies can change reachability, so
re-evaluate the complete strategy instead of permanently ignoring such rows.

Near-ties are different from exact ties. A small score perturbation can change
the selected action. A strict gap greater than twice a uniform action-score
error protects the maximizer, but the gap theorem does not itself provide that
error bound for a floating-point solver.

In the exact finite model, the Lean theorem `solveOrdered_table` proves that the
least-state (first-label) selector returns, on every row, the least maximizer of
that row's bucket utility, and `solveOrdered_semantic` that on every row of
positive probability this is the least maximizer of the expected utility of
acting there and then following the returned later policies. A zero-probability
row has no such semantic score; its entry depends on how the utility potential
is represented there, and is not claimed to match between representations.

With evidence, DVE slices every chance factor and every utility at the observed
states. The returned policy therefore ignores observed information variables: on
a row that contradicts the evidence it repeats the action of the observed row,
not the action that would be optimal had that row been possible. The Lean model
of this conditioning agrees with the likelihood representation on every row of
positive probability (`solveConditioned_policy_eq`) and repeats the observed
row's entry elsewhere (`solveConditioned_kernel_clamp`).

## Zero mass, rare evidence and numerical interpretation

An exactly zero row is not replaced with a small positive probability. In
chance reduction, nonnegative probabilities make a zero denominator imply a
zero weighted numerator; the zero utility branch preserves weighted meaning.
An entirely impossible evidence event has no conditional expected utility and
raises `ImpossibleEvidenceError`, rather than returning zero as an answer.

An extremely small **positive** mass is a different case. Ordinary Float64
arithmetic may underflow or lose a small utility through cancellation.
`DecisionVariableElimination(stable=true)` uses exact rational meanings of the
bound data for its bucket arithmetic and rounds the final value. It can
therefore avoid those failures while retaining the same information
restrictions.

The default backends do not report an underflow as impossibility (ADR 0014).
When the ordinary run ends with an evidence mass that is not a normal positive
Float64, `DecisionVariableElimination` reruns the same schedule in exact
rational arithmetic and `ExhaustivePolicySearch` scores strategies one at a
time through `BayesianNetworks.marginal`, whose own fallback is exact and
correctly rounded (ADR 0016); both record `exact_fallback = true` in
the diagnostics. `ImpossibleEvidenceError` therefore means probability exactly
zero. A model with tolerated negative entries (in `[-atol, 0)`) whose evidence
mass is not larger than the tolerance budget has no determined answer and
raises `IndeterminatePosteriorError` instead of returning one.

Exact arithmetic on stored values is not the same as exact normalization of
those values. A rounded CPT accepted within the model's `atol` need not sum
exactly to one. Stable DVE does not silently renormalize it. Its
`exact_probability_guards` diagnostic concerns action constancy, **not** exact
normalization of all source CPTs. The independent trace consumer checks both
when applying the exact-model contract.

`ExhaustivePolicySearch(stable=true)` evaluates policies using log-domain
marginals and compensated sums; it is not an exact-rational policy oracle.
For finite exact conformance, the workspace also uses independent rational
enumeration. Agreement with a numerical oracle remains empirical, whereas
the finite-model proofs state their normalization, positivity and
information premises explicitly.

## Evidence downstream of actions

Conditioning on an action's descendant can make evidence probability depend on
the policy. Maximizing an unnormalized numerator is then not generally the
same as maximizing the conditional ratio. This is why DVE rejects that case
structurally, regardless of how small the evidence probability is.

Exhaustive search can compare the ratio for each policy with positive evidence
mass and exclude policies under which evidence is impossible. That is a
well-defined conditional optimization calculation, not automatically a
prospective causal recommendation. If the intended question is the outcome
of choosing an action before observing its consequences, use the corresponding
unconditioned decision model rather than conditioning on a future outcome.

The exact-algebra results, tested native algorithms and ordinary trusted
computing platform are separate levels of assurance. General parser,
compiler and physical-hardware verification is not a prerequisite for
understanding these network-specific guarantees.
