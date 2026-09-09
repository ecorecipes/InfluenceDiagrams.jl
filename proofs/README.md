# InfluenceDiagramsProofs

Lean 4 / Mathlib formalisation accompanying `InfluenceDiagrams.jl` (toolchain
`leanprover/lean4:v4.30.0`, Mathlib tag `v4.30.0`; ADR 0005). It depends by path on the
BayesianNetworks proofs project (`../../BayesianNetworks.jl/proofs`, Lake package
`bayesian_networks_proofs`), which supplies the finite Bayesian-network model (`FinBayesNet`,
kernels, `Local`, `Normalised`, `Closed`, `TopoOrder`, `joint`, Propositions 1 and 4) and the
ACSet schema terms.

```sh
cd proofs
lake exe cache get          # prebuilt Mathlib oleans (shared checkout, see below)
lake build --wfail          # `make build`: verifies every proof in the default target
make audit                 # axiom inventory, whitelist and source escape-hatch scan
lake exe emit_schema        # `make emit-schema`: regenerate schemas/influence_diagram.schema.json
lake exe emit_schema --check  # `make check-schema`: exit 1 if the JSON is stale
lake build InfluenceDiagramsProofs.Roadmap --wfail  # remaining-work module, no sorry
```

The dependency checkout is shared with the other ecosystem `proofs/` projects through
`packagesDir = "../../.lake-packages"` (gitignored); CI rewrites it to a local `.lake/packages`
and checks out `ecorecipes/BayesianNetworks.jl` next to this repository so the path `require`
resolves. Every module imports only the Mathlib files it needs (never `import Mathlib`) and sets
`autoImplicit false`.

## Documents

The proofs are also rendered as a readable document (`InfluenceDiagramsProofs.md`, `.html`, `.pdf`, committed
here). It is generated from the Lean sources by [mdgen](https://github.com/Seasawher/mdgen)
(Lake dependency, tag `v4.30.0`): the `/-! ... -/` module docstrings become prose and everything
else becomes a `lean` code block, so the document is the verbatim, machine-checked source.

```sh
make mdgen   # InfluenceDiagramsProofs.md   — lake exe mdgen, modules concatenated in import order
make html    # InfluenceDiagramsProofs.html — pandoc --standalone --toc --mathjax, style.css
make pdf     # InfluenceDiagramsProofs.pdf  — pandoc → lualatex with header.tex (STIX Two Text/Math, JuliaMono)
make docs    # all three
```

Requirements: pandoc (≥ 3.8; `lean.xml` is a minimal Lean syntax definition, pandoc has none
built in) and a TeX distribution with `lualatex` (TinyTeX or MacTeX). Fonts: STIX Two Text and
STIX Two Math (macOS system fonts, or TeX Live `stix2-otf`) for prose and mathematics, and
[JuliaMono](https://juliamono.netlify.app) (SIL OFL) for code, which covers all of Lean's
Unicode; it is read from `../../fonts/JuliaMono/` by path (`header.tex`), not installed
system-wide. `make pdf` prints the number of `Missing character` warnings in the LaTeX log
(expected 0). The documents are built locally and committed; CI does not rebuild them.

Module order (`MD_FILES` in the `Makefile`, the import order of `InfluenceDiagramsProofs.lean`):

1. `Basic.lean` — introduction, structure and SPEC/Julia correspondence tables
2. `Finite/InfluenceDiagram.lean`
3. `Finite/Instantiate.lean`
4. `Finite/ExpectedUtility.lean`
5. `Finite/Information.lean`
6. `Finite/Optimization.lean`
7. `Finite/OptimalInformation.lean`
8. `Finite/DVE/Valuation.lean`, `Semantics.lean`, `Driver.lean`, `Solver.lean`
9. `Finite/DVE/Schedule.lean`, `Evidence.lean`, `Example.lean`
10. `Finite/DVE/Guard/Positive.lean`, `Provenance.lean`, `Complete.lean`, `Boundary.lean`
11. `Finite/OrderedPolicies.lean` — supplied state-order ties, finite information tables and gap stability
12. `Roadmap.lean` — remaining literal-implementation refinements; no unproved declarations

## What is formalised

The algebraic results are over an arbitrary commutative semiring `R`; optimisation and the
attained-optimum information theorems use `ℝ`. `Policy` requires normalisation but, over
`ℝ`, not nonnegativity: `Strategy.Nonneg` is an explicit premise of optimisation. The
inherited `FinBayesNet.nonemptyS` fields ensure that every action space is nonempty.

| Module | Content |
|---|---|
| `Finite/InfluenceDiagram.lean` | `FinInfluenceDiagram extends FinBayesNet`: decisions `D` with `action : D → V` and information sets `info : D → Finset V`, utility nodes `U` with scopes `uscope`. Validity: `GeneratorsDisjoint`, `GeneratorsCover`, `Closed` (`Sum.elim target action` bijective) with `closed_iff` unpacking it into injectivity, disjointness and coverage; `IDOrder` (a variable order with `parents_before`, `info_before_action`, `no_self`, `no_self_info`). `Policy id R d` = kernel `Assignment → states (action d) → R` that is `LocalOn (info d)` and normalised; `Policy.ofFun` (deterministic), `Policy.const` (local for every information set); `Strategy id R = ∀ d, Policy id R d` (complete by construction); `Strategy.fix` (`fix_decision`). |
| `Finite/Instantiate.lean` | **Prop 5.** `instantiate id : FinBayesNet` with `M := M ⊕ D`, `target := Sum.elim target action`, `parents := Sum.elim parents info`; kernels `strategyKernel κ σ = Sum.elim κ (σ ·).kernel`. `closed_instantiate` (from `Closed id`), `IDOrder.toTopoOrder`, `local_instantiate`, `normalised_instantiate`, hence `sum_joint_instantiate_eq_one : ∑ x, joint (strategyKernel κ σ) x = 1` (Prop 1a of the BN project applied to the instantiated network) and the factorisation `joint_instantiate : joint (strategyKernel κ σ) x = (∏ m, κ m x (x (target m))) * ∏ d, (σ d).kernel x (x (action d))` (SPEC §31). |
| `Finite/ExpectedUtility.lean` | **Prop 6.** `Utility id R = U → Assignment → R`, `Utility.Local`, `totalUtility u x = ∑ j, u j x`, `expectedUtility κ σ u = ∑ x, joint (strategyKernel κ σ) x * totalUtility u x`. `expectedUtility_eq` (Prop 6 written out through `joint_instantiate`), linearity `expectedUtility_add` / `expectedUtility_smul`, additive decomposition `expectedUtility_eq_sum : EU = ∑ j, ∑ x, joint x * u j x` (SPEC §30–§31), `expectedUtility_const` (constant total utility `c` has expected utility `c`, via Prop 5). **`fix_decision`:** `strategyKernel_fix_eq_intervene : strategyKernel κ (σ.fix d a) = intervene (strategyKernel κ σ) (.inr d) a` — fixing a decision is the hard intervention of the BN project on the corresponding mechanism, so `joint_fix` is Prop 4's truncated factorisation and `expectedUtility_fix` follows. |
| `Finite/Information.lean` | **Information monotonicity** (SPEC §34, §35, §55.7). `localOn_mono`; `withInfo id info'` (same diagram, enlarged information sets); `Policy.enlarge`, `Strategy.enlarge`; `strategyKernel_enlarge`, `expectedUtility_enlarge` (same kernels, same joint, same expected utility); `exists_strategy_enlarged_eq : ∀ σ, ∃ σ', EU σ' = EU σ` — the optimal expected utility cannot decrease when information is added. |
| `Basic.lean` | Smoke test. |
| `Finite/Optimization.lean` | `joint_table_mixture` and `expectedUtility_table_mixture`; `exists_deterministic_optimal_all` proves global deterministic sufficiency for any finite number of decisions, without a perfect-recall premise. The original single-decision theorem is a corollary. `signed_weights_exceed_every_action` shows why strategy nonnegativity matters. |
| `Finite/OptimalInformation.lean` | `optimalValue_attained`, `optimalValue_info_mono`, `optimal_information_value_nonneg`: genuine attained maxima and cost-free information-value nonnegativity, not only same-value strategy inclusion. |
| `Finite/DVE/` | Actual `(φ,ψ)` bucket algorithm, generated no-forgetting schedule, structural probability independence, local deterministic reconstruction, realization and equality to the global optimum; action-free ancestral evidence with a proved strategy-independent normalizer and an explicit positive-mass boundary. |
| `Finite/DVE/Guard/` | The exact all-row probability diagnostic is complete, including zero-outside contexts. Probability-expression provenance and continuous normalized smoothing remove the temporary strict-positivity assumption. Checked drivers return the previously proved result; zero evidence mass remains a separate rejection. |
| `Roadmap.lean` | Remaining literal-Julia refinements; no unproved declarations. |

`Audit.lean` prints the axioms of every main theorem (and of the definitions `Policy.ofFun`,
`Policy.const`, `IDOrder.toTopoOrder`); all report a subset of `propext`, `Classical.choice`,
`Quot.sound`. `make audit` also rejects missing/ambiguous results, any other axiom and

The axiom audit is fail-closed and shared with the existing BN proof dependency. It rejects
missing/duplicate/unexpected results, unknown axioms, warnings and source escape hatches.
The source scanner permits kernel-checked `decide +kernel` but rejects native proof shortcuts.

### Ordered policy tables and numerical margins

`Finite/OrderedPolicies.lean` constructs the least maximizing local action in a supplied finite
linear order and proves the exact first-state tie property. On raw compiled state spaces
`Fin n`, this is the checked `state_position` order. A finite table over only the information
variables reconstructs the same admissible local policy. A strict `2ε` score gap proves that
uniform score errors bounded by `ε` cannot change the selected action.

This is a local policy/table and stability bridge. It does not silently replace the previously
proved DVE driver's arbitrary classical tie selector or prove its output array identical to
Julia's first-label arrays. The BN numerical module supplies separate CPT/product and
positive-mass-dependent posterior error contracts; no universal Float64 equality is claimed. `make audit` also rejects missing/ambiguous results, any other axiom and
proof escape hatches in this project's sources and its own BayesianNetworks proof
dependency. The CI workflow runs that fail-closed command.

### Correspondence

| SPEC | Lean | Julia |
|---|---|---|
| §26–§27 policies, strategies | `Policy`, `Policy.ofFun`, `Strategy` | `DeterministicPolicy`, `StochasticPolicy`, `Strategy` |
| §28, §61 Prop 5 | `instantiate`, `strategyKernel`, `closed_instantiate`, `IDOrder.toTopoOrder`, `sum_joint_instantiate_eq_one`, `joint_instantiate` | `instantiate(id, strategy) -> BayesNet` (`validate(closed=true)` succeeds) |
| §29–§31, §61 Prop 6 | `Utility`, `totalUtility`, `expectedUtility`, `expectedUtility_eq`, `expectedUtility_eq_sum` | `expected_utility(id, strategy)` (instantiate, enumerate the joint, sum utilities, take the expectation) |
| §41 fixed decision | `Policy.const`, `Strategy.fix`, `strategyKernel_fix_eq_intervene`, `joint_fix` | `fix_decision(model, :D => :a)` = `do_intervention` on the instantiated network |
| §34–§35, §55.7 | `withInfo`, `Strategy.enlarge`, `exists_strategy_enlarged_eq` | `expected_value_of_information` is non-negative |
| §24 schema | `schInfluenceDiagram` (defined in the BayesianNetworks project), re-emitted by `lake exe emit_schema` | `SchInfluenceDiagram` (`generate_json_acset_schema` compared with `schemas/influence_diagram.schema.json` modulo `version`) |

### Deterministic optimality and the remaining Proposition 7 gap

The original `exists_deterministic_optimal` Roadmap statement is now proved. More strongly,
`exists_deterministic_optimal_all` produces a deterministic, nonnegative strategy dominating
every nonnegative strategy for **any finite number of decisions**, including limited-memory
diagrams. Each decision contributes one policy factor per joint assignment, so independent
sampling of each policy row expresses its joint as a mixture over deterministic tables.
Expected utility is the same convex combination and is bounded by the largest table value.

The previous assertion that this multi-decision existence result required perfect recall
was false for this finite model. Perfect recall concerns the correctness of the particular
backward/strong-order elimination algorithm, not existence of a deterministic global optimum.
The global theorem does not even need chance-kernel positivity, locality or normalisation
for its algebraic bound. Those premises and diagram validity remain necessary when claiming
the joint is a probability distribution.

### Actual decision variable elimination

The optimum-existence theorem is no longer the endpoint. `DVE.solve` performs bucket
combination, chance summation with `0/0 := 0`, and separate probability/utility maxima at
decisions, recording local utility-maximizing policies. It never enumerates strategies.
`NoForgettingOrder.plan` generates the strong schedule from a complete reverse-chronological
decision list with perfect recall. Its data contains only variable/information-set conditions,
not a semantic legality certificate. `RankedOrder.ofOrder` derives numeric ranks from the
existing `IDOrder`.

`DVE.probability_independent` proves the crucial free-action independence from closedness,
causal/information acyclicity, local normalized chance kernels, normalized reconstructed
policies and the generated information boundary. Hidden ancestors may be summed after their
observed descendants: the proof first normalizes a topological downstream block and then
marginalizes the remaining ancestors. It is not restricted to fully observed trees.

`DVE.solve_spec` proves that the actual output strategy is deterministic (admissibility is
carried by `Policy`), that it realizes the reported value, and that the value equals the
existing `optimalValue`. All chance kernels are explicitly nonnegative and normalized;
utilities may have either sign and must be local to their declared scopes. Finite nonempty
action spaces are inherited from `FinBayesNet`. Zero probability rows are allowed.

`DVE.solveEvidence_spec` and `DVE.solveEvidence_eq_optimal` handle nonnegative likelihoods
on an **action-free chance-ancestral set**, including hard evidence indicators. Evidence-mass
independence is proved, not assumed. Conditional claims require positive mass.
`solveEvidenceChecked_eq` proves that the driver checks its own computed mass and rejects
zero mass. Action-descendant evidence is outside this contract.

The Boolean hidden-state example has two decisions, a noisy initial observation, a test that
can reveal the hidden state, and unreachable information rows. Its closedness, topological
order, perfect recall, CPT locality/normalization/nonnegativity and utility locality are all
checked before instantiating the generic solver theorem.

**Refinement boundaries remain.** The finite-function solver has common sufficient scopes
rather than separate ordered probability/utility arrays. It allows arbitrary fixed local
argmax ties rather than proving Julia's first-label table identity. Equivalence means realized
optimal value, not equal joint distributions or equal actions on tied/unreachable rows.
The exact all-row probability guard is now proved complete, including unreachable bucket rows:
see `all_guards_complete`, `all_guards_complete_evidence`, `checkedRun_generated_eq` and
`checkedRun_generated_evidence_eq`. The source's special
representatives for zero-weight utilities and explicit array conditioning are not proved
entrywise equal to the likelihood-factor representation. Float64 tolerance behavior is not
covered and can admit action-dependent evidence that violates the exact invariant.

### Exact all-row diagnostic completeness

`ExactGuard` quantifies every assignment and every action. `exactGuard_iff_diagnostic` proves
that it is equivalent to nonpositivity of the maximum row maximum-minus-minimum, precisely the
source check at exact zero tolerance. `checkedRun` executes this diagnostic without a
reachability restriction.

The proof tracks a fixed symbolic probability expression for every actual bucket. Its leaves
are original chance entries, one and the optional likelihood; its operations are finite
products, sums and maximum values. It does not include utility division or utility argmax
selectors. For positive inputs the existing structural global-independence theorem permits
cancellation of all outside products. Every kernel is approximated by the local normalized
family `(κ+t)/(1+n*t)`, and the supported likelihood by `L+t`. For `t>0` every exact guard
holds. The fixed probability expressions are continuous at `t=0`, including finite maximum
values, so all identities extend to the original nonnegative inputs. The argmax selector
itself is not claimed continuous, and no smoothing is performed by the actual solver.

`solveGuarded_spec` returns a realized deterministic optimum without adding strict positivity.
For supported evidence, `solveEvidenceGuarded_none_iff` says the probability guard introduces
no extra rejection: failure means exactly zero total evidence mass.
`Guard/Boundary.lean` checks a normalized no-evidence model with a deterministic observed
root whose factor is zero outside the action bucket and a summed child retaining the action
axis in its probability factor, and the previous hidden-state model with
an identically zero supported likelihood. In the latter, the probability guard succeeds and
the subsequent evidence-mass check rejects.

`optimalValue_info_mono` compares attained maxima with the same chance kernels and utilities.
Its nonnegative information-value corollary includes no acquisition cost, no solver claim,
and no proof that every possible information enlargement respects temporal validity.

## How the schema JSON reaches Julia

`schInfluenceDiagram` is defined once, in `BayesianNetworksProofs/Schema/BayesNet.lean`, as an
extension of `schBayesNet`. `lake exe emit_schema` (target `emit_schema`, root `Main.lean`;
links only Lean core because the `Schema/` modules do not import Mathlib) re-emits it as
`schemas/influence_diagram.schema.json` in the shape of ACSets.jl's
`generate_json_acset_schema`, byte-identical to the file of the BayesianNetworks project. The
Julia test compares `generate_json_acset_schema(SchInfluenceDiagram)` with this committed file
structurally, modulo the `version` object; `lake exe emit_schema --check` (run in CI after the
build) exits 1 if the committed file differs from what the Lean term would emit.
