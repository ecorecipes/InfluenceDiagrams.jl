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
lake build                  # `make build`: verifies every proof in the default target
lake env lean Audit.lean    # `make audit`: #print axioms for every main theorem
lake exe emit_schema        # `make emit-schema`: regenerate schemas/influence_diagram.schema.json
lake exe emit_schema --check  # `make check-schema`: exit 1 if the JSON is stale
lake build InfluenceDiagramsProofs.Roadmap  # `make roadmap`: type-check the unproved statements
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
6. `Roadmap.lean` — rendered last as "Roadmap (contains `sorry`)"; not in the default target

## What is formalised

All results are over an arbitrary commutative semiring `R` (instantiate at `ℝ≥0` or `ℝ`).

| Module | Content |
|---|---|
| `Finite/InfluenceDiagram.lean` | `FinInfluenceDiagram extends FinBayesNet`: decisions `D` with `action : D → V` and information sets `info : D → Finset V`, utility nodes `U` with scopes `uscope`. Validity: `GeneratorsDisjoint`, `GeneratorsCover`, `Closed` (`Sum.elim target action` bijective) with `closed_iff` unpacking it into injectivity, disjointness and coverage; `IDOrder` (a variable order with `parents_before`, `info_before_action`, `no_self`, `no_self_info`). `Policy id R d` = kernel `Assignment → states (action d) → R` that is `LocalOn (info d)` and normalised; `Policy.ofFun` (deterministic), `Policy.const` (local for every information set); `Strategy id R = ∀ d, Policy id R d` (complete by construction); `Strategy.fix` (`fix_decision`). |
| `Finite/Instantiate.lean` | **Prop 5.** `instantiate id : FinBayesNet` with `M := M ⊕ D`, `target := Sum.elim target action`, `parents := Sum.elim parents info`; kernels `strategyKernel κ σ = Sum.elim κ (σ ·).kernel`. `closed_instantiate` (from `Closed id`), `IDOrder.toTopoOrder`, `local_instantiate`, `normalised_instantiate`, hence `sum_joint_instantiate_eq_one : ∑ x, joint (strategyKernel κ σ) x = 1` (Prop 1a of the BN project applied to the instantiated network) and the factorisation `joint_instantiate : joint (strategyKernel κ σ) x = (∏ m, κ m x (x (target m))) * ∏ d, (σ d).kernel x (x (action d))` (SPEC §31). |
| `Finite/ExpectedUtility.lean` | **Prop 6.** `Utility id R = U → Assignment → R`, `Utility.Local`, `totalUtility u x = ∑ j, u j x`, `expectedUtility κ σ u = ∑ x, joint (strategyKernel κ σ) x * totalUtility u x`. `expectedUtility_eq` (Prop 6 written out through `joint_instantiate`), linearity `expectedUtility_add` / `expectedUtility_smul`, additive decomposition `expectedUtility_eq_sum : EU = ∑ j, ∑ x, joint x * u j x` (SPEC §30–§31), `expectedUtility_const` (constant total utility `c` has expected utility `c`, via Prop 5). **`fix_decision`:** `strategyKernel_fix_eq_intervene : strategyKernel κ (σ.fix d a) = intervene (strategyKernel κ σ) (.inr d) a` — fixing a decision is the hard intervention of the BN project on the corresponding mechanism, so `joint_fix` is Prop 4's truncated factorisation and `expectedUtility_fix` follows. |
| `Finite/Information.lean` | **Information monotonicity** (SPEC §34, §35, §55.7). `localOn_mono`; `withInfo id info'` (same diagram, enlarged information sets); `Policy.enlarge`, `Strategy.enlarge`; `strategyKernel_enlarge`, `expectedUtility_enlarge` (same kernels, same joint, same expected utility); `exists_strategy_enlarged_eq : ∀ σ, ∃ σ', EU σ' = EU σ` — the optimal expected utility cannot decrease when information is added. |
| `Basic.lean` | Smoke test. |
| `Roadmap.lean` | Unproved statements (`sorry`), **not** in the default target or the audit — see below. |

`Audit.lean` prints the axioms of every main theorem (and of the definitions `Policy.ofFun`,
`Policy.const`, `IDOrder.toTopoOrder`); all report a subset of `propext`, `Classical.choice`,
`Quot.sound`.

### Correspondence

| SPEC | Lean | Julia |
|---|---|---|
| §26–§27 policies, strategies | `Policy`, `Policy.ofFun`, `Strategy` | `DeterministicPolicy`, `StochasticPolicy`, `Strategy` |
| §28, §61 Prop 5 | `instantiate`, `strategyKernel`, `closed_instantiate`, `IDOrder.toTopoOrder`, `sum_joint_instantiate_eq_one`, `joint_instantiate` | `instantiate(id, strategy) -> BayesNet` (`validate(closed=true)` succeeds) |
| §29–§31, §61 Prop 6 | `Utility`, `totalUtility`, `expectedUtility`, `expectedUtility_eq`, `expectedUtility_eq_sum` | `expected_utility(id, strategy)` (instantiate, enumerate the joint, sum utilities, take the expectation) |
| §41 fixed decision | `Policy.const`, `Strategy.fix`, `strategyKernel_fix_eq_intervene`, `joint_fix` | `fix_decision(model, :D => :a)` = `do_intervention` on the instantiated network |
| §34–§35, §55.7 | `withInfo`, `Strategy.enlarge`, `exists_strategy_enlarged_eq` | `expected_value_of_information` is non-negative |
| §24 schema | `schInfluenceDiagram` (defined in the BayesianNetworks project), re-emitted by `lake exe emit_schema` | `SchInfluenceDiagram` (`generate_json_acset_schema` compared with `schemas/influence_diagram.schema.json` modulo `version`) |

### Roadmap (contains `sorry`)

* `FinInfluenceDiagram.exists_deterministic_optimal` — the single-decision shadow of **Prop 7**
  (DVE correctness): over `ℝ`, with non-negative chance kernels, some deterministic strategy
  dominates every non-negative strategy, so exhaustive policy enumeration finds the optimum.
  The multi-decision statement holds only in the regular (perfect-recall) subset the Julia
  solver supports and is covered by property tests against exhaustive enumeration (SPEC §55.6).

## How the schema JSON reaches Julia

`schInfluenceDiagram` is defined once, in `BayesianNetworksProofs/Schema/BayesNet.lean`, as an
extension of `schBayesNet`. `lake exe emit_schema` (target `emit_schema`, root `Main.lean`;
links only Lean core because the `Schema/` modules do not import Mathlib) re-emits it as
`schemas/influence_diagram.schema.json` in the shape of ACSets.jl's
`generate_json_acset_schema`, byte-identical to the file of the BayesianNetworks project. The
Julia test compares `generate_json_acset_schema(SchInfluenceDiagram)` with this committed file
structurally, modulo the `version` object; `lake exe emit_schema --check` (run in CI after the
build) exits 1 if the committed file differs from what the Lean term would emit.
