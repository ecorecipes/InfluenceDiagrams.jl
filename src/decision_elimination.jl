"""
Decision variable elimination (SPEC §33, Proposition 7) over the [`Valuation`](@ref)
algebra, and the value of information (SPEC §35, §55.7).

The strong elimination order follows the decision order `D₁ ≺ ... ≺ Dₙ` of
[`decision_order`](@ref): the variables are partitioned into blocks
`I₀ ≺ D₁ ≺ I₁ ≺ ... ≺ Dₙ ≺ Iₙ`, where `I_{k-1}` holds the chance variables first
observed at `D_k` (in the information set of `D_k` but of no earlier decision) and
`Iₙ` holds the chance variables never observed. Elimination proceeds from the last
block backwards: `Iₙ` is summed out, `Dₙ` maximised, `I_{n-1}` summed out, and so on,
with a min-fill (or other `EliminationStrategy`) order inside each chance block.
Every returned block order is checked before execution: it must contain each
currently present variable in that chance block exactly once, and no other
variable. A custom strategy cannot move an action into a chance block or discard
information by crossing a block boundary.

The algorithm is exact when, at the moment each decision is maximised, the utility
potential depends only on variables in that decision's information set. This is the
*no-forgetting* (perfect recall) subset of influence diagrams: everything known at a
decision is still known at every later one. [Shachter1986](@cite) reserves *regular*
for the weaker property that a directed path runs through all the decisions, so the two
terms are kept apart here; [`no_forgetting_arcs`](@ref) reports what is missing and
[`with_no_forgetting`](@ref) adds it. Eliminating decisions by dynamic programming over
the diagram is the scheme of [TatmanShachter1990](@cite), here carried out on the
[`Valuation`](@ref) algebra of [JensenJensenDittmer1994](@cite).

No-forgetting is deliberately not a validity condition: a diagram that forgets is a
well-formed limited-memory influence diagram [LauritzenNilsson2001](@cite) which
[`ExhaustivePolicySearch`](@ref) solves exactly, and which [`validate`](@ref)
therefore accepts. It is this backend that requires it, and it says so at run time with
an [`IrregularDiagramError`](@ref) naming the variables the decision maker would have to
remember. Note that [`decision_order`](@ref) linearises a partial order by part id, so
two decisions with no arcs between them are ordered but do not know each other's
actions: that is a forgetting diagram, and `with_no_forgetting` is the repair.

External evidence must have no action among its causal ancestors. This structural
precondition is checked before elimination, independently of likelihood scale.
Action-descendant evidence can have a policy-dependent normalizer and must instead
be handled by exhaustive search. This does not forbid later information variables
whose chance mechanisms depend on earlier actions.

Every optimised run is checked against [`ExhaustivePolicySearch`](@ref) in the test
suite (SPEC §55.6, §56 item 6).
"""

"""
    DecisionVariableElimination(; order = MinFill(), atol = nothing, stable=false)

Solve an influence diagram by decision variable elimination: chance variables are
summed out and decisions maximised in the strong elimination order (see the module
documentation of `decision_elimination.jl`), with `order` (an `EliminationStrategy`
of BayesianNetworkInference.jl) choosing the order inside each chance block and `atol`
the relative per-row tolerance of the constancy check of the probability potential at each
maximisation. `atol = nothing` (the default) follows the normalisation tolerance the model
is validated with, so a diagram whose rounded CPTs `validate` accepts cannot then be
rejected by a *tighter* constancy check; pass a number to fix the tolerance independently. Returns the maximal expected utility and the recovered strategy of
deterministic policies, with ties broken in favour of the first action label.

`stable=true` runs the same bucket algorithm with exact rational meanings of
the bound scalar data, rounding only the returned Float64 value. This avoids
underflow and signed-utility cancellation without taking logarithms of signed
utilities, and remains exponential in factor width rather than policy count.
It costs more time and memory than ordinary Float64 arithmetic. Accepted
rounded CPTs are not silently normalized; `exact_probability_guards` in the
diagnostics distinguishes exact constancy from mere tolerance acceptance.

With `stable=false` the Float64 run is not trusted when its final evidence mass is not a
normal positive Float64, or when a product it forms from nonzero operands falls below
`floatmin(Float64)`, coming out subnormal or rounding to `0.0` (an underflowing probability
row would otherwise look non-constant in an action). A product with an exactly zero
operand does not count. Either way the same schedule is rerun in exact arithmetic and the
diagnostics record `exact_fallback = true`. So an evidence mass that is not a normal
positive Float64 is not taken as impossibility: `ImpossibleEvidenceError` means
probability exactly zero.

A model may hold tolerated negative entries (in `[-atol, 0)`). With evidence, such an entry
takes part when it lies on a joint state consistent with the evidence whose entries are all
nonzero. When one takes part, `IndeterminatePosteriorError` (ADR 0014) is raised if:

- the evidence mass is not larger than the tolerance budget `(1 + atol)^n - 1`, where
  `atol` is the normalisation tolerance (`optimize`'s `atol`, not this backend's) and `n`
  counts the chance mechanisms and the decisions, as in the network
  [`instantiate`](@ref) builds for a strategy;
- or a posterior cell is negative: a joint state consistent with the evidence has a
  negative probability.

A negative entry that the evidence rules out, or that an exactly zero entry multiplies, does
not count, and a prior (no evidence) is exempt. The exact rerun accepts tolerated entries
and applies the same rule to exact values; `stable=true` does not accept them
(`FactorDomainError`). Whether an entry takes part, and the signs, are decided exactly, by
an elimination of the entries' zero pattern and signs over the run's own schedule. A joint
state fixes every action, so some deterministic strategy reaches it. These are the
conditions under which [`ExhaustivePolicySearch`](@ref) raises the error for some strategy,
and [`expected_utility`](@ref) for that strategy, checked here for every strategy at once.

What the policy tables are (docs/LEAN-JULIA-DISCREPANCIES-2026-09-30.md):

- **Ties.** On every information row the policy picks the first action label among the
  maximizers of the computed scores, compared with `==` (so `-0.0` and `0.0` tie). With
  `stable=true` the scores are exact, and the table is the one the Lean development proves
  unique (`solveOrdered_table`) and independent of the elimination plan
  (`solvePlanOrdered_table_eq`). On the Float64 path rounding can create or break a tie
  that exact arithmetic would see differently, and the summation order follows the order
  in which the utilities are stored; use `stable=true` when a reproducible table matters.
- **Tolerance.** The probability-constancy guard accepts rows equal within the relative
  `atol`. `exact_probability_guards == false` in a stable run means some row was accepted
  only by that tolerance, which is outside the proved contract; an exactly normalised model
  passes with exact equality.
- **Zero-probability rows.** On an information row of probability zero every action is
  optimal. Julia's `sum_out` keeps a utility table there where the Lean model stores zero;
  without evidence, the Lean development proves that this changes no value and no entry on
  a row of positive probability (`solveRepPlanWith_kernel_eq`), and that the whole table is
  the first-label table of Julia's own scores (`solveRepPlanOrdered_table`), which on
  zero-probability rows may differ from the model's.
"""
struct DecisionVariableElimination{O<:EliminationStrategy} <: DecisionBackend
    order::O
    atol::Union{Nothing,Float64}
    stable::Bool
end
function DecisionVariableElimination(order::EliminationStrategy, atol::Real)
    return DecisionVariableElimination(order, Float64(atol), false)
end
function DecisionVariableElimination(; order::EliminationStrategy=MinFill(),
                                     atol::Union{Nothing,Real}=nothing,
                                     stable::Bool=false)
    atol === nothing || _check_probability_tolerance(atol)
    return DecisionVariableElimination(order, atol === nothing ? nothing : Float64(atol),
                                       stable)
end

# Blocks
########

# The blocks I_0, D_1, I_1, ..., D_n, I_n as a vector of `(kind, names)` pairs, kind
# `:chance` or `:decision`; the decision blocks hold the action variable's name.
function _blocks(id::AbstractInfluenceDiagram, ds::Vector{Int})
    n = length(ds)
    first_seen = Dict{Int,Int}()
    for (k, d) in enumerate(ds), v in decision_information(id, d)
        is_decision(id, v) && continue
        haskey(first_seen, v) || (first_seen[v] = k)
    end
    chance = [Int[] for _ in 0:n]
    for v in chance_variables(id)
        push!(chance[get(first_seen, v, n + 1)], v)
    end
    blocks = Pair{Symbol,Vector{Symbol}}[]
    for k in 1:(n + 1)
        push!(blocks, :chance => Symbol[variable_name(id, v) for v in chance[k]])
        k <= n &&
            push!(blocks,
                  :decision => Symbol[variable_name(id, decision_variable(id, ds[k]))])
    end
    return blocks
end

"""
    strong_elimination_order(id::AbstractInfluenceDiagram; strategy = MinFill()) -> Vector{Symbol}
    strong_elimination_order(m::InfluenceDiagramModel; strategy = MinFill())

The variables in the order in which [`DecisionVariableElimination`](@ref) eliminates
them: the blocks `Iₙ, Dₙ, I_{n-1}, ..., D₁, I₀` of the strong order, with the chance
variables inside each block ordered by `strategy` on the interaction graph of the
initial factors (mechanisms and utilities; the actual run reorders each block on the
current factors, so this is the order a run without fill-in would use).
"""
function strong_elimination_order(id::AbstractInfluenceDiagram;
                                  strategy::EliminationStrategy=MinFill())
    ds = decision_order(id)
    blocks = _blocks(id, ds)
    fg = _dummy_factor_graph(id)
    out = Symbol[]
    for (kind, names_) in reverse(blocks)
        if kind == :decision
            append!(out, names_)
        else
            append!(out, _block_order(fg, names_, strategy))
        end
    end
    return out
end

function strong_elimination_order(m::InfluenceDiagramModel; kw...)
    return strong_elimination_order(syntax(m);
                                    kw...)
end

# Factors with unit tables carrying only the scopes of mechanisms and utilities, for
# computing orders without semantics.
function _dummy_factor_graph(id::AbstractInfluenceDiagram)
    fs = Factor{Float64}[]
    ax = v -> FiniteAxis(variable_name(id, v), states(id, v))
    for mech in mechanisms(id)
        vars = unique(vcat(inputs(id, mech), target(id, mech)))
        push!(fs,
              Factor(FiniteAxis[ax(v) for v in vars],
                     ones(Tuple(nstates(id, v) for v in vars))))
    end
    for u in utilities(id)
        vars = utility_scope(id, u)
        push!(fs,
              Factor(FiniteAxis[ax(v) for v in vars],
                     ones(Tuple(nstates(id, v) for v in vars))))
    end
    return FactorGraph(fs)
end

# Order of the variables of `block` that appear in `fg`, keeping everything else.
function _block_order(fg::FactorGraph, block::Vector{Symbol}, strategy::EliminationStrategy)
    present = BayesianNetworkInference.variables(fg)
    inblock = Set(block)
    keep = Symbol[v for v in present if !(v in inblock)]
    length(keep) == length(present) && return Symbol[]
    selected = elimination_order(fg, strategy; keep=keep)
    selected isa AbstractVector{Symbol} ||
        throw(BayesianNetworkInference.ScopeError(:decision_elimination,
                                                  "ordering strategy must return a vector of variable names",
                                                  copy(block)))
    ordered = collect(selected)
    expected = Symbol[v for v in present if v in inblock]
    allunique(ordered) && length(ordered) == length(expected) &&
        Set(ordered) == Set(expected) ||
        throw(BayesianNetworkInference.ScopeError(:decision_elimination,
                                                  "ordering strategy must list each current chance-block variable once and no other variables; expected $(repr(expected)), got $(repr(ordered))",
                                                  union(expected, ordered)))
    return ordered
end

# The run
#########

function _check_dve_structure(id::AbstractInfluenceDiagram, ev)
    missing = no_forgetting_arcs(id)
    if !isempty(missing)
        d = first(missing).first
        throw(IrregularDiagramError(d, Symbol[p.second for p in missing if p.first == d],
                                    :information))
    end
    observed = Set(variable_id(id, x) for x in keys(ev))
    isempty(observed) && return nothing
    graph = variable_graph(id)
    for d in decisions(id)
        seen = Set{Int}()
        pending = Int[decision_variable(id, d)]
        while !isempty(pending)
            v = pop!(pending)
            v in seen && continue
            push!(seen, v)
            append!(pending, outneighbors(graph, v))
        end
        affected = sort!(collect(intersect(seen, observed)))
        isempty(affected) ||
            throw(IrregularDiagramError(decision_name(id, d),
                                        Symbol[variable_name(id, v) for v in affected],
                                        :evidence))
    end
    return nothing
end

"""
    decision_elimination(m::InfluenceDiagramModel; order = MinFill(), atol = nothing, normalization_atol = 1e-8, stable=false) -> DecisionSolution

Run decision variable elimination on `m` (see [`DecisionVariableElimination`](@ref)).
`atol` is the relative per-row tolerance of the constancy check at each
maximisation, and `nothing` (the default) uses `normalization_atol`.
`normalization_atol` is the tolerance of the kernel-normalisation precondition check
(`optimize`'s `atol`), and the tolerance of the budget for tolerated negative entries.
The initial valuations are `(κ_X, 0)` for every chance mechanism (the factor
`κ(x | parents)` of its kernel) and `(1, u_j)` for every utility, each conditioned on
the model's evidence. The diagnostics are a named tuple with the elimination `order`
actually used, the `max_factor_size` of any potential and the `policy_scopes` on
which each recovered policy really depends (a subset of its information set).
`stable=true` selects exact rational bucket arithmetic and adds log evidence,
ordinary mass classification and exact-constancy diagnostics.
"""
function decision_elimination(m::InfluenceDiagramModel;
                              order::EliminationStrategy=MinFill(),
                              atol::Union{Nothing,Real}=nothing,
                              normalization_atol::Real=BayesianNetworks.DEFAULT_ATOL,
                              stable::Bool=false)
    _check_solvable(m; atol=normalization_atol)
    # A row the model was *accepted* with may deviate from summing to one by
    # `normalization_atol`, so it may legitimately vary by about that much across a
    # decision. A constancy check tighter than the tolerance the model passed would reject
    # diagrams `validate` accepts, which is what `atol = nothing` avoids.
    eff = atol === nothing ? Float64(normalization_atol) : Float64(atol)
    _check_probability_tolerance(eff)
    return _run_decision_elimination(m, order, eff, Float64(normalization_atol), stable)
end

# The run of `decision_elimination` after its precondition checks. `eff` is the constancy
# tolerance and `normalization_atol` the kernel-normalisation tolerance the model was
# validated with, which sets the budget for tolerated negative entries. `observer` and
# `sources` are passed to `_decision_elimination`; the certificate's solution profile uses
# them.
function _run_decision_elimination(m::InfluenceDiagramModel, order, eff::Float64,
                                   normalization_atol::Float64, stable::Bool;
                                   observer=nothing, sources=nothing)
    stable &&
        return _decision_elimination(m, order, eff, Rational{BigInt}, observer; sources,
                                     normalization_atol)
    # Evidence mass (ADR 0014): the binary64 run decides nothing when its mass is not a
    # normal positive number, since a positive probability can underflow, nor when a
    # product of nonzero values fell below the normal range (`_checked_product`). Rerun the
    # same bucket schedule in exact rational arithmetic, where only an exact zero raises
    # `ImpossibleEvidenceError`, and record the fallback in the diagnostics.
    try
        return _decision_elimination(m, order, eff, Float64, observer; sources,
                                     normalization_atol)
    catch e
        e isa _UnresolvedDecisionMass || rethrow()
    end
    return _exact_rerun(m, order, eff, normalization_atol; observer, sources)
end

# The exact rerun of an untrusted binary64 run (ADR 0014, ADR 0016): the same bucket
# schedule in `Rational{BigInt}` on the values as bound, with the value rounded once. Unlike
# `stable=true`, which keeps `FactorDomainError` for a negative entry (ADR 0015), it accepts
# tolerated entries and decides them by the rule the binary64 run follows, on exact values
# (`_check_tolerated_entries`), as BayesianNetworks' exact run does.
function _exact_rerun(m::InfluenceDiagramModel, order, eff::Float64,
                      normalization_atol::Float64; observer=nothing, sources=nothing)
    sol = _decision_elimination(m, order, eff, Rational{BigInt}, observer; sources,
                                normalization_atol, tolerated=true)
    return DecisionSolution(sol.expected_utility, sol.strategy,
                            merge(sol.diagnostics, (exact_fallback=true,)))
end

# Whether a mechanism of the model has a tolerated entry in [-atol, 0) (ADR 0007). Only the
# kernels that mechanisms reference count: an intervention leaves the kernel it replaced
# bound under its old reference, where no mechanism reads it.
function _has_negative_entry(m::InfluenceDiagramModel)
    id = syntax(m)
    return any(mechanisms(id)) do mech
        return any(<(0), kernel(m.model, variable_name(id, target(id, mech))).table)
    end
end

# The products of the binary64 run (see `_product`), which also decide whether the run is
# trusted. The rule, which the binary64 runs of BayesianNetworks and
# BayesianNetworkInference follow too: the run is untrusted if its final mass is not a
# normal positive number, or if a product it computes from operands that are all nonzero has
# magnitude below `floatmin(Float64)`, whether the product comes out subnormal or rounds all
# the way to 0.0 (ADR 0014). Such a product has lost significand bits, or all of them, so a
# probability row can look non-constant in an action when it is not, and every value formed
# from it inherits the error. `_run_decision_elimination` repeats an untrusted run exactly.
#
# A product with an exactly zero operand is a structural zero and does not count, wherever
# the zero comes among the operands, so each cell of a combination is judged by all its
# operands at once and the verdict does not depend on the order of multiplication. An
# operand already below `floatmin` marks the run untrusted by itself.
function _checked_product(factors::AbstractVector{Factor{Float64}})
    result = reduce(multiply, factors)
    length(factors) == 1 && return result
    any(f -> any(issubnormal, f.table), factors) && throw(_UnresolvedDecisionMass())
    any(issubnormal, result.table) && throw(_UnresolvedDecisionMass())
    if any(iszero, result.table) && _may_underflow(factors)
        # The cells whose operands are all nonzero, in the result's axis order.
        nonzero = reduce(multiply, [_support(f, !iszero) for f in factors])
        any(i -> nonzero.table[i] && iszero(result.table[i]), eachindex(result.table)) &&
            throw(_UnresolvedDecisionMass())
    end
    return result
end

# Whether a product of nonzero operands can round to 0.0: every partial product, in the
# order `reduce` multiplies, is at least the product of the operands' smallest nonzero
# magnitudes up to that point. A factor with no nonzero entry makes every cell a
# structural zero.
function _may_underflow(factors::AbstractVector{Factor{Float64}})
    bound = 1.0
    for f in factors
        smallest = minimum((abs(x) for x in f.table if !iszero(x)); init=Inf)
        isinf(smallest) && return false
        bound *= smallest
        bound < floatmin(Float64) && return true
    end
    return false
end

# ADR 0014 decision 4 for a run with evidence, a tolerated negative entry among the
# conditioned chance factors `conditioned`, and evidence mass `pe`: a trusted binary64 run,
# or the exact rerun on exact values. `ExhaustivePolicySearch` and `expected_utility`
# evaluate a strategy on its instantiated network, where `BayesianNetworks.marginal` applies
# this rule to the posterior of all the variables. A negative entry takes part when it lies
# on a joint state consistent with the evidence whose entries are all nonzero; one that the
# evidence rules out, or that an exactly zero entry multiplies, does not. When one takes
# part, the posterior is indeterminate if the evidence mass is not larger than the budget
# `(1 + atol)^n - 1`, or if a posterior cell is negative. A joint state fixes every action,
# so some deterministic strategy reaches it, and the run raises when some strategy would.
# `atol` is the normalisation tolerance, and `n` counts the mechanisms of an instantiated
# network: one per chance variable and one policy per decision. The evidence has no action
# among its ancestors, so its mass does not depend on the strategy, except through the
# kernels' normalisation tolerance.
function _check_tolerated_entries(pe, ev, conditioned, atol, n, order)
    _takes_part(conditioned, order) || return nothing
    budget = BayesianNetworks._joint_atol(atol, n)
    if !(pe > budget)
        pe < floatmin(Float64) &&
            throw(BayesianNetworks.IndeterminatePosteriorError(copy(ev),
                                                               "a tolerated negative entry lies on a configuration consistent with evidence whose mass is below binary64's normal range"))
        mass = pe isa Float64 ? pe : _nearest_binary64(pe)
        throw(BayesianNetworks.IndeterminatePosteriorError(copy(ev),
                                                           "the evidence mass $(mass) is within the tolerance budget $(budget) of zero"))
    end
    _negative_product(conditioned, order) &&
        throw(BayesianNetworks.IndeterminatePosteriorError(copy(ev),
                                                           "a posterior cell is negative: a tolerated negative entry gives a joint state consistent with the evidence a negative probability"))
    return nothing
end

# Support eliminations: whether a tolerated negative entry takes part, and whether some joint
# state has a negative product, decided exactly from the zero pattern and the signs of the
# entries. They never enumerate joint states. Each factor becomes a pair of Boolean factors
# that mark, for its states, two properties of a product; a product of pairs follows the
# signs, and eliminating a variable asks whether some state of it has the property
# (`maximize` of Booleans is `or`). Ranging over every action value is ranging over the
# strategies. `order` is the run's own schedule, so no table is larger than the run's.
#
# `_takes_part`: all entries nonzero, and all entries nonzero with one of them negative.
function _takes_part(factors, order)
    pairs = [(_support(f, !iszero), _support(f, <(0))) for f in factors]
    function product((a1, h1), (a2, h2))
        return (multiply(a1, a2),
                _or(multiply(h1, a2), multiply(a1, h2)))
    end
    return only(last(_eliminate_support(pairs, order, product)).table)
end

# `_negative_product`: all entries nonzero with an even number of them negative, and with an
# odd number of them negative.
function _negative_product(factors, order)
    pairs = [(_support(f, >(0)), _support(f, <(0))) for f in factors]
    function product((e1, o1), (e2, o2))
        return (_or(multiply(e1, e2), multiply(o1, o2)),
                _or(multiply(e1, o2), multiply(o1, e2)))
    end
    return only(last(_eliminate_support(pairs, order, product)).table)
end

_support(f::Factor, test) = Factor(f.vars, f.axes, map(test, f.table))
# Two Boolean factors over the same scope in the same order.
_or(f::Factor{Bool}, g::Factor{Bool}) = Factor(f.vars, f.axes, map(|, f.table, g.table))

function _eliminate_support(pairs, order, product)
    remaining = collect(pairs)
    # The run eliminates every variable of its factors; any other comes last.
    order = collect(order)
    for p in pairs, x in first(p).vars
        x in order || push!(order, x)
    end
    for x in order
        touching = filter(p -> x in first(p).vars, remaining)
        isempty(touching) && continue
        filter!(p -> !(x in first(p).vars), remaining)
        u, v = reduce(product, touching)
        push!(remaining, (maximize(u, x), maximize(v, x)))
    end
    return reduce(product, remaining)
end

# `sources`, when given, is called as `sources(:chance, name)` and `sources(:utility, name)`
# and returns the initial factor to use instead of the bound kernel's or utility's
# (`nothing` keeps the bound one). The DVE certificate passes the exact tables it exports.
# `atol` is the constancy tolerance; `normalization_atol` sets the budget for tolerated
# negative entries. An exact run refuses a negative entry with `FactorDomainError`, as
# `stable=true` documents (ADR 0015), unless `tolerated` (the exact rerun of an untrusted
# binary64 run, `_exact_rerun`).
function _decision_elimination(m::InfluenceDiagramModel, order, atol, ::Type{T},
                               observer=nothing; sources=nothing,
                               normalization_atol::Real, tolerated::Bool=false) where {T}
    stable = T == Rational{BigInt}
    # The binary64 run checks every product it forms for underflow.
    product = stable ? _product : _checked_product
    id = syntax(m)
    bm = m.model
    ev = evidence(m)
    _check_dve_structure(id, ev)
    vals = Valuation{T}[]
    # The chance factors conditioned on the evidence, for the tolerated-entry rule.
    conditioned = Factor{T}[]
    for mech in mechanisms(id)
        x = variable_name(id, target(id, mech))
        ps = Symbol[variable_name(id, p) for p in inputs(id, mech)]
        bound_kernel = kernel(bm, x)
        given = sources === nothing ? nothing : sources(:chance, x)
        factor = given === nothing ? Factor(bound_kernel, ps, x) : given
        if stable
            bad = findfirst(value -> !(isfinite(value) && (tolerated || value >= 0)),
                            factor.table)
            bad === nothing ||
                throw(BayesianNetworkInference.FactorDomainError(:stable_decision_elimination,
                                                                 copy(factor.vars),
                                                                 Tuple(bad),
                                                                 factor.table[bad]))
        end
        probability = _convert(T, factor)
        observer === nothing || observer(:input,
                                         (kind="chance", name=x, parents=ps,
                                          source=bound_kernel, compiled=factor,
                                          value=Valuation(probability)))
        sliced = condition(probability, ev)
        push!(conditioned, sliced)
        push!(vals, Valuation(sliced))
    end
    for (name, u) in m.utilities
        given = sources === nothing ? nothing : sources(:utility, name)
        f = given === nothing ? utility_factor(u, _utility_axes(m, utility_id(id, name))) :
            given
        # In both arithmetics: a NaN or infinite utility has no expected value, and
        # `expected_utility` rejects it too (docs/LEAN-JULIA-DISCREPANCIES-2026-09-30.md, 2).
        all(isfinite, f.table) ||
            throw(UtilityScopeError(name, :value, "finite utility entries", f.table))
        initial = Valuation(unit_factor(T), _convert(T, f))
        observer === nothing || observer(:input,
                                         (kind="utility", name=name, parents=Symbol[],
                                          source=u, compiled=f, value=initial))
        push!(vals, Valuation(initial.φ, condition(initial.ψ, ev)))
    end
    observer === nothing || observer(:conditioned, vals)
    ds = decision_order(id)
    blocks = _blocks(id, ds)
    elim = Symbol[]
    max_size = 0
    policy_scopes = Dict{Symbol,Vector{Symbol}}()
    ps = Dict{Symbol,AbstractPolicy}()
    exact_guards = true
    probability_atol = stable ? Rational{BigInt}(atol) : atol
    for (kind, names_) in reverse(blocks)
        if kind == :chance
            # Only the scopes matter here: the graph orders the block. It holds signed
            # utilities (the psi potentials), so it is not a measure, and it is built with
            # the unchecked inner constructor, which skips the entry check a
            # FactorGraph of probabilities gets.
            pots = vcat([v.φ for v in vals], [v.ψ for v in vals])
            fg = FactorGraph{T}(pots, fill(nothing, length(pots)))
            for x in _block_order(fg, names_, order)
                touching = Valuation{T}[]
                rest = Valuation{T}[]
                for v in vals
                    push!(x in scope(v) ? touching : rest, v)
                end
                combined = _combine(touching, product)
                max_size = max(max_size, length(combined.φ.table), length(combined.ψ.table))
                reduced = _sum_out(combined, x, product)
                if observer !== nothing
                    observer(:chance,
                             (variable=x, inputs=findall(v -> x in scope(v), vals),
                              combined=combined, result=reduced))
                end
                push!(rest, reduced)
                vals = rest
                push!(elim, x)
            end
        else
            a = only(names_)
            d = decision_id(id, a)
            dname = decision_name(id, d)
            info = _information_axes(m, d)
            action = _action_axis(m, d)
            touching = Valuation{T}[]
            rest = Valuation{T}[]
            for v in vals
                push!(a in scope(v) ? touching : rest, v)
            end
            if isempty(touching)
                ps[dname] = DeterministicPolicy(dname, info, action,
                                                (labels...) -> first(action.labels))
                policy_scopes[dname] = Symbol[]
                observer === nothing || observer(:inactive,
                                                 (variable=a, decision=dname, action=first(action.labels)))
            else
                # A probability row that underflowed stops a binary64 run here, before
                # `max_out` would compare its rounded entries.
                combined = _combine(touching, product)
                max_size = max(max_size, length(combined.φ.table), length(combined.ψ.table))
                if stable && a in combined.φ.vars
                    position = findfirst(==(a), combined.φ.vars)
                    exact_guards &= maximum(combined.φ.table; dims=position) ==
                                    minimum(combined.φ.table; dims=position)
                end
                reduced, table, pscope = max_out(combined, a; atol=probability_atol)
                info_names = [ax.name for ax in info]
                extra = setdiff(pscope, info_names)
                isempty(extra) || throw(IrregularDiagramError(dname, extra, :information))
                pos = Int[findfirst(==(x), info_names) for x in pscope]
                ps[dname] = DeterministicPolicy(dname, info, action,
                                                (labels...) -> table[ntuple(j -> label_index(info[pos[j]],
                                                                                             labels[pos[j]]),
                                                                            length(pos))...])
                policy_scopes[dname] = pscope
                if observer !== nothing
                    observer(:decision,
                             (variable=a, decision=dname,
                              inputs=findall(v -> a in scope(v), vals),
                              combined=combined, result=reduced, policy=table,
                              policy_scope=pscope))
                end
                push!(rest, reduced)
                vals = rest
            end
            push!(elim, a)
        end
    end
    final = _combine(vals, product)
    observer === nothing || observer(:final, final)
    isempty(scope(final)) || throw(UneliminatedVariablesError(collect(scope(final))))
    pe = only(final.φ.table)
    stable || (isfinite(pe) && pe >= floatmin(Float64)) || throw(_UnresolvedDecisionMass())
    # Tolerated negative entries (ADR 0014 decision 4), in a trusted binary64 run and in the
    # exact rerun alike. A prior (no evidence) is exempt: it is the model's own law.
    !isempty(ev) && any(f -> any(<(0), f.table), conditioned) &&
        _check_tolerated_entries(pe, ev, conditioned, normalization_atol,
                                 length(variables(id)), elim)
    # Exact arithmetic: only an exact zero reaches this.
    (isempty(ev) || pe > 0) ||
        throw(BayesianNetworks.ImpossibleEvidenceError(copy(ev)))
    meu = only(final.ψ.table)
    if stable
        value = _nearest_binary64(meu)
        isfinite(value) ||
            throw(UtilityScopeError(:total, :value, "finite representable expected utility",
                                    value))
        log_mass = _rational_log(pe)
        ordinary_mass = _nearest_binary64(pe)
        status = iszero(pe) ? :zero :
                 iszero(ordinary_mass) ? :underflow :
                 isinf(ordinary_mass) ? :overflow : :finite
        return DecisionSolution(value, Strategy(ps),
                                (order=elim, max_factor_size=max_size,
                                 policy_scopes=policy_scopes,
                                 evidence_probability=ordinary_mass,
                                 log_evidence_probability=log_mass,
                                 mass_status=status, arithmetic=:exact_rational,
                                 exact_probability_guards=exact_guards))
    end
    return DecisionSolution(meu, Strategy(ps),
                            (order=elim, max_factor_size=max_size,
                             policy_scopes=policy_scopes, evidence_probability=pe))
end

function optimize(m::InfluenceDiagramModel, b::DecisionVariableElimination;
                  atol::Real=BayesianNetworks.DEFAULT_ATOL)
    return decision_elimination(m; order=b.order, atol=b.atol, normalization_atol=atol,
                                stable=b.stable)
end

# Value of information
######################

"""
    expected_value_of_information(m::InfluenceDiagramModel, variable, decision; backend = DecisionVariableElimination()) -> Float64

`EVI(X -> D) = max_σ EU(ID + info(X, D)) - max_σ EU(ID)` (SPEC §35): the gain in
maximal expected utility from observing `variable` before `decision`
([`with_information`](@ref)). This is information value theory in the sense of
[Howard1966](@cite) and [Raiffa1968](@cite). It is never negative (SPEC §55.7, the Lean theorem
`exists_strategy_enlarged_eq`) and zero when the variable is already observed. Throws
[`InvalidInformationSetError`](@ref) when the variable is not available before the
decision.

`info(X, D)` is taken under perfect recall: a variable observed before `D` is still
known at every later decision, so [`with_information`](@ref) propagates the arc and the
enlarged diagram still has no-forgetting. Both optimisations therefore work with the
default backend on sequential diagrams; for example
`expected_value_of_information(two_stage_model(), :Oil, :Test)` is 29.0 (it is 24.0 with
`no_forgetting = false`, where the later decision has to be signalled through the test).
"""
function expected_value_of_information(m::InfluenceDiagramModel, x, d;
                                       backend::DecisionBackend=DecisionVariableElimination())
    id = syntax(m)
    did = _decision_id(id, d)
    v = _variable_id(id, x)
    v in decision_information(id, did) && return 0.0
    base = optimize(m, backend).expected_utility
    enlarged = optimize(with_information(m, did, v), backend).expected_utility
    return enlarged - base
end

"""
    admissible_information(id::AbstractInfluenceDiagram, decision) -> Vector{Int}
    admissible_information(m::InfluenceDiagramModel, decision)

Part ids of the chance variables that could be added to the information set of
`decision`: those not already in it and not downstream of its action in
[`information_graph`](@ref), so that adding the arc keeps the information sets
consistent (the graph acyclic).
"""
function admissible_information(id::AbstractInfluenceDiagram, d)
    did = _decision_id(id, d)
    a = decision_variable(id, did)
    down = Set(_reachable(information_graph(id), a))
    known = Set(decision_information(id, did))
    return Int[v for v in chance_variables(id) if !(v in down) && !(v in known) && v != a]
end
admissible_information(m::InfluenceDiagramModel, d) = admissible_information(syntax(m), d)

"""
    expected_value_of_perfect_information(m::InfluenceDiagramModel, decision; variables = admissible_information(m, decision), backend = DecisionVariableElimination()) -> Float64

The gain in maximal expected utility from observing all of `variables` (by default
every chance variable that can be observed before `decision`, see
[`admissible_information`](@ref)) before the decision: the expected value of perfect
information of [Howard1966](@cite) and [Raiffa1968](@cite), an upper bound on what any
single observation in [`expected_value_of_information`](@ref) can be worth. Each arc is added with
[`with_information`](@ref), which propagates it to the later decisions, so the enlarged
diagram keeps no-forgetting and the default backend solves it; on a diagram that already
forgets, both optimisations throw [`IrregularDiagramError`](@ref) and either
[`with_no_forgetting`](@ref) or [`ExhaustivePolicySearch`](@ref) is needed.
"""
function expected_value_of_perfect_information(m::InfluenceDiagramModel, d;
                                               variables=admissible_information(m, d),
                                               backend::DecisionBackend=DecisionVariableElimination())
    id = syntax(m)
    did = _decision_id(id, d)
    base = optimize(m, backend).expected_utility
    enlarged = m
    for v in variables
        vid = _variable_id(id, v)
        vid in decision_information(syntax(enlarged), did) && continue
        enlarged = with_information(enlarged, did, vid)
    end
    return optimize(enlarged, backend).expected_utility - base
end
