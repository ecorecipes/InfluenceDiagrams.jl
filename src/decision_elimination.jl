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

With `stable=false` an evidence mass that is not a normal positive Float64 is not
taken as impossibility: the same schedule is rerun in exact arithmetic and the
diagnostics record `exact_fallback = true`. `ImpossibleEvidenceError` means
probability exactly zero. A model with tolerated negative entries whose evidence mass
is within the tolerance budget raises `IndeterminatePosteriorError` (ADR 0014).
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
    decision_elimination(m::InfluenceDiagramModel; order = MinFill(), atol = 1e-9, normalization_atol = 1e-8, stable=false) -> DecisionSolution

Run decision variable elimination on `m` (see [`DecisionVariableElimination`](@ref)).
`atol` is the relative per-row tolerance of the constancy check at each
maximisation; `normalization_atol` is the tolerance of the kernel-normalisation
precondition check (`optimize`'s `atol`).
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
    stable && return _decision_elimination(m, order, eff, Rational{BigInt})
    # Evidence mass (ADR 0014): the binary64 run decides nothing when its mass is not a
    # normal positive number, since a positive probability can underflow. Rerun the same
    # bucket schedule in exact rational arithmetic, where only an exact zero raises
    # `ImpossibleEvidenceError`, and record the fallback in the diagnostics.
    try
        return _decision_elimination(m, order, eff, Float64)
    catch e
        e isa _UnresolvedDecisionMass || rethrow()
    end
    _has_negative_entry(m) &&
        throw(BayesianNetworks.IndeterminatePosteriorError(copy(evidence(m)),
                                                           "the binary64 evidence mass is below the normal range and the model has a tolerated negative entry, which exact arithmetic does not accept"))
    sol = _decision_elimination(m, order, eff, Rational{BigInt})
    return DecisionSolution(sol.expected_utility, sol.strategy,
                            merge(sol.diagnostics, (exact_fallback=true,)))
end

# Whether a bound chance kernel has a tolerated entry in [-atol, 0) (ADR 0007).
function _has_negative_entry(m::InfluenceDiagramModel)
    return any(k -> k isa FiniteKernel && any(<(0), k.table), values(kernels(m.model)))
end

function _decision_elimination(m::InfluenceDiagramModel, order, atol, ::Type{T},
                               observer=nothing) where {T}
    stable = T == Rational{BigInt}
    id = syntax(m)
    bm = m.model
    ev = evidence(m)
    _check_dve_structure(id, ev)
    vals = Valuation{T}[]
    for mech in mechanisms(id)
        x = variable_name(id, target(id, mech))
        ps = Symbol[variable_name(id, p) for p in inputs(id, mech)]
        bound_kernel = kernel(bm, x)
        factor = Factor(bound_kernel, ps, x)
        if stable && !all(value -> isfinite(value) && value >= 0, factor.table)
            throw(BayesianNetworkInference.ScopeError(:decision_elimination,
                                                      "stable probabilities must be finite and nonnegative",
                                                      factor.vars))
        end
        probability = _convert(T, factor)
        observer === nothing || observer(:input,
                                         (kind="chance", name=x, parents=ps,
                                          source=bound_kernel, compiled=factor,
                                          value=Valuation(probability)))
        push!(vals, Valuation(condition(probability, ev)))
    end
    for (name, u) in m.utilities
        f = utility_factor(u, _utility_axes(m, utility_id(id, name)))
        stable && !all(isfinite, f.table) &&
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
                combined = combine(touching)
                max_size = max(max_size, length(combined.φ.table), length(combined.ψ.table))
                reduced = sum_out(combined, x)
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
                combined = combine(touching)
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
    final = combine(vals)
    observer === nothing || observer(:final, final)
    isempty(scope(final)) || throw(UneliminatedVariablesError(collect(scope(final))))
    pe = only(final.φ.table)
    if !stable && !isempty(ev)
        (isfinite(pe) && pe >= floatmin(Float64)) || throw(_UnresolvedDecisionMass())
        if _has_negative_entry(m)
            budget = BayesianNetworks._joint_atol(atol, length(mechanisms(id)))
            pe > budget ||
                throw(BayesianNetworks.IndeterminatePosteriorError(copy(ev),
                                                                   "the evidence mass $(pe) is within the tolerance budget $(budget) of zero"))
        end
    end
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
