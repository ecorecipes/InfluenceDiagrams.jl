"""
Expected utility (SPEC §30, §31; Proposition 6). Utilities aggregate additively,
`U(x) = Σ_j u_j(x_{scope(u_j)})`, and the expected utility of a strategy is
`EU(σ) = Σ_x P_σ(x) U(x)` over the joint law of the instantiated network. The
reference algorithm is the one of SPEC §31: instantiate, enumerate the joint by brute
force, evaluate the total utility of every assignment, take the expectation. It is an
oracle for small models, not a scalable backend.
"""

# Utilities and their axes, from an instantiated `BayesModel` or a model.
function _utilities_of(bm::BayesModel)
    haskey(extras(bm), :utilities) ||
        throw(ArgumentError("the model carries no utilities in extras(bm)[:utilities]; use instantiate on an InfluenceDiagramModel"))
    return extras(bm)[:utilities]::Dict{Symbol,AbstractUtility}
end

function _scope_axes(bm::BayesModel, u::AbstractUtility)
    return FiniteAxis[only(factors(space(bm, x))) for x in scope(u)]
end

"""
    total_utility(m::InfluenceDiagramModel, assignment) -> Float64
    total_utility(bn::BayesModel, assignment) -> Float64
    total_utility(utilities::AbstractDict{Symbol,<:AbstractUtility}, assignment) -> Float64

The additive total utility `Σ_j u_j(x)` of an assignment (a dictionary or a list of
`:X => :x` pairs covering every scope variable), over the bound utilities of a model,
of an instantiated network, or of a dictionary of utilities.
"""
function total_utility(us::AbstractDict{Symbol,<:AbstractUtility},
                       assignment::AbstractDict{Symbol,Symbol})
    return sum((utility_value(u, assignment) for u in values(us)); init=0.0)
end

function total_utility(us::AbstractDict{Symbol,<:AbstractUtility},
                       assignment::AbstractVector{<:Pair{Symbol,Symbol}})
    return total_utility(us, Dict{Symbol,Symbol}(assignment))
end

total_utility(m::InfluenceDiagramModel, assignment) = total_utility(m.utilities, assignment)
total_utility(bm::BayesModel, assignment) = total_utility(_utilities_of(bm), assignment)

# Σ_x P(x) U(x) over a joint table with the given axis order.
function _expectation(J::JointTable, us::AbstractDict{Symbol,<:AbstractUtility},
                      axes_of)
    pos = Dict{Symbol,Int}(x => i for (i, x) in enumerate(J.variables))
    tables = Tuple{Array{Float64},Vector{Int}}[]
    for (name, u) in us
        axes = axes_of(u)
        for a in axes
            haskey(pos, a.name) || throw(UnknownVariableError(a.name))
            J.states[pos[a.name]] == a.labels ||
                throw(UtilityScopeError(name, :scope, J.states[pos[a.name]], a.labels))
        end
        table = utility_table(u, axes)
        # Checked on every entry, reachable or not: a NaN or infinite utility makes the model
        # invalid data, as in the stable path and the optimisers.
        all(isfinite, table) ||
            throw(UtilityScopeError(name, :value, "finite utility entries", table))
        push!(tables, (table, Int[pos[a.name] for a in axes]))
    end
    eu = 0.0
    for ci in CartesianIndices(J.table)
        p = J.table[ci]
        p == 0 && continue
        u = 0.0
        for (tab, ax) in tables
            u += tab[ntuple(j -> ci[ax[j]], length(ax))...]
        end
        eu += p * u
    end
    return eu
end

function _compensated_sum(values)
    total, correction = 0.0, 0.0
    for value in values
        combined = total + value
        correction += abs(total) >= abs(value) ? (total - combined) + value :
                      (value - combined) + total
        total = combined
    end
    return total + correction
end

function _stable_expected_utility(bm::BayesModel, us; max_states, atol)
    count = prod((BigInt(nstates(syntax(bm), name)) for name in variable_names(syntax(bm)));
                 init=big(1))
    count <= max_states ||
        throw(ModelTooLargeError(Int(min(count, typemax(Int))), max_states))
    graph = BayesianNetworkInference.compile(bm; atol)
    observed = evidence(bm)
    BayesianNetworkInference.log_evidence_probability(graph; evidence=observed) == -Inf &&
        throw(BayesianNetworks.ImpossibleEvidenceError(copy(observed)))
    terms = Float64[]
    for name in sort!(collect(keys(us)))
        utility = us[name]
        factor = utility_factor(utility, _scope_axes(bm, utility))
        all(isfinite, factor.table) ||
            throw(UtilityScopeError(name, :value, "finite utility entries", factor.table))
        factor = condition(factor, observed)
        if isempty(factor.vars)
            push!(terms, factor.table[])
            continue
        end
        posterior, _ = BayesianNetworkInference.infer(graph, factor.vars; evidence=observed,
                                                      backend=BayesianNetworkInference.LogVariableElimination())
        scale = maximum(abs, factor.table)
        value = iszero(scale) ? 0.0 :
                scale * _compensated_sum(p * (u / scale)
                                         for (p, u) in zip(posterior.table, factor.table))
        push!(terms, value)
    end
    scale = maximum(abs, terms; init=0.0)
    result = iszero(scale) ? 0.0 :
             scale * _compensated_sum(value / scale for value in terms)
    isfinite(result) ||
        throw(UtilityScopeError(:total, :value, "finite representable expected utility",
                                result))
    return result
end

"""
    expected_utility(bn::BayesModel; max_states = 1_000_000, atol = DEFAULT_ATOL, stable=false) -> Float64

The expected total utility of an instantiated network (as returned by
[`instantiate`](@ref), which stores the utilities in `extras(bn)[:utilities]`) by
brute force: `Σ_x P(x | e) U(x)` over the joint law conditioned on the network's
evidence (`joint_distribution` / `marginal` of BayesianNetworks.jl).

With `stable=true`, compute each utility's conditional marginal using centered
log-domain variable elimination, accumulate its expectation with scaled
compensated summation, then add the separate expectations. This avoids losing
a small additive utility before large per-world terms cancel. The original
state-count cap and validation tolerance still apply. This opt-in path does not
assert a universal floating-point error bound.
"""
function expected_utility(bm::BayesModel; max_states::Integer=1_000_000,
                          atol::Real=BayesianNetworks.DEFAULT_ATOL, stable::Bool=false)
    us = _utilities_of(bm)
    stable && return _stable_expected_utility(bm, us; max_states, atol)
    vars = variable_names(syntax(bm))
    J = if isempty(evidence(bm))
        JointTable(joint_distribution(bm; max_states=max_states, atol=atol))
    else
        JointTable(marginal(bm, vars; evidence=evidence(bm), max_states=max_states,
                            atol=atol))
    end
    return _expectation(J, us, u -> _scope_axes(bm, u))
end

"""
    expected_utility(m::InfluenceDiagramModel, strategy = strategy(m); max_states = 1_000_000, atol = DEFAULT_ATOL, stable=false) -> Float64
    expected_utility(m, :D => :a; kwargs...)
    expected_utility(m, [:D => :a, :E => :b]; kwargs...)

The expected utility `EU(σ) = E_{P_σ}[U]` of the strategy (SPEC §31, Proposition 6):
[`instantiate`](@ref) the strategy, enumerate the joint law, evaluate the total utility
of every assignment and take the expectation. Given `:D => :a` pairs, the decisions are
first fixed with [`fix_decision`](@ref) (the expected utility of a fixed action, SPEC §46
analysis 1). Throws [`IncompleteStrategyError`](@ref) when a decision has no policy, and
[`EvidenceOnActionError`](@ref) when the model carries evidence on an action variable.
`atol` is forwarded through [`instantiate`](@ref)'s validation and the brute-force
joint or conditional evaluation, so rounded models use the same normalization
tolerance throughout both oracle and optimized paths.
`stable=true` selects per-utility log-domain marginals and compensated accumulation;
the default retains the original reference arithmetic for reproducibility.
"""
function expected_utility(m::InfluenceDiagramModel, σ::Strategy=m.strategy;
                          max_states::Integer=1_000_000,
                          atol::Real=BayesianNetworks.DEFAULT_ATOL, stable::Bool=false)
    _check_evidence_variables(syntax(m), evidence(m))
    return expected_utility(instantiate(m, σ; atol=atol); max_states=max_states, atol=atol,
                            stable)
end

function expected_utility(m::InfluenceDiagramModel, f::Pair{Symbol,Symbol}; kw...)
    return expected_utility(fix_decision(m, f); kw...)
end

function expected_utility(m::InfluenceDiagramModel,
                          fs::AbstractVector{<:Pair{Symbol,Symbol}};
                          kw...)
    return expected_utility(fix_decision(m, fs); kw...)
end
