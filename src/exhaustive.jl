"""
Policy optimisation by exhaustive enumeration of deterministic strategies (SPEC §32):
the correctness oracle against which [`DecisionVariableElimination`](@ref) is tested
(SPEC §55.6, §56 item 6). The number of strategies is the product over decisions of
`|A_D|^{|I_D|}`, so this is only for tiny diagrams.
"""

"""
    DecisionBackend

Abstract supertype of the backends accepted by [`optimize`](@ref):
[`ExhaustivePolicySearch`](@ref) and [`DecisionVariableElimination`](@ref).
"""
abstract type DecisionBackend end

"""
    ExhaustivePolicySearch(; max_policies = 1_000_000, brute_force = false, stable = false)

Enumerate every deterministic strategy (the product over decisions of
[`all_deterministic_policies`](@ref)) and return the best one; the first strategy in
enumeration order attaining the maximum is returned when several tie. Throws
[`PolicySearchTooLargeError`](@ref) when there are more than `max_policies` strategies.

By default each strategy is scored from a value table computed once by enumerating
the joint states of all variables with the actions left free: `Σ_x P_chance(x) U(x)`
and `Σ_x P_chance(x)` accumulated over the information and action variables, so that a
strategy's expected utility is the ratio of the two sums over the assignments it
selects (the denominator matters only with evidence). With `brute_force = true` every
strategy is instead evaluated through [`instantiate`](@ref) and
[`expected_utility`](@ref), the reference algorithm of SPEC §31, which is much slower.
`stable=true` also evaluates strategies individually, using the opt-in stable
expected-utility path instead of the value-table shortcut. It is deliberately
slower and avoids merging small utility terms before cancellation.
Strategies under which the evidence is impossible are excluded. If no strategy
supports the evidence, throw `BayesianNetworks.ImpossibleEvidenceError`: probability
exactly zero. When a value-table product falls outside the normal Float64 range, the
table cannot tell an underflow from a zero, so the search falls back to scoring each
strategy individually and records `exact_fallback = true` in the diagnostics (ADR 0014).
"""
struct ExhaustivePolicySearch <: DecisionBackend
    max_policies::Int
    brute_force::Bool
    stable::Bool
end
function ExhaustivePolicySearch(max_policies::Int, brute_force::Bool)
    return ExhaustivePolicySearch(max_policies, brute_force, false)
end
function ExhaustivePolicySearch(; max_policies::Integer=1_000_000, brute_force::Bool=false,
                                stable::Bool=false)
    return ExhaustivePolicySearch(Int(max_policies), brute_force, stable)
end

"""
    DecisionSolution(expected_utility, strategy, diagnostics)

The result of [`optimize`](@ref): the maximal expected utility, an optimal
[`Strategy`](@ref) of deterministic policies, and backend-specific `diagnostics` (a
named tuple: the number of strategies enumerated for the exhaustive backend; the
elimination order, largest factor and recovered policies' scopes for decision variable
elimination).
"""
struct DecisionSolution
    expected_utility::Float64
    strategy::Strategy
    diagnostics::Any
end

function Base.show(io::IO, s::DecisionSolution)
    return print(io, "DecisionSolution(expected_utility = ", s.expected_utility, ", ",
                 s.strategy, ")")
end

"""
    optimize(m::InfluenceDiagramModel; backend = DecisionVariableElimination()) -> DecisionSolution
    optimize(m, backend)

Solve `σ* = argmax_σ EU(σ)` (SPEC §32) with the given backend. The model must be
closed, with every chance kernel and every utility bound, and must carry no evidence on
an action variable ([`EvidenceOnActionError`](@ref): a decision is fixed with
[`fix_decision`](@ref), not observed); its current strategy is ignored (the solution's
strategy can be installed with [`set_policy`](@ref)). `atol` is the
kernel-normalisation tolerance of the precondition check, to be matched to the `atol` a
model read from a file was parsed with; the tolerance of
[`DecisionVariableElimination`](@ref)'s own constancy check is a field of the backend.
"""
function optimize(m::InfluenceDiagramModel;
                  backend::DecisionBackend=DecisionVariableElimination(),
                  atol::Real=BayesianNetworks.DEFAULT_ATOL, kw...)
    return optimize(m, backend; atol=atol, kw...)
end

# Preconditions of both backends: closed, uniquely named, fully bound, and no evidence
# on an action variable (an action has no chance mechanism, so there is nothing to
# condition; `validate(::InfluenceDiagramModel)` throws `EvidenceOnActionError`).
# `atol` is the kernel-normalisation tolerance, which must match the one a model read
# from a file was parsed with.
function _check_solvable(m::InfluenceDiagramModel;
                         atol::Real=BayesianNetworks.DEFAULT_ATOL)
    validate(m; closed=true, unique_names=true, semantics=true, atol=atol)
    return nothing
end

# The value tables of the exhaustive backend: numerator Σ_x P_c(x) U(x) and
# denominator Σ_x P_c(x), both accumulated over the `keep` variables (information and
# action variables), with x ranging over the joint states consistent with the evidence.
function _value_tables(m::InfluenceDiagramModel, keep::Vector{Symbol};
                       max_states::Integer)
    id = syntax(m)
    bm = m.model
    vars = variable_names(id)
    n = prod(BigInt[nstates(id, x) for x in vars]; init=big(1))
    n <= max_states || throw(ModelTooLargeError(Int(min(n, typemax(Int))), max_states))
    pos = Dict{Symbol,Int}(x => i for (i, x) in enumerate(vars))
    dims = Tuple(nstates(id, x) for x in vars)
    factors_ = Tuple{Array{Float64},Vector{Int}}[]
    for mech in mechanisms(id)
        x = variable_name(id, target(id, mech))
        k = kernel(bm, x)
        push!(factors_,
              (convert(Array{Float64}, k.table),
               Int[pos[x]; Int[pos[variable_name(id, p)] for p in inputs(id, mech)]]))
    end
    utils = Tuple{Array{Float64},Vector{Int}}[]
    for (name, u) in m.utilities
        axes = _utility_axes(m, utility_id(id, name))
        push!(utils, (utility_table(u, axes), Int[pos[a.name] for a in axes]))
    end
    ev = [(pos[x], label_index(only(factors(space(bm, x))), s)) for (x, s) in evidence(m)]
    kpos = Int[pos[x] for x in keep]
    kdims = Tuple(dims[i] for i in kpos)
    N = zeros(Float64, kdims)
    Z = zeros(Float64, kdims)
    # Whether a product of nonzero entries fell below binary64's normal range: then a
    # strategy's zero mass may be an underflow rather than an exact zero (ADR 0014). A
    # negative product comes from a tolerated negative entry.
    unreliable = false
    for ci in CartesianIndices(dims)
        all(e -> ci[e[1]] == e[2], ev) || continue
        p = 1.0
        exact_zero = false
        for (tab, ax) in factors_
            x = tab[ntuple(j -> ci[ax[j]], length(ax))...]
            if x == 0
                exact_zero = true
                break
            end
            p *= x
        end
        exact_zero && continue
        (p >= floatmin(Float64) && isfinite(p)) || (unreliable = true)
        p == 0 && continue
        u = 0.0
        for (tab, ax) in utils
            u += tab[ntuple(j -> ci[ax[j]], length(ax))...]
        end
        k = CartesianIndex(ntuple(j -> ci[kpos[j]], length(kpos)))
        N[k] += p * u
        Z[k] += p
    end
    return N, Z, unreliable
end

function optimize(m::InfluenceDiagramModel, b::ExhaustivePolicySearch;
                  max_states::Integer=1_000_000,
                  atol::Real=BayesianNetworks.DEFAULT_ATOL)
    _check_solvable(m; atol=atol)
    id = syntax(m)
    ds = decision_order(id)
    names_ = Symbol[decision_name(id, d) for d in ds]
    total = prod(BigInt[n_deterministic_policies(m, d) for d in ds]; init=BigInt(1))
    total <= b.max_policies || throw(PolicySearchTooLargeError(total, b.max_policies))
    per_decision = [all_deterministic_policies(m, d) for d in ds]
    best = -Inf
    best_strategy = Strategy()
    if b.brute_force || b.stable
        for choice in Iterators.product(per_decision...)
            σ = Strategy(Dict{Symbol,AbstractPolicy}(names_[i] => choice[i]
                                                     for i in eachindex(names_)))
            eu = try
                expected_utility(m, σ; max_states=max_states, atol=atol, stable=b.stable)
            catch err
                err isa BayesianNetworks.ImpossibleEvidenceError || rethrow()
                continue
            end
            if eu > best
                best, best_strategy = eu, σ
            end
        end
        best == -Inf && throw(BayesianNetworks.ImpossibleEvidenceError(copy(evidence(m))))
        return DecisionSolution(best, best_strategy,
                                (nstrategies=Int(total),
                                 method=b.stable ? :stable_brute_force : :brute_force))
    end
    keep = Symbol[]
    for d in ds
        for x in information_names(id, d)
            x in keep || push!(keep, x)
        end
        a = variable_name(id, decision_variable(id, d))
        a in keep || push!(keep, a)
    end
    N, Z, unreliable = _value_tables(m, keep; max_states=max_states)
    # An underflowed or negative product makes a zero or small binary64 mass undecided, so
    # search strategy by strategy instead: `expected_utility` evaluates each one through
    # `BayesianNetworks.marginal`, which recomputes underflowed evidence exactly (ADR 0016)
    # and skips only strategies that make the evidence exactly impossible (ADR 0014).
    if unreliable
        sol = optimize(m, ExhaustivePolicySearch(b.max_policies, true, false);
                       max_states, atol)
        return DecisionSolution(sol.expected_utility, sol.strategy,
                                merge(sol.diagnostics, (exact_fallback=true,)))
    end
    kpos = Dict{Symbol,Int}(x => i for (i, x) in enumerate(keep))
    info_pos = [Int[kpos[x] for x in information_names(id, d)] for d in ds]
    act_pos = [kpos[variable_name(id, decision_variable(id, d))] for d in ds]
    act_labels = [_action_axis(m, d).labels for d in ds]
    # Policies as tables of action indices.
    index_tables = [[map(a -> label_index(FiniteAxis(:a, act_labels[i]), a), p.table)
                     for p in per_decision[i]] for i in eachindex(ds)]
    for choice in Iterators.product(eachindex.(per_decision)...)
        tabs = ntuple(i -> index_tables[i][choice[i]], length(ds))
        num = 0.0
        den = 0.0
        for ci in CartesianIndices(N)
            ok = true
            for i in eachindex(ds)
                ip = info_pos[i]
                tabs[i][ntuple(j -> ci[ip[j]], length(ip))...] == ci[act_pos[i]] ||
                    (ok = false;
                     break)
            end
            ok || continue
            num += N[ci]
            den += Z[ci]
        end
        den > 0 || continue
        eu = num / den
        if eu > best
            best = eu
            best_strategy = Strategy(Dict{Symbol,AbstractPolicy}(names_[i] => per_decision[i][choice[i]]
                                                                 for i in eachindex(ds)))
        end
    end
    best == -Inf && throw(BayesianNetworks.ImpossibleEvidenceError(copy(evidence(m))))
    return DecisionSolution(best, best_strategy,
                            (nstrategies=Int(total), method=:value_table))
end
