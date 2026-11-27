"""
Policy optimisation by branch and bound over policy rows: exact on any diagram, with or
without no-forgetting, and without enumerating the strategies.

Origin. The problem class and the role of single policy updating follow
DecisionProgramming.jl (github.com/gamma-opt/DecisionProgramming.jl, MIT licence; Salo,
Andelmin and Oliveira 2022; Hankimaa, Herrala, Oliveira and Tollander de Balsch 2023),
which solves limited-memory influence diagrams as mixed-integer linear programmes and
uses single policy updating for starting solutions. This file is an independent
implementation that needs no optimisation package: it shares no code with
DecisionProgramming.jl and uses a different exact method (a combinatorial branch and
bound on the value tables of [`ExhaustivePolicySearch`](@ref) instead of an integer
programme). Single policy updating is the algorithm of Lauritzen and Nilsson (2001).
"""

"""
    BranchAndBoundPolicySearch(; max_nodes = 1_000_000)

Find an optimal deterministic strategy by branch and bound over policy rows. It is
exact on every valid diagram, including a limited-memory one
[LauritzenNilsson2001](@cite), which [`DecisionVariableElimination`](@ref) refuses, and it
does not enumerate strategies, so the number of strategies is no limit: what limits it
is the number of joint states (`max_states` of [`optimize`](@ref), as for
[`ExhaustivePolicySearch`](@ref)) and the number of nodes searched (`max_nodes`,
[`SearchNodeLimitError`](@ref) beyond it).

The method works on the value tables of [`ExhaustivePolicySearch`](@ref): `N[c, a]`,
the sum of `P(x) U(x)` over the joint states `x` that agree with `c` on the chance
variables some decision observes and with `a` on the actions, and `Z[c, a]`, the same
sum of `P(x)`. A strategy selects one action tuple for every `c`, and its expected
utility is the selected sum of `N` over the selected sum of `Z`.

- **Bound.** Let every decision see what any decision sees: choose the best action
  tuple for each `c` separately, keeping to the policy rows already fixed. No strategy
  that extends those rows can do better, because it also selects one tuple for each `c`.
- **Branch.** If the tuples so chosen ask one policy row for two different actions, fix
  that row to each action in turn. If they never do, they are a strategy, it attains
  the bound, and the node is solved.
- **Start.** Single policy updating [LauritzenNilsson2001](@cite) improves one
  decision's policy at a time, the others held fixed, until no decision can improve;
  its strategy is the first incumbent.
- **Ratio.** The kernels of a model are accepted within a tolerance and never
  renormalised, so the sum of `Z` depends (slightly) on the strategy. The ratio is
  maximised exactly by Dinkelbach's iteration: maximise `N - λ Z` with `λ` the ratio of
  the incumbent, and repeat until the ratio stops increasing.

The strategy returned is optimal; when several are, it need not be the one
[`ExhaustivePolicySearch`](@ref) returns (the first in its order). A policy row that no
state reaches gets the first action label.

Not supported, and refused with `ArgumentError`: evidence, a [`DecisionContext`](@ref),
and a model in which a product of nonzero probabilities falls below the normal range of
`Float64` (ADR 0014: such a run is untrusted). [`ExhaustivePolicySearch`](@ref) handles
all three.

Diagnostics: `(; method = :branch_and_bound, nodes, root_bound, incumbent_start,
ratio_iterations, nstrategies)`, where `root_bound` is the bound before any branching and
`incumbent_start` the value single policy updating reached, both on the first ratio
iteration, and `nstrategies` is the size of the space that was not enumerated (a
`BigInt`).
"""
struct BranchAndBoundPolicySearch <: DecisionBackend
    max_nodes::Int
    function BranchAndBoundPolicySearch(max_nodes::Integer)
        max_nodes >= 1 ||
            throw(ArgumentError("max_nodes must be at least 1, got $(max_nodes)"))
        return new(Int(max_nodes))
    end
end
function BranchAndBoundPolicySearch(; max_nodes::Integer=1_000_000)
    return BranchAndBoundPolicySearch(max_nodes)
end

# The value-table cells in the form the search reads them, one entry per cell `k` of the
# tables (column-major over the `keep` variables):
# - `chance[k]`: the linear index of the cell's values of the observed chance variables;
# - `action[i][k]`: the index of decision `i`'s action in the cell;
# - `row[i][k]`: the linear index of decision `i`'s information state in the cell, in the
#   layout of a `DeterministicPolicy` table (the first information axis fastest).
struct _SearchCells
    chance::Vector{Int32}
    action::Vector{Vector{Int32}}
    row::Vector{Vector{Int32}}
    nchance::Int
    nactions::Vector{Int}
    nrows::Vector{Int}
end

function _search_cells(kdims::NTuple{M,Int}, act_pos::Vector{Int},
                       info_pos::Vector{Vector{Int}}) where {M}
    n = length(act_pos)
    chance_pos = Int[j for j in 1:M if !(j in act_pos)]
    L = prod(kdims; init=1)
    chance = Vector{Int32}(undef, L)
    action = [Vector{Int32}(undef, L) for _ in 1:n]
    row = [Vector{Int32}(undef, L) for _ in 1:n]
    for (k, ci) in enumerate(CartesianIndices(kdims))
        chance[k] = _linear(ci, chance_pos, kdims)
        for i in 1:n
            action[i][k] = ci[act_pos[i]]
            row[i][k] = _linear(ci, info_pos[i], kdims)
        end
    end
    return _SearchCells(chance, action, row,
                        prod(Int[kdims[j] for j in chance_pos]; init=1),
                        Int[kdims[j] for j in act_pos],
                        Int[prod(Int[kdims[j] for j in p]; init=1) for p in info_pos])
end

# The column-major linear index of the coordinates of `ci` at `positions`.
function _linear(ci::CartesianIndex, positions::Vector{Int}, kdims::Tuple)
    idx = 1
    stride = 1
    for j in positions
        idx += stride * (ci[j] - 1)
        stride *= kdims[j]
    end
    return idx
end

# Whether cell `k` keeps to the policy rows in `tables` (0 = row not fixed), leaving
# decision `skip` out.
@inline function _keeps(cells::_SearchCells, tables::Vector{Vector{Int}}, k::Int,
                        skip::Int=0)
    @inbounds for i in eachindex(tables)
        i == skip && continue
        a = tables[i][cells.row[i][k]]
        (a == 0 || a == cells.action[i][k]) || return false
    end
    return true
end

# The sum of `T` over the cells a complete strategy selects.
function _selected_sum(T::Vector{Float64}, cells::_SearchCells,
                       tables::Vector{Vector{Int}})
    total = 0.0
    @inbounds for k in eachindex(T)
        _keeps(cells, tables, k) && (total += T[k])
    end
    return total
end

# Single policy updating on the objective `T`, in place on `tables` (complete). Each sweep
# visits every decision once and, for each of its information states, moves to an action
# that is strictly better given the other decisions' policies. Returns the number of
# sweeps; the objective never decreases.
function _single_policy_updating!(tables::Vector{Vector{Int}}, T::Vector{Float64},
                                  cells::_SearchCells; max_sweeps::Int=100)
    sweeps = 0
    changed = true
    while changed && sweeps < max_sweeps
        changed = false
        sweeps += 1
        for i in eachindex(tables)
            score = zeros(cells.nrows[i], cells.nactions[i])
            @inbounds for k in eachindex(T)
                _keeps(cells, tables, k, i) &&
                    (score[cells.row[i][k], cells.action[i][k]] += T[k])
            end
            for r in 1:cells.nrows[i]
                current = tables[i][r]
                best = current
                for a in 1:cells.nactions[i]
                    score[r, a] > score[r, best] && (best = a)
                end
                if best != current
                    tables[i][r] = best
                    changed = true
                end
            end
        end
    end
    return sweeps
end

# The relaxation at a node: for every value `c` of the observed chance variables, the best
# cell that keeps to the fixed rows of `tables`. Returns the bound (the sum of the best
# values), and either a strategy attaining it (`conflict === nothing`) or the policy row
# `(decision, row)` that the chosen cells ask for two different actions. A `c` whose
# admissible cells all have the same value constrains nothing and is left out of the
# strategy's construction.
function _relax(T::Vector{Float64}, cells::_SearchCells, tables::Vector{Vector{Int}},
                best::Vector{Float64}, low::Vector{Float64}, arg::Vector{Int})
    fill!(best, -Inf)
    fill!(low, Inf)
    fill!(arg, 0)
    @inbounds for k in eachindex(T)
        _keeps(cells, tables, k) || continue
        c = cells.chance[k]
        t = T[k]
        if t > best[c]
            best[c] = t
            arg[c] = k
        end
        t < low[c] && (low[c] = t)
    end
    bound = 0.0
    for c in eachindex(best)
        bound += best[c]
    end
    wanted = [zeros(Int, cells.nrows[i]) for i in eachindex(tables)]
    clashes = [zeros(Int, cells.nrows[i]) for i in eachindex(tables)]
    conflict = nothing
    most = 0
    @inbounds for c in eachindex(best)
        best[c] > low[c] || continue
        k = arg[c]
        for i in eachindex(tables)
            r = cells.row[i][k]
            a = cells.action[i][k]
            if wanted[i][r] == 0
                wanted[i][r] = a
            elseif wanted[i][r] != a
                clashes[i][r] += 1
                if clashes[i][r] > most
                    most = clashes[i][r]
                    conflict = (i, Int(r))
                end
            end
        end
    end
    conflict === nothing || return bound, conflict, wanted
    strategy = [Int[tables[i][r] != 0 ? tables[i][r] : max(wanted[i][r], 1)
                    for r in 1:cells.nrows[i]] for i in eachindex(tables)]
    return bound, nothing, strategy
end

mutable struct _SearchState
    value::Float64
    strategy::Vector{Vector{Int}}
    nodes::Int
    const max_nodes::Int
end

# Depth-first search below the node `tables`, whose relaxation is `(bound, conflict,
# found)`. Children are visited in decreasing order of their bounds.
function _branch!(state::_SearchState, T::Vector{Float64}, cells::_SearchCells,
                  tables::Vector{Vector{Int}}, bound::Float64, conflict, found,
                  buffers)
    bound > state.value || return nothing
    if conflict === nothing
        value = _selected_sum(T, cells, found)
        if value > state.value
            state.value = value
            state.strategy = found
        end
        return nothing
    end
    i, r = conflict
    children = map(1:cells.nactions[i]) do a
        child = [copy(t) for t in tables]
        child[i][r] = a
        state.nodes += 1
        state.nodes <= state.max_nodes ||
            throw(SearchNodeLimitError(state.nodes, state.max_nodes))
        return (child, _relax(T, cells, child, buffers...)...)
    end
    for (child, b, c, f) in sort!(children; by=x -> x[2], rev=true)
        _branch!(state, T, cells, child, b, c, f, buffers)
    end
    return nothing
end

# Maximise the selected sum of `T` over the complete strategies, from the incumbent
# `start`. Returns the best strategy, its value, the root bound and the nodes searched.
function _maximise_selected_sum(T::Vector{Float64}, cells::_SearchCells,
                                start::Vector{Vector{Int}}, max_nodes::Int)
    state = _SearchState(_selected_sum(T, cells, start), start, 1, max_nodes)
    buffers = (Vector{Float64}(undef, cells.nchance), Vector{Float64}(undef, cells.nchance),
               Vector{Int}(undef, cells.nchance))
    free = [zeros(Int, cells.nrows[i]) for i in eachindex(start)]
    bound, conflict, found = _relax(T, cells, free, buffers...)
    _branch!(state, T, cells, free, bound, conflict, found, buffers)
    return state.strategy, state.value, bound, state.nodes
end

function optimize(m::InfluenceDiagramModel, b::BranchAndBoundPolicySearch;
                  max_states::Integer=1_000_000,
                  atol::Real=BayesianNetworks.DEFAULT_ATOL,
                  context::Union{Nothing,DecisionContext}=nothing)
    context === nothing || _active_context(context) === nothing ||
        throw(ArgumentError("BranchAndBoundPolicySearch does not take a decision context; optimise against a context with ExhaustivePolicySearch"))
    _check_solvable(m; atol=atol)
    isempty(evidence(m)) ||
        throw(ArgumentError("BranchAndBoundPolicySearch does not take evidence; optimise a model with evidence with ExhaustivePolicySearch"))
    id = syntax(m)
    ds = decision_order(id)
    keep = Symbol[]
    for d in ds
        for x in information_names(id, d)
            x in keep || push!(keep, x)
        end
        a = variable_name(id, decision_variable(id, d))
        a in keep || push!(keep, a)
    end
    N, Z, _, unreliable = _value_tables(m, keep; max_states=max_states)
    unreliable &&
        throw(ArgumentError("a product of nonzero probabilities fell below the normal range of Float64, so the value tables are untrusted (ADR 0014); use ExhaustivePolicySearch, which scores such a model strategy by strategy"))
    kpos = Dict{Symbol,Int}(x => i for (i, x) in enumerate(keep))
    info_pos = [Int[kpos[x] for x in information_names(id, d)] for d in ds]
    act_pos = Int[kpos[variable_name(id, decision_variable(id, d))] for d in ds]
    cells = _search_cells(size(N), act_pos, info_pos)
    n, z = vec(N), vec(Z)
    tables = [ones(Int, cells.nrows[i]) for i in eachindex(ds)]
    nodes = 0
    iterations = 0
    root_bound = NaN
    incumbent_start = NaN
    while true
        iterations += 1
        den = _selected_sum(z, cells, tables)
        λ = _selected_sum(n, cells, tables) / den
        T = n .- λ .* z
        _single_policy_updating!(tables, T, cells)
        iterations == 1 && (incumbent_start = _selected_sum(n, cells, tables) /
                                              _selected_sum(z, cells, tables))
        found, _, bound, searched = _maximise_selected_sum(T, cells, tables, b.max_nodes)
        nodes += searched
        iterations == 1 && (root_bound = bound + λ * den)
        better = _selected_sum(n, cells, found) / _selected_sum(z, cells, found)
        better > λ || break
        tables = found
        # The ratio increases strictly at every pass and there are finitely many
        # strategies, so this ends; the cap only guards against rounding.
        iterations < 50 || break
    end
    value = _selected_sum(n, cells, tables) / _selected_sum(z, cells, tables)
    return DecisionSolution(value, _strategy_from_indices(m, ds, tables),
                            (method=:branch_and_bound, nodes=nodes, root_bound=root_bound,
                             incumbent_start=incumbent_start,
                             ratio_iterations=iterations,
                             nstrategies=n_deterministic_strategies(m)))
end
