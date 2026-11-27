"""
The mixed-integer programme of `MixedIntegerPolicySearch`, stated in JuMP on the rooted
junction tree that `InfluenceDiagrams` builds. See `src/mixed_integer.jl` for the
formulation and its origin (the RJT model of DecisionProgramming.jl, after Parmentier et
al. 2020 and Herrala et al. 2024; an independent implementation, no shared code).
"""
module InfluenceDiagramsJuMPExt

using InfluenceDiagrams
using InfluenceDiagrams: InfluenceDiagrams, BayesianNetworks, InfluenceDiagramModel,
                         MixedIntegerPolicySearch, MixedIntegerSolverError,
                         UtilityScopeError
using JuMP: JuMP

const ID = InfluenceDiagrams

# The column-major linear index, in an array of sizes `dims[positions]`, of the coordinates
# of `ci` at `positions`.
function _sub_index(ci::CartesianIndex, positions::Vector{Int}, dims::Vector{Int})
    index = 1
    stride = 1
    for j in positions
        index += stride * (ci[j] - 1)
        stride *= dims[j]
    end
    return index
end

function ID._mixed_integer_optimize(m::InfluenceDiagramModel, b::MixedIntegerPolicySearch;
                                    max_states::Integer, atol::Real)
    id = ID.syntax(m)
    tree = ID.rooted_junction_tree(id)
    order, clusters, parent = tree.order, tree.clusters, tree.parent
    nstates = Dict{Symbol,Int}(x => ID.nstates(id, x) for x in order)
    sizes = Dict{Symbol,Vector{Int}}(x => Int[nstates[y] for y in clusters[x]]
                                     for x in order)
    largest = maximum(prod(big.(sizes[x])) for x in order; init=big(1))
    largest <= b.max_cluster_states ||
        throw(BayesianNetworks.ModelTooLargeError(Int(min(largest, typemax(Int))),
                                                  b.max_cluster_states))
    ds = ID.decision_order(id)
    decision_at = Dict{Symbol,Int}(ID.variable_name(id, ID.decision_variable(id, d)) => i
                                   for (i, d) in enumerate(ds))
    kernels = Dict{Symbol,Any}()
    for mech in ID.mechanisms(id)
        x = ID.variable_name(id, ID.target(id, mech))
        kernels[x] = (convert(Array{Float64}, ID.kernel(m.model, x).table),
                      Symbol[x;
                             Symbol[ID.variable_name(id, p) for p in ID.inputs(id, mech)]])
    end
    # No strategy carries more mass than the product of the largest row sums, which is one
    # for normalised kernels.
    mass = prod(max(1.0, maximum(sum(table; dims=1))) for (table, _) in values(kernels);
                init=1.0)

    model = JuMP.Model(b.optimizer)
    b.silent && JuMP.set_silent(model)
    μ = Dict{Symbol,Any}()
    z = Vector{Any}(undef, length(ds))
    for x in order
        cluster = clusters[x]
        dims = sizes[x]
        cells = CartesianIndices(Tuple(dims))
        μx = JuMP.@variable(model, [1:length(cells)], lower_bound = 0.0)
        μ[x] = μx
        # The marginal of the parent cluster on this cluster without `x` (which is last).
        rest = collect(1:(length(cluster) - 1))
        marginal = if parent[x] === nothing
            JuMP.AffExpr[JuMP.AffExpr(1.0)]
        else
            up = parent[x]
            at = Int[findfirst(==(y), clusters[up]) for y in cluster[rest]]
            exprs = [JuMP.AffExpr(0.0) for _ in 1:prod(dims[rest]; init=1)]
            for (k, ci) in enumerate(CartesianIndices(Tuple(sizes[up])))
                JuMP.add_to_expression!(exprs[_sub_index(ci, at, sizes[up])], μ[up][k])
            end
            exprs
        end
        if haskey(decision_at, x)
            i = decision_at[x]
            information = ID.information_names(id, ds[i])
            at = Int[findfirst(==(y), cluster) for y in information]
            rows = prod(dims[at]; init=1)
            zi = JuMP.@variable(model, [1:rows, 1:nstates[x]], Bin)
            z[i] = zi
            JuMP.@constraint(model, [r in 1:rows], sum(zi[r, :]) == 1)
            totals = [JuMP.AffExpr(0.0) for _ in eachindex(marginal)]
            for (k, ci) in enumerate(cells)
                JuMP.add_to_expression!(totals[_sub_index(ci, rest, dims)], μx[k])
                JuMP.@constraint(model,
                                 μx[k] <= mass * zi[_sub_index(ci, at, dims), ci[length(dims)]])
            end
            JuMP.@constraint(model, [j in eachindex(marginal)], totals[j] == marginal[j])
        else
            table, axes = kernels[x]
            at = Int[findfirst(==(y), cluster) for y in axes]
            for (k, ci) in enumerate(cells)
                p = table[_sub_index(ci, at, dims)]
                JuMP.@constraint(model, μx[k] == p * marginal[_sub_index(ci, rest, dims)])
            end
        end
    end
    position = Dict{Symbol,Int}(x => i for (i, x) in enumerate(order))
    objective = JuMP.AffExpr(0.0)
    for (name, u) in m.utilities
        axes = ID._utility_axes(m, ID.utility_id(id, name))
        table = ID.utility_table(u, axes)
        all(isfinite, table) ||
            throw(UtilityScopeError(name, :value, "finite utility entries", table))
        if isempty(axes)
            JuMP.add_to_expression!(objective, Float64(only(table)))
            continue
        end
        scope = Symbol[a.name for a in axes]
        holder = argmax(x -> position[x], scope)
        at = Int[findfirst(==(y), clusters[holder]) for y in scope]
        for (k, ci) in enumerate(CartesianIndices(Tuple(sizes[holder])))
            JuMP.add_to_expression!(objective, table[_sub_index(ci, at, sizes[holder])],
                                    μ[holder][k])
        end
    end
    JuMP.@objective(model, Max, objective)
    JuMP.optimize!(model)
    status = JuMP.termination_status(model)
    status == JuMP.OPTIMAL || throw(MixedIntegerSolverError(Symbol(status)))

    tables = [Int[argmax(JuMP.value.(z[i][r, :])) for r in axes(z[i], 1)]
              for i in eachindex(ds)]
    strategy = ID._strategy_from_indices(m, ds, tables)
    solved = JuMP.objective_value(model)
    joint = prod(big(nstates[x]) for x in order; init=big(1))
    verified = joint <= max_states
    value = verified ? ID.expected_utility(m, strategy; max_states=max_states, atol=atol) :
            solved
    return ID.DecisionSolution(value, strategy,
                               (method=:mixed_integer, verified=verified, objective=solved,
                                status=Symbol(status), clusters=length(order),
                                largest_cluster=Int(largest),
                                binaries=sum(length(zi) for zi in z; init=0),
                                nstrategies=ID.n_deterministic_strategies(m)))
end

end # module
