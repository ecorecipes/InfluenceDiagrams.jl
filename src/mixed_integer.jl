"""
Policy optimisation as a mixed-integer linear programme on a rooted junction tree.

Origin. The formulation is the one DecisionProgramming.jl
(github.com/gamma-opt/DecisionProgramming.jl, MIT licence) calls its RJT model: integer
programming on the junction-tree polytope of Parmentier, Cohen, Leclère, Obozinski and
Salmon (2020), as used for decision programming by Herrala, Terho and Oliveira (2024),
within the framework of Salo, Andelmin and Oliveira (2022). This is an independent
implementation written from those papers: it shares no code with DecisionProgramming.jl.
The tree and the data of the programme are built here, with no dependency; the programme
itself is stated and solved in the extension `InfluenceDiagramsJuMPExt`, which loads when
JuMP does.
"""

"""
    MixedIntegerPolicySearch(optimizer; silent = true, max_cluster_states = 1_000_000)

Find an optimal deterministic strategy by solving a mixed-integer linear programme, with
`optimizer` a JuMP optimizer (for example `HiGHS.Optimizer`). It is exact on every valid
diagram, with or without no-forgetting, up to the solver's own tolerances, and it does
not enumerate the joint states: its size is set by the clusters of a rooted junction
tree, not by the diagram as a whole, so it reaches diagrams that
[`ExhaustivePolicySearch`](@ref) and [`BranchAndBoundPolicySearch`](@ref) cannot.

**It needs JuMP**, which is not a dependency of this package: `optimize` with this backend
throws `ArgumentError` until `using JuMP` has loaded the extension.

The programme is integer programming on the junction-tree polytope
[ParmentierEtAl2020](@cite), the formulation of decision programming [Salo2022](@cite)
on rooted junction trees [HerralaEtAl2024](@cite). Every variable `v` of the diagram has a cluster `C_v`
holding `v`, its parents (for an action, its information set) and whatever later clusters
pass down, and a nonnegative variable `μ_v(x)` for each state `x` of the cluster, which at
an integer solution is the probability of `x` under the strategy. With `m_v` the marginal
of the parent cluster's `μ` on `C_v` without `v` (the constant one at a root):

- a chance variable has `μ_v(x) = P(x_v | parents) m_v(x)`;
- a decision has a binary `z(a | i)` for every information state `i` and action `a`, one
  action per information state, with `Σ_a μ_v(x, a) = m_v(x)` and `μ_v(x, a) ≤ M z(a | i)`,
  where `M` bounds the total mass (one, for normalised kernels);
- the objective is `Σ_u Σ_x U_u(x) μ(x)`, each utility read from a cluster that holds its
  scope.

The value reported is this package's own: the strategy the solver returns is scored by
[`expected_utility`](@ref) when the diagram has at most `max_states` joint states
(`diagnostics.verified`), and the solver's objective is reported otherwise. The
programme maximises `Σ_x P(x) U(x)`; kernels accepted within a tolerance are not
renormalised, so on such a model the strategy can differ from the oracle's by a
tolerance-sized amount of value.

`silent = false` shows the solver's log. A cluster with more than `max_cluster_states`
states throws `ModelTooLargeError`. Evidence and a [`DecisionContext`](@ref) are refused
with `ArgumentError`, as [`BranchAndBoundPolicySearch`](@ref) refuses them. A solve that
does not end at a proven optimum throws [`MixedIntegerSolverError`](@ref).

Diagnostics: `(; method = :mixed_integer, verified, objective, status, clusters,
largest_cluster, binaries, nstrategies)`.
"""
struct MixedIntegerPolicySearch <: DecisionBackend
    optimizer::Any
    silent::Bool
    max_cluster_states::Int
    function MixedIntegerPolicySearch(optimizer; silent::Bool=true,
                                      max_cluster_states::Integer=1_000_000)
        max_cluster_states >= 1 ||
            throw(ArgumentError("max_cluster_states must be at least 1, got $(max_cluster_states)"))
        return new(optimizer, silent, Int(max_cluster_states))
    end
end

# A topological order of the variables of a diagram in which every parent of a mechanism
# precedes its target and every information variable precedes the action it informs.
# Ties go to the smaller part id, so the order is a function of the diagram.
function _decision_topological_order(id::AbstractInfluenceDiagram)
    vars = variable_names(id)
    parents = _decision_parents(id)
    placed = Set{Symbol}()
    order = Symbol[]
    while length(order) < length(vars)
        next = findfirst(x -> !(x in placed) && all(in(placed), parents[x]), vars)
        # `validate` has already refused a cyclic diagram.
        next === nothing && throw(DecisionPrecedenceCycleError(setdiff(vars, order)))
        push!(order, vars[next])
        push!(placed, vars[next])
    end
    return order
end

# The parents of every variable: the inputs of its mechanism for a chance variable, in
# input order, and its information set for an action, in `information_position` order.
function _decision_parents(id::AbstractInfluenceDiagram)
    parents = Dict{Symbol,Vector{Symbol}}(x => Symbol[] for x in variable_names(id))
    for mech in mechanisms(id)
        parents[variable_name(id, target(id, mech))] = Symbol[variable_name(id, p)
                                                              for p in inputs(id, mech)]
    end
    for d in decisions(id)
        parents[variable_name(id, decision_variable(id, d))] = information_names(id, d)
    end
    return parents
end

"""
    rooted_junction_tree(id; scopes = utility scopes of id) -> NamedTuple

The rooted junction tree of an influence diagram [ParmentierEtAl2020](@cite), on which
[`MixedIntegerPolicySearch`](@ref) states its programme. The result is `(; order,
clusters, parent)`: `order` is a topological order of the variables (parents and
information variables first), `clusters[v]` the cluster of `v` in that order, with `v`
last, and `parent[v]` the variable whose cluster is the parent of `v`'s (`nothing` at a
root).

Each cluster holds its variable and that variable's parents, and what the clusters below
it pass up: a cluster passes everything but its own variable to the cluster of the latest
of them. So `clusters[v]` without `v` is contained in `clusters[parent[v]]`, the clusters
holding a variable are connected, and every variable of a cluster precedes the cluster's
own. `scopes` (lists of variable names) are further sets that some cluster must hold;
by default the scopes of the utilities.
"""
function rooted_junction_tree(id::AbstractInfluenceDiagram;
                              scopes=[utility_scope_names(id, u) for u in utilities(id)])
    order = _decision_topological_order(id)
    position = Dict{Symbol,Int}(x => i for (i, x) in enumerate(order))
    parents = _decision_parents(id)
    members = Dict{Symbol,Set{Symbol}}(x => Set{Symbol}([x; parents[x]]) for x in order)
    # A scope behaves as a variable placed after every other: it passes its members to the
    # cluster of the latest of them.
    for scope in scopes
        isempty(scope) && continue
        for x in scope
            haskey(position, x) || throw(UnknownVariableError(x))
        end
        latest = argmax(x -> position[x], scope)
        union!(members[latest], scope)
    end
    parent = Dict{Symbol,Union{Nothing,Symbol}}()
    for x in reverse(order)
        rest = setdiff(members[x], (x,))
        if isempty(rest)
            parent[x] = nothing
        else
            latest = argmax(y -> position[y], collect(rest))
            union!(members[latest], rest)
            parent[x] = latest
        end
    end
    clusters = Dict{Symbol,Vector{Symbol}}(x => sort!(collect(members[x]);
                                                      by=y -> position[y]) for x in order)
    return (; order, clusters, parent)
end

function rooted_junction_tree(m::InfluenceDiagramModel; kw...)
    return rooted_junction_tree(syntax(m); kw...)
end

# The strategy with the action indices `tables[i]` for the `i`-th decision of `ds`, each in
# the layout of a `DeterministicPolicy` table.
function _strategy_from_indices(m::InfluenceDiagramModel, ds, tables)
    id = syntax(m)
    policies = Dict{Symbol,AbstractPolicy}()
    for (i, d) in enumerate(ds)
        name = decision_name(id, d)
        information = _information_axes(m, d)
        act = _action_axis(m, d)
        labels = reshape(Symbol[act.labels[a] for a in tables[i]],
                         Tuple(length(a) for a in information))
        policies[name] = DeterministicPolicy(name, information, act, labels)
    end
    return Strategy(policies)
end

# The method the extension adds; `optimize` reaches it only when the extension is loaded.
function _mixed_integer_optimize end

function optimize(m::InfluenceDiagramModel, b::MixedIntegerPolicySearch;
                  max_states::Integer=1_000_000,
                  atol::Real=BayesianNetworks.DEFAULT_ATOL,
                  context::Union{Nothing,DecisionContext}=nothing)
    Base.get_extension(@__MODULE__, :InfluenceDiagramsJuMPExt) === nothing &&
        throw(ArgumentError("MixedIntegerPolicySearch needs JuMP, which is not a dependency of InfluenceDiagrams: load it with `using JuMP` (and an optimizer such as HiGHS)"))
    context === nothing || _active_context(context) === nothing ||
        throw(ArgumentError("MixedIntegerPolicySearch does not take a decision context; optimise against a context with ExhaustivePolicySearch"))
    _check_solvable(m; atol=atol)
    isempty(evidence(m)) ||
        throw(ArgumentError("MixedIntegerPolicySearch does not take evidence; optimise a model with evidence with ExhaustivePolicySearch"))
    return _mixed_integer_optimize(m, b; max_states=max_states, atol=atol)
end
