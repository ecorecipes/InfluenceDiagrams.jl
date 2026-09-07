"""
Read-only accessors for the influence-diagram objects. Decisions and utilities are
accepted as part ids or names (a decision may also be named by its action variable);
results are part ids unless the name says otherwise.

Ordering contract: information sets are sorted by `information_position` and utility
scopes by `utility_position`; part-id order is never used to define an order.
"""

# Decisions
###########

"""
    decisions(id) -> Vector{Int}

Part ids of all decisions.
"""
decisions(id::AbstractInfluenceDiagram) = collect(parts(id, :Decision))

"""
    decision_names(id) -> Vector{Symbol}

Names of all decisions, in part-id order.
"""
decision_names(id::AbstractInfluenceDiagram) = collect(subpart(id, :decision_name))

"""
    decision_name(id, d) -> Symbol

Name of decision `d` (id or name).
"""
function decision_name(id::AbstractInfluenceDiagram, d)
    return subpart(id, _decision_id(id, d),
                   :decision_name)
end

"""
    decision_variable(id, d) -> Int

Part id of the action variable controlled by decision `d` (id or name).
"""
function decision_variable(id::AbstractInfluenceDiagram, d)
    return subpart(id, _decision_id(id, d), :decision_variable)
end

"""
    decision_of(id, v) -> Union{Int, Nothing}

Part id of the decision controlling variable `v` (id or name), or `nothing` if it is a
chance variable. Throws [`DecisionUniquenessError`](@ref) if several decisions control
it.
"""
function decision_of(id::AbstractInfluenceDiagram, v)
    vid = _variable_id(id, v)
    ds = incident(id, vid, :decision_variable)
    isempty(ds) && return nothing
    length(ds) > 1 &&
        throw(DecisionUniquenessError(subpart(id, ds[2], :decision_name),
                                      variable_name(id, vid), :duplicate_decision))
    return first(ds)
end

"""
    is_decision(id, v) -> Bool

Whether variable `v` (id or name) is the action variable of some decision.
"""
function is_decision(id::AbstractInfluenceDiagram, v)
    return !isempty(incident(id, _variable_id(id, v), :decision_variable))
end

"""
    information_ids(id, d) -> Vector{Int}

`InformationInput` part ids of decision `d` (id or name), sorted by
`information_position`.
"""
function information_ids(id::AbstractInfluenceDiagram, d)
    ids = collect(incident(id, _decision_id(id, d), :information_decision))
    return sort!(ids; by=i -> (subpart(id, i, :information_position), i))
end

"""
    decision_information(id, d) -> Vector{Int}

Part ids of the variables in the information set of decision `d` (id or name), sorted
by `information_position`. This is the domain order of the decision's policy.
"""
function decision_information(id::AbstractInfluenceDiagram, d)
    return [subpart(id, i, :information_variable) for i in information_ids(id, d)]
end

"""
    information_names(id, d) -> Vector{Symbol}

Names of the variables in the information set of decision `d`, in
`information_position` order.
"""
function information_names(id::AbstractInfluenceDiagram, d)
    return Symbol[variable_name(id, v) for v in decision_information(id, d)]
end

"""
    action_variables(id) -> Vector{Int}

Part ids of the variables controlled by a decision, in decision part-id order.
"""
function action_variables(id::AbstractInfluenceDiagram)
    return unique!([subpart(id, d, :decision_variable) for d in decisions(id)])
end

"""
    action_names(id) -> Vector{Symbol}

Names of the action variables, in decision part-id order.
"""
function action_names(id::AbstractInfluenceDiagram)
    return Symbol[variable_name(id, v)
                  for v in action_variables(id)]
end

"""
    chance_variables(id) -> Vector{Int}

Part ids of the variables that are not controlled by any decision.
"""
function chance_variables(id::AbstractInfluenceDiagram)
    return filter(v -> !is_decision(id, v),
                  variables(id))
end

"""
    chance_names(id) -> Vector{Symbol}

Names of the chance variables, in part-id order.
"""
function chance_names(id::AbstractInfluenceDiagram)
    return Symbol[variable_name(id, v)
                  for v in chance_variables(id)]
end

# Utilities
###########

"""
    utilities(id) -> Vector{Int}

Part ids of all utility nodes.
"""
utilities(id::AbstractInfluenceDiagram) = collect(parts(id, :Utility))

"""
    utility_names(id) -> Vector{Symbol}

Names of all utility nodes, in part-id order.
"""
utility_names(id::AbstractInfluenceDiagram) = collect(subpart(id, :utility_name))

"""
    utility_name(id, u) -> Symbol

Name of utility node `u` (id or name).
"""
function utility_name(id::AbstractInfluenceDiagram, u)
    return subpart(id, _utility_id(id, u),
                   :utility_name)
end

"""
    utility_ref(id, u) -> KernelRef

The `utility_ref` attribute of utility node `u` (id or name).
"""
utility_ref(id::AbstractInfluenceDiagram, u) = subpart(id, _utility_id(id, u), :utility_ref)

"""
    utility_input_ids(id, u) -> Vector{Int}

`UtilityInput` part ids of utility node `u` (id or name), sorted by `utility_position`.
"""
function utility_input_ids(id::AbstractInfluenceDiagram, u)
    ids = collect(incident(id, _utility_id(id, u), :utility_node))
    return sort!(ids; by=i -> (subpart(id, i, :utility_position), i))
end

"""
    utility_scope(id, u) -> Vector{Int}

Part ids of the variables read by utility node `u` (id or name), sorted by
`utility_position`. This is the argument order of the utility function.
"""
function utility_scope(id::AbstractInfluenceDiagram, u)
    return [subpart(id, i, :utility_variable) for i in utility_input_ids(id, u)]
end

"""
    utility_scope_names(id, u) -> Vector{Symbol}

Names of the variables in the scope of utility node `u`, in `utility_position` order.
"""
function utility_scope_names(id::AbstractInfluenceDiagram, u)
    return Symbol[variable_name(id, v) for v in utility_scope(id, u)]
end

# Precedence and decision order
###############################

"""
    precedences(id) -> Vector{Pair{Int,Int}}

The explicit `earlier => later` decision precedence rows, as decision part ids.
"""
function precedences(id::AbstractInfluenceDiagram)
    return Pair{Int,Int}[subpart(id, p, :earlier) => subpart(id, p, :later)
                         for p in parts(id, :DecisionPrecedence)]
end

"""
    information_graph(id) -> Graphs.SimpleDiGraph{Int}

The directed graph on the variables (vertex `i` is variable `i`) with one edge per
causal `Input` (parent to target), one edge per `InformationInput` (information variable
to action variable) and one edge per explicit precedence (earlier action to later
action). The declared information is consistent, and the decisions can be ordered, when
this graph is acyclic (SPEC §37 items 4, 8 and 11); its topological orders are the
orders in which a decision maker can take the decisions with the declared information.
Acyclicity is weaker than no-forgetting: see [`no_forgetting_arcs`](@ref). Information edges are never part of
`variable_graph`, which only carries the causal structure (SPEC §34).
"""
function information_graph(id::AbstractInfluenceDiagram)
    g = _arc_graph(id)
    for p in parts(id, :DecisionPrecedence)
        add_edge!(g, subpart(id, subpart(id, p, :earlier), :decision_variable),
                  subpart(id, subpart(id, p, :later), :decision_variable))
    end
    return g
end

# Causal and information arcs only (no explicit precedence).
function _arc_graph(id::AbstractInfluenceDiagram)
    g = variable_graph(id)
    for i in parts(id, :InformationInput)
        d = subpart(id, i, :information_decision)
        add_edge!(g, subpart(id, i, :information_variable),
                  subpart(id, d, :decision_variable))
    end
    return g
end

# Kahn's algorithm on a directed graph, smallest vertex first; returns the order and the
# vertices that could not be placed.
function _kahn(g::SimpleDiGraph)
    n = nv(g)
    indegree = zeros(Int, n)
    succ = [Int[] for _ in 1:n]
    for e in edges(g)
        s, t = src(e), dst(e)
        push!(succ[s], t)
        indegree[t] += 1
    end
    ready = sort!(findall(==(0), indegree); rev=true)
    order = Int[]
    while !isempty(ready)
        v = pop!(ready)
        push!(order, v)
        for t in succ[v]
            indegree[t] -= 1
            if indegree[t] == 0
                push!(ready, t)
                sort!(ready; rev=true)
            end
        end
    end
    return order, findall(>(0), indegree)
end

# Vertices reachable from `start` in `g` (excluding `start` unless on a cycle).
function _reachable(g::SimpleDiGraph, start::Int)
    seen = falses(nv(g))
    stack = [start]
    out = Int[]
    while !isempty(stack)
        v = pop!(stack)
        for t in outneighbors(g, v)
            seen[t] && continue
            seen[t] = true
            push!(out, t)
            push!(stack, t)
        end
    end
    return out
end

"""
    decision_order(id) -> Vector{Int}

The decisions (part ids) in the order in which they are taken: a topological order of
the action variables in [`information_graph`](@ref), which combines causal arcs,
information arcs and explicit precedence. Ties are broken by the smallest variable id.
Throws [`DecisionPrecedenceCycleError`](@ref) when the explicit precedence is cyclic
or contradicts the arcs, and `CyclicBayesNetError` when the causal graph itself has a
cycle.
"""
function decision_order(id::AbstractInfluenceDiagram)
    order, remaining = _kahn(information_graph(id))
    if !isempty(remaining)
        _, causal_remaining = _kahn(variable_graph(id))
        isempty(causal_remaining) ||
            throw(CyclicBayesNetError(variable_name.(Ref(id), causal_remaining),
                                      causal_remaining))
        ds = [decision_name(id, d)
              for d in decisions(id)
              if subpart(id, d, :decision_variable) in remaining]
        throw(DecisionPrecedenceCycleError(ds))
    end
    position = Dict{Int,Int}(v => i for (i, v) in enumerate(order))
    return sort(decisions(id); by=d -> (position[subpart(id, d, :decision_variable)], d))
end

# No-forgetting
###############

"""
    no_forgetting_arcs(id::AbstractInfluenceDiagram) -> Vector{Pair{Symbol,Symbol}}
    no_forgetting_arcs(m::InfluenceDiagramModel)

The information arcs that are missing for the diagram to have *no-forgetting* (perfect
recall), as `decision => variable` pairs in [`decision_order`](@ref), each decision's
missing variables in the order in which they first became known.

A diagram has no-forgetting when everything known at a decision is still known at every
later decision: for `D_k ≺ D_l`, the information set of `D_l` contains the information
set of `D_k` and the action variable of `D_k`. [Shachter1986](@cite) calls a diagram
with a directed path through all decisions *regular*; no-forgetting is the stronger
property that the algorithms of this package need, and the two terms are kept apart
here.

No-forgetting is *not* checked by [`validate`](@ref): a diagram that forgets is a
well-formed limited-memory influence diagram [LauritzenNilsson2001](@cite) which
[`ExhaustivePolicySearch`](@ref) solves exactly. It is
[`DecisionVariableElimination`](@ref) that needs it, and it reports what is missing as
an [`IrregularDiagramError`](@ref). Use [`with_no_forgetting`](@ref) to add the arcs.

```jldoctest
julia> no_forgetting_arcs(two_stage_diagram())
Pair{Symbol, Symbol}[]

julia> id = syntax(without_information(two_stage_model(), :Drill, :Test));

julia> no_forgetting_arcs(id)
1-element Vector{Pair{Symbol, Symbol}}:
 :Drill => :Test
```
"""
function no_forgetting_arcs(id::AbstractInfluenceDiagram)
    ds = decision_order(id)
    out = Pair{Symbol,Symbol}[]
    known = Int[]
    for d in ds
        have = Set(decision_information(id, d))
        for v in known
            v in have && continue
            push!(out, decision_name(id, d) => variable_name(id, v))
            push!(have, v)
        end
        for v in decision_information(id, d)
            v in known || push!(known, v)
        end
        a = decision_variable(id, d)
        a in known || push!(known, a)
    end
    return out
end

"""
    is_no_forgetting(id::AbstractInfluenceDiagram) -> Bool
    is_no_forgetting(m::InfluenceDiagramModel) -> Bool

Whether the diagram has no-forgetting (perfect recall), that is whether
[`no_forgetting_arcs`](@ref) is empty. Diagrams with a single decision always do.
"""
is_no_forgetting(id::AbstractInfluenceDiagram) = isempty(no_forgetting_arcs(id))
