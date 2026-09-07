"""
Bridge to BayesianNetworkFormats.jl: a `NetworkIR` with decision and utility nodes
(Netica `.dne`, GeNIe `.xdsl`, HUGIN `.net`) becomes an `InfluenceDiagramModel` and
back. Chance nodes are variables with mechanisms, decision nodes are variables with a
decision whose information set is the node's parent list (in order), utility nodes are
utility nodes whose scope is the parent list and whose table becomes a
[`TabularUtility`](@ref). Titles, positions, comments and format extras are kept in
`extras(m)` as BayesianNetworks.jl does, so a round trip through the IR is lossless.
"""

# The metadata layout of `BayesianNetworks.ir_extras`, plus the multi-attribute utility
# nodes, which only influence diagrams carry.
function _ir_extras(ir::NetworkIR)
    ex = BayesianNetworks.ir_extras(ir)
    ex[:mau] = copy(ir.mau)
    return ex
end

_extra(m, key::Symbol, default) = get(extras(m), key, default)

"""
    InfluenceDiagramModel(ir::NetworkIR; atol = 1e-6, renormalize = false) -> InfluenceDiagramModel

Build a model from a `NetworkIR`: chance nodes become variables with a mechanism
(parents in IR order, name `Symbol(id, "_mechanism")`) and the kernel bound with
`bind_cpt` from the node's table (a missing table leaves the mechanism unbound);
decision nodes become variables with a decision of the same name whose information
set is the node's parents, in order; utility nodes become utility nodes whose scope is
the parent list, bound to a [`TabularUtility`](@ref) when the node has a table. A
multi-attribute utility node is accepted only with unit weights
([`UnsupportedAggregationError`](@ref) otherwise), since aggregation is additive. The
network name, format, source, titles, positions, comments and extras are stored in
`extras` in the layout of `BayesianNetworks.ir_extras`, with the multi-attribute utility
nodes under `:mau`.
"""
function InfluenceDiagramModel(ir::NetworkIR; atol::Real=1e-6, renormalize::Bool=false)
    for mau in ir.mau
        all(w -> isapprox(w, 1.0; atol=atol), mau.weights) ||
            throw(UnsupportedAggregationError(mau.id, mau.weights))
    end
    id = InfluenceDiagram()
    for v in ir.variables
        v.kind == UtilityNode && continue
        add_variable!(id, v.id; states=Symbol.(v.states))
    end
    for v in ir.variables
        if v.kind == ChanceNode
            add_mechanism!(id, v.id; inputs=v.parents, name=Symbol(v.id, "_mechanism"))
        elseif v.kind == DecisionNode
            add_decision!(id, v.id; information=v.parents)
        else
            add_utility!(id, v.id; scope=v.parents)
        end
    end
    m = InfluenceDiagramModel(id; extras=_ir_extras(ir))
    for v in ir.variables
        v.table === nothing && continue
        if v.kind == ChanceNode
            m = bind_cpt(m, v.id => v.table; atol=atol, renormalize=renormalize)
        elseif v.kind == UtilityNode
            m = bind_utility(m, v.id => v.table)
        end
    end
    return m
end

"""
    NetworkIR(m::InfluenceDiagramModel; name = extras(m)[:name]) -> NetworkIR

The model as a `NetworkIR`: chance variables as chance nodes (parents in
`input_position` order, table `cpt(kernel)` when the kernel resolves), action
variables as decision nodes (parents = information set in `information_position`
order), utility nodes as utility nodes (parents = scope, table = the bound utility
tabulated over it, `nothing` when unbound), in part-id order with utilities last.
Titles, positions, comments, deterministic flags, extras and any multi-attribute
utility nodes are read back from `extras`. Evidence, history and the strategy
are not part of the IR.
"""
function NetworkIR(m::InfluenceDiagramModel;
                   name::AbstractString=_extra(m, :name, "influence_diagram"))
    id = syntax(m)
    bm = m.model
    titles = _extra(m, :titles, Dict{Symbol,String}())
    positions = _extra(m, :positions, Dict{Symbol,Any}())
    comments = _extra(m, :comments, Dict{Symbol,String}())
    deterministic = _extra(m, :deterministic, Symbol[])
    vextras = _extra(m, :variable_extras, Dict{Symbol,Dict{Symbol,Any}}())
    vars = IRVariable[]
    for v in variables(id)
        x = variable_name(id, v)
        d = decision_of(id, v)
        if d === nothing
            mech = mechanism_of(id, v)
            table = nothing
            ps = Symbol[]
            if mech !== nothing
                ps = Symbol[variable_name(id, p) for p in inputs(id, mech)]
                k = try
                    kernel(bm, x)
                catch e
                    e isa MissingKernelError || rethrow()
                    nothing
                end
                k === nothing || (table = cpt(k))
            end
            push!(vars,
                  IRVariable(x; title=get(titles, x, ""), states=string.(states(id, v)),
                             parents=ps, table=table, deterministic=x in deterministic,
                             position=get(positions, x, nothing),
                             comment=get(comments, x, ""),
                             extras=get(vextras, x, Dict{Symbol,Any}())))
        else
            push!(vars,
                  IRVariable(x; title=get(titles, x, ""), kind=DecisionNode,
                             states=string.(states(id, v)),
                             parents=information_names(id, d),
                             position=get(positions, x, nothing),
                             comment=get(comments, x, ""),
                             extras=get(vextras, x, Dict{Symbol,Any}())))
        end
    end
    for u in utilities(id)
        name_u = utility_name(id, u)
        table = haskey(m.utilities, name_u) ?
                utility_table(m.utilities[name_u], _utility_axes(m, u)) : nothing
        push!(vars,
              IRVariable(name_u; title=get(titles, name_u, ""), kind=UtilityNode,
                         parents=utility_scope_names(id, u), table=table,
                         position=get(positions, name_u, nothing),
                         comment=get(comments, name_u, ""),
                         extras=get(vextras, name_u, Dict{Symbol,Any}())))
    end
    return NetworkIR(name, vars; format=_extra(m, :format, :ir),
                     source=_extra(m, :source, ""), mau=_extra(m, :mau, MAUNode[]),
                     extras=_extra(m, :network_extras, Dict{Symbol,Any}()))
end

"""
    read_influence_diagram(path; format = nothing, strict = true, atol = 1e-6, renormalize = false) -> InfluenceDiagramModel

`InfluenceDiagramModel(read_network(path; ...))`: read an influence diagram (or a
plain network) in any format supported by BayesianNetworkFormats.jl, detected from
the extension unless `format` is given, and bind its tables and utilities.

```julia
m = read_influence_diagram(fixture_path("dne/umbrella.dne"))
optimize(m).expected_utility   # 77.0
```
"""
function read_influence_diagram(path::AbstractString; atol::Real=1e-6,
                                renormalize::Bool=false, kw...)
    ir = read_network(path; atol=atol, renormalize=renormalize, kw...)
    return InfluenceDiagramModel(ir; atol=atol, renormalize=renormalize)
end

"""
    write_influence_diagram(path, m::InfluenceDiagramModel; format = nothing, name = extras(m)[:name]) -> path

`write_network(path, NetworkIR(m; name); format)`: write the model in the format given
or detected from the extension of `path` (`.dne`, `.xdsl` and `.net` carry decision
and utility nodes).
"""
function write_influence_diagram(path::AbstractString, m::InfluenceDiagramModel;
                                 format=nothing,
                                 name::AbstractString=_extra(m, :name, "influence_diagram"))
    return write_network(path, NetworkIR(m; name=name); format=format)
end
