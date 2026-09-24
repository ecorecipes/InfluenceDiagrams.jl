"""
Graphviz drawings of influence diagrams: chance variables as ellipses, decisions as
boxes, utility nodes as diamonds; causal arcs solid, information arcs dashed, value
arcs solid into the diamond. The result is a `BayesianNetworks.Graphviz.Graph`, which
`show`s as SVG through the Graphviz binaries that BayesianNetworks.jl configures.
"""

const _GV_FONT = "Helvetica"

_gv_string(x) = x isa AbstractString ? String(x) : string(x)
_gv_attrs(d::AbstractDict) = Dict{Symbol,String}(Symbol(k) => _gv_string(v) for (k, v) in d)

"""
    to_graphviz(id::AbstractInfluenceDiagram; kwargs...) -> Graphviz.Graph
    to_graphviz(m::InfluenceDiagramModel; kwargs...)

Draw an influence diagram with Graphviz: one ellipse per chance variable and one box
per action variable, labelled with the name and (with `states = true`) the states; one
diamond per utility node; a solid edge per causal `Input` (parent to target), a dashed
edge per `InformationInput` (information variable to action) and a solid edge per
`UtilityInput` (variable to utility node). Variables with `evidence` are shaded and
labelled `X = x`; hard interventions (`PointMassRef` mechanisms) and the variables in
`intervened` get a double border. On a model, `evidence` and `intervened` default to
the model's. Keyword arguments: `states`, `evidence`, `intervened`, `rankdir = "TB"`,
`name`, and `graph_attrs`, `node_attrs`, `edge_attrs` (merged over the defaults).
"""
function to_graphviz(id::AbstractInfluenceDiagram; states::Bool=true,
                     intervened::AbstractVector{Symbol}=Symbol[],
                     evidence::AbstractDict{Symbol,Symbol}=Dict{Symbol,Symbol}(),
                     rankdir::AbstractString="TB", name::AbstractString="ID",
                     graph_attrs::AbstractDict=Dict{Symbol,String}(),
                     node_attrs::AbstractDict=Dict{Symbol,String}(),
                     edge_attrs::AbstractDict=Dict{Symbol,String}())
    stmts = Graphviz.Statement[]
    for v in variables(id)
        x = variable_name(id, v)
        mech = mechanism_of(id, v)
        ref = mech === nothing ? NoRef() : kernel_ref(id, mech)
        hard = ref isa PointMassRef
        label = hard ? "do($x = $(ref.state))" :
                haskey(evidence, x) ? "$x = $(evidence[x])" : string(x)
        if states && !hard && !haskey(evidence, x)
            label *= "\\n{" * join(BayesianNetworks.states(id, v), ", ") * "}"
        end
        attrs = Dict{Symbol,String}(:label => label, :style => "filled",
                                    :shape => is_decision(id, v) ? "box" : "ellipse")
        if hard || x in intervened
            attrs[:peripheries] = "2"
            attrs[:color] = "firebrick"
        end
        haskey(evidence, x) && (attrs[:fillcolor] = "lightgrey")
        push!(stmts, Graphviz.Node("v$v", attrs))
    end
    for u in utilities(id)
        push!(stmts,
              Graphviz.Node("u$u",
                            Dict{Symbol,String}(:label => string(utility_name(id, u)),
                                                :shape => "diamond", :style => "filled",
                                                :fillcolor => "lightyellow")))
    end
    for mech in mechanisms(id), p in inputs(id, mech)
        push!(stmts, Graphviz.Edge(["v$p", "v$(target(id, mech))"]))
    end
    for i in parts(id, :InformationInput)
        d = subpart(id, i, :information_decision)
        push!(stmts,
              Graphviz.Edge(["v$(subpart(id, i, :information_variable))",
                             "v$(subpart(id, d, :decision_variable))"],
                            Dict{Symbol,String}(:style => "dashed")))
    end
    for i in parts(id, :UtilityInput)
        push!(stmts,
              Graphviz.Edge(["v$(subpart(id, i, :utility_variable))",
                             "u$(subpart(id, i, :utility_node))"]))
    end
    return Graphviz.Digraph(String(name), stmts; prog="dot",
                            graph_attrs=merge(Dict{Symbol,String}(:rankdir => String(rankdir),
                                                                  :fontname => _GV_FONT),
                                              _gv_attrs(graph_attrs)),
                            node_attrs=merge(Dict{Symbol,String}(:fontname => _GV_FONT,
                                                                 :fillcolor => "white",
                                                                 :margin => "0.1,0.05"),
                                             _gv_attrs(node_attrs)),
                            edge_attrs=merge(Dict{Symbol,String}(:arrowsize => "0.7",
                                                                 :fontname => _GV_FONT),
                                             _gv_attrs(edge_attrs)))
end

function to_graphviz(m::InfluenceDiagramModel; intervened=intervened_variables(m),
                     evidence=BayesianNetworks.evidence(m), kw...)
    return to_graphviz(syntax(m); intervened=intervened, evidence=evidence, kw...)
end
