"""
JSON serialisation of structural influence diagrams, in the same envelope as
BayesianNetworks.jl's `json_bayesnet` (SPEC §48) with the format name
`"influence-diagram-acset"`.
"""

const JSON_FORMAT = "influence-diagram-acset"
const JSON_SCHEMA_VERSION = "0.1"

"""
    json_influence_diagram(id) -> String

Serialise `id` as `{"format": "influence-diagram-acset", "schema_version": "0.1",
"acset": ...}` where `acset` is the ACSets.jl JSON representation; `KernelRef`
attributes are written as objects with a `"type"` discriminator. Inverse of
[`parse_json_influence_diagram`](@ref).
"""
function json_influence_diagram(id::AbstractInfluenceDiagram)
    return JSON3.write((format=JSON_FORMAT, schema_version=JSON_SCHEMA_VERSION,
                        acset=generate_json_acset(id)))
end

"""
    parse_json_influence_diagram(str; type = InfluenceDiagram) -> type

Parse a JSON string produced by [`json_influence_diagram`](@ref). Throws
`BayesianNetworks.FormatError` if `str` is not JSON, or if the envelope is missing or
names another format or schema version. An error inside the `"acset"` body is not
converted: it comes unchanged from ACSets' `parse_json_acset`.
"""
function parse_json_influence_diagram(str::AbstractString;
                                      type::Type{<:AbstractInfluenceDiagram}=InfluenceDiagram)
    return _parse_envelope(BayesianNetworks._read_json(str), type)
end

function _parse_envelope(obj, type)
    obj isa AbstractDict || throw(FormatError("expected a JSON object envelope"))
    for key in (:format, :schema_version, :acset)
        haskey(obj, key) || throw(FormatError("envelope is missing the \"$key\" key"))
    end
    obj[:format] == JSON_FORMAT ||
        throw(FormatError("format is \"$(obj[:format])\", expected \"$JSON_FORMAT\""))
    obj[:schema_version] == JSON_SCHEMA_VERSION ||
        throw(FormatError("schema_version is \"$(obj[:schema_version])\", expected \"$JSON_SCHEMA_VERSION\""))
    return parse_json_acset(type, obj[:acset])
end

"""
    write_json_influence_diagram(path, id) -> path

Write [`json_influence_diagram`](@ref)`(id)` to the file at `path`.
"""
function write_json_influence_diagram(path::AbstractString, id::AbstractInfluenceDiagram)
    open(path, "w") do io
        return write(io, json_influence_diagram(id))
    end
    return path
end

"""
    read_json_influence_diagram(path; type = InfluenceDiagram) -> type

Read a diagram written by [`write_json_influence_diagram`](@ref). Errors as for
[`parse_json_influence_diagram`](@ref).
"""
function read_json_influence_diagram(path::AbstractString;
                                     type::Type{<:AbstractInfluenceDiagram}=InfluenceDiagram)
    return _parse_envelope(BayesianNetworks._read_json(read(path, String)), type)
end

"""
    canonicalize(id::AbstractInfluenceDiagram) -> typeof(id)

A copy of `id` whose parts are renumbered deterministically: the chance part as
`canonicalize(::AbstractBayesNet)` (variables by name, states by position, mechanisms
by target and name, inputs by position), then decisions by `(action variable,
decision_name)`, information inputs by `(decision, information_position)`, utilities by
`utility_name`, utility inputs by `(utility, utility_position)` and precedence rows by
`(earlier, later)`. Two diagrams that differ only in construction order have `==`
canonical forms; [`is_isomorphic`](@ref) compares them.
"""
function canonicalize(id::AbstractInfluenceDiagram)
    return BayesianNetworks._canonical_copy(id,
                                            sort(variables(id);
                                                 by=v -> (variable_name(id, v), v)))
end

function BayesianNetworks._canonical_copy(id::AbstractInfluenceDiagram,
                                          old_vars::AbstractVector{Int})
    out = constructor(id)()
    new_var = Dict{Int,Int}()
    for v in old_vars
        new_var[v] = add_part!(out, :Variable; variable_name=variable_name(id, v),
                               space_ref=subpart(id, v, :space_ref))
        for s in BayesianNetworks.state_ids(id, v)
            add_part!(out, :State; state_variable=new_var[v],
                      state_name=subpart(id, s, :state_name),
                      state_position=subpart(id, s, :state_position))
        end
    end
    old_mechs = sort(mechanisms(id);
                     by=m -> (get(new_var, subpart(id, m, :target), 0),
                              mechanism_name(id, m), m))
    for m in old_mechs
        new_m = add_part!(out, :Mechanism; target=get(new_var, subpart(id, m, :target), 0),
                          mechanism_name=mechanism_name(id, m),
                          kernel_ref=subpart(id, m, :kernel_ref))
        for i in BayesianNetworks.input_ids(id, m)
            add_part!(out, :Input; input_mechanism=new_m,
                      input_variable=get(new_var, subpart(id, i, :input_variable), 0),
                      input_position=subpart(id, i, :input_position))
        end
    end
    new_dec = Dict{Int,Int}()
    old_decs = sort(decisions(id);
                    by=d -> (get(new_var, subpart(id, d, :decision_variable), 0),
                             subpart(id, d, :decision_name), d))
    for d in old_decs
        new_dec[d] = add_part!(out, :Decision;
                               decision_variable=get(new_var,
                                                     subpart(id, d, :decision_variable),
                                                     0),
                               decision_name=subpart(id, d, :decision_name))
        for i in information_ids(id, d)
            add_part!(out, :InformationInput; information_decision=new_dec[d],
                      information_variable=get(new_var,
                                               subpart(id, i, :information_variable), 0),
                      information_position=subpart(id, i, :information_position))
        end
    end
    old_utils = sort(utilities(id);
                     by=u -> (subpart(id, u, :utility_name),
                              repr(subpart(id, u, :utility_ref)),
                              Tuple((subpart(id, i, :utility_position),
                                     get(new_var, subpart(id, i, :utility_variable), 0))
                                    for i in utility_input_ids(id, u))))
    for u in old_utils
        new_u = add_part!(out, :Utility; utility_name=subpart(id, u, :utility_name),
                          utility_ref=subpart(id, u, :utility_ref))
        for i in utility_input_ids(id, u)
            add_part!(out, :UtilityInput; utility_node=new_u,
                      utility_variable=get(new_var, subpart(id, i, :utility_variable), 0),
                      utility_position=subpart(id, i, :utility_position))
        end
    end
    prec = sort([(get(new_dec, subpart(id, p, :earlier), 0),
                  get(new_dec, subpart(id, p, :later), 0))
                 for p in parts(id, :DecisionPrecedence)])
    for (e, l) in prec
        add_part!(out, :DecisionPrecedence; earlier=e, later=l)
    end
    return out
end

"""
    is_isomorphic(a::AbstractInfluenceDiagram, b::AbstractInfluenceDiagram; max_orderings=100_000) -> Bool

Whether two diagrams are the same up to renumbering of parts, as equality of their
[`canonicalize`](@ref)d forms (exact when variable, mechanism, decision and utility
names are unique; otherwise a bounded search over equally named variables decides).
Every candidate retains decision information, utility scopes/references and
precedence rows. `max_orderings` has the same meaning as for Bayesian networks.
"""
function is_isomorphic(a::AbstractInfluenceDiagram, b::AbstractInfluenceDiagram;
                       max_orderings::Integer=100_000)
    canonicalize(a) == canonicalize(b) && return true
    _names_unique(a) && _names_unique(b) && return false
    return BayesianNetworks._isomorphic_by_search(a, b, max_orderings)
end

function _names_unique(id::AbstractInfluenceDiagram)
    return allunique(subpart(id, :variable_name)) &&
           allunique(subpart(id, :mechanism_name)) &&
           allunique(subpart(id, :decision_name)) && allunique(subpart(id, :utility_name))
end
