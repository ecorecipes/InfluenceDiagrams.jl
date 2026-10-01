"""
Structural validation of influence diagrams (SPEC §37). The chance part is checked by
BayesianNetworks.jl; the decision part adds the checks below. Model-level checks
(utility references, policy signatures, strategy completeness: items 7, 9 and 10) live
with the model in `model.jl`.

Correspondence with SPEC §37:

1. every decision controls exactly one action variable: one by construction (the hom
   `decision_variable`), and at most one decision per variable
   ([`DecisionUniquenessError`](@ref) `:duplicate_decision`);
2. action variables have no chance mechanism ([`DecisionUniquenessError`](@ref)
   `:has_mechanism`);
3. information inputs reference valid variables (`DanglingReferenceError`) and are
   neither the decision's own action nor repeated ([`InvalidInformationSetError`](@ref));
4. information is available before the decision: no information variable is downstream
   of the action in [`information_graph`](@ref) ([`InvalidInformationSetError`](@ref)
   `:downstream`);
5. utility nodes have no children: utilities are not variables, so nothing in the
   schema can point at one; this holds by construction;
6. utility inputs reference valid variables (`DanglingReferenceError`) without
   repetition ([`UtilityScopeError`](@ref) `:duplicate`);
7. utility references resolve: `validate(::InfluenceDiagramModel; semantics = true)`;
8. decision precedence is acyclic and consistent with the arcs
   ([`DecisionPrecedenceCycleError`](@ref));
9. policies match information and action spaces: [`validate_policy`](@ref);
10. complete strategies: `validate(::InfluenceDiagramModel; strategy = true)`;
11. the causal wiring is acyclic with actions exogenous (`CyclicBayesNetError`, from the
    Bayesian-network checks, where actions are simply variables without a mechanism);
12. information wiring is never compiled as causal wiring: `InformationInput` and
    `Input` are different objects, `variable_graph` ignores the former and
    [`instantiate`](@ref) turns information inputs into the inputs of a policy
    mechanism only when a policy is supplied.
"""

_in_range(id, ob::Symbol, x::Int) = 1 <= x <= nparts(id, ob)

function _check_id_references!(errs, id::AbstractInfluenceDiagram)
    ok = true
    check = (ob, p, hom, codom) -> begin
        x = subpart(id, p, hom)
        if !_in_range(id, codom, x)
            push!(errs, DanglingReferenceError(ob, p, hom, x))
            ok = false
        end
    end
    for d in parts(id, :Decision)
        check(:Decision, d, :decision_variable, :Variable)
    end
    for i in parts(id, :InformationInput)
        check(:InformationInput, i, :information_decision, :Decision)
        check(:InformationInput, i, :information_variable, :Variable)
    end
    for i in parts(id, :UtilityInput)
        check(:UtilityInput, i, :utility_node, :Utility)
        check(:UtilityInput, i, :utility_variable, :Variable)
    end
    for p in parts(id, :DecisionPrecedence)
        check(:DecisionPrecedence, p, :earlier, :Decision)
        check(:DecisionPrecedence, p, :later, :Decision)
    end
    return ok
end

function _check_decisions!(errs, id::AbstractInfluenceDiagram, closed::Bool)
    for v in parts(id, :Variable)
        ds = incident(id, v, :decision_variable)
        ms = incident(id, v, :target)
        if length(ds) > 1
            push!(errs,
                  DecisionUniquenessError(subpart(id, ds[2], :decision_name),
                                          variable_name(id, v), :duplicate_decision))
        end
        if !isempty(ds) && !isempty(ms)
            push!(errs,
                  DecisionUniquenessError(subpart(id, first(ds), :decision_name),
                                          variable_name(id, v), :has_mechanism))
        end
        if closed && isempty(ds) && isempty(ms)
            push!(errs, MissingMechanismError(variable_name(id, v), v))
        end
    end
end

function _check_id_positions!(errs, id::AbstractInfluenceDiagram)
    for d in parts(id, :Decision)
        members = incident(id, d, :information_decision)
        isempty(members) && continue
        positions = sort(Int[subpart(id, i, :information_position) for i in members])
        positions == 1:length(positions) ||
            push!(errs,
                  PositionError(:InformationInput, subpart(id, d, :decision_name), d,
                                positions))
    end
    for u in parts(id, :Utility)
        members = incident(id, u, :utility_node)
        isempty(members) && continue
        positions = sort(Int[subpart(id, i, :utility_position) for i in members])
        positions == 1:length(positions) ||
            push!(errs,
                  PositionError(:UtilityInput, subpart(id, u, :utility_name), u, positions))
    end
end

function _check_information_sets!(errs, id::AbstractInfluenceDiagram)
    for d in parts(id, :Decision)
        dname = subpart(id, d, :decision_name)
        a = subpart(id, d, :decision_variable)
        seen = Set{Int}()
        for i in information_ids(id, d)
            v = subpart(id, i, :information_variable)
            if v == a
                push!(errs, InvalidInformationSetError(dname, variable_name(id, v), :self))
            elseif v in seen
                push!(errs,
                      InvalidInformationSetError(dname, variable_name(id, v), :duplicate))
            end
            push!(seen, v)
        end
    end
end

function _check_utility_scopes!(errs, id::AbstractInfluenceDiagram)
    for u in parts(id, :Utility)
        seen = Set{Int}()
        for i in utility_input_ids(id, u)
            v = subpart(id, i, :utility_variable)
            v in seen &&
                push!(errs,
                      UtilityScopeError(subpart(id, u, :utility_name), :duplicate,
                                        unique(utility_scope(id, u)),
                                        utility_scope(id, u)))
            push!(seen, v)
        end
    end
end

# Items 4, 8 and 11 together: the combined graph must be acyclic. When it is not, the
# reason is reported as precisely as possible.
function _check_information_order!(errs, id::AbstractInfluenceDiagram)
    is_acyclic(id) || return nothing   # the causal cycle is already reported
    g = information_graph(id)
    _, remaining = _kahn(g)
    isempty(remaining) && return nothing
    # Availability is judged on causal and information arcs alone; a contradiction
    # that only appears once the explicit precedence is added is a precedence error.
    g_arcs = _arc_graph(id)
    found = false
    for d in parts(id, :Decision)
        a = subpart(id, d, :decision_variable)
        down = Set(_reachable(g_arcs, a))
        for v in decision_information(id, d)
            (v in down || v == a) || continue
            push!(errs,
                  InvalidInformationSetError(subpart(id, d, :decision_name),
                                             variable_name(id, v), :downstream))
            found = true
        end
    end
    found && return nothing
    ds = [subpart(id, d, :decision_name)
          for d in parts(id, :Decision)
          if subpart(id, d, :decision_variable) in remaining]
    push!(errs, DecisionPrecedenceCycleError(ds))
    return nothing
end

function _check_precedence!(errs, id::AbstractInfluenceDiagram)
    n = nparts(id, :Decision)
    g = SimpleDiGraph{Int}(n)
    for p in parts(id, :DecisionPrecedence)
        add_edge!(g, subpart(id, p, :earlier), subpart(id, p, :later))
    end
    _, remaining = _kahn(g)
    isempty(remaining) ||
        push!(errs,
              DecisionPrecedenceCycleError([subpart(id, d, :decision_name)
                                            for d in remaining]))
    return nothing
end

function _check_id_names!(errs, id::AbstractInfluenceDiagram)
    for (ob, attr) in ((:Decision, :decision_name), (:Utility, :utility_name))
        groups = Dict{Symbol,Vector{Int}}()
        for p in parts(id, ob)
            push!(get!(groups, subpart(id, p, attr), Int[]), p)
        end
        for name in sort!(collect(keys(groups)))
            ids = groups[name]
            length(ids) > 1 && push!(errs, DuplicateNameError(ob, name, ids))
        end
    end
end

"""
    validation_errors(id::AbstractInfluenceDiagram; closed = false, unique_names = false) -> Vector{Exception}

All structural problems of the influence diagram `id`, in a deterministic order,
without stopping at the first: the checks of `validation_errors(::AbstractBayesNet)`
on the chance part (with `closed = false`, so that action variables may lack a
mechanism), then the influence-diagram checks of SPEC §37 listed in the module
documentation of `validation.jl`. A `Label` or `Position` attribute without a value,
which only an ACSet built part by part can have, is a `MissingAttributeError`; the checks
that read attributes are then skipped, and only the reference checks run. With
`closed = true` every variable must have exactly
one generator, a chance mechanism or a decision (`MissingMechanismError` otherwise).
With `unique_names = true` decision and utility names must be unique as well as
variable and mechanism names (`DuplicateNameError`).
"""
function validation_errors(id::AbstractInfluenceDiagram; closed::Bool=false,
                           unique_names::Bool=false)
    errs = invoke(validation_errors, Tuple{AbstractBayesNet}, id; closed=false,
                  unique_names=unique_names)
    refs_ok = _check_id_references!(errs, id)
    # The chance-part checks cover every `Label` and `Position` attribute of the diagram's
    # schema, `decision_name` to `utility_position` included; the checks below read them.
    any(e -> e isa MissingAttributeError, errs) && return errs
    _check_decisions!(errs, id, closed)
    _check_id_positions!(errs, id)
    if refs_ok
        _check_information_sets!(errs, id)
        _check_utility_scopes!(errs, id)
        _check_precedence!(errs, id)
        _check_information_order!(errs, id)
    end
    unique_names && _check_id_names!(errs, id)
    return errs
end

@doc """
    validate(id::AbstractInfluenceDiagram; closed = false, unique_names = false) -> Nothing

Check the structural invariants of an influence diagram and throw the first violation
as a typed exception; return `nothing` when the diagram is valid. See
[`validation_errors`](@ref) for the checks. `closed = true` requires every variable to
have exactly one generator (chance mechanism or decision), which is what
[`instantiate`](@ref) needs.
""" validate(::AbstractInfluenceDiagram)
