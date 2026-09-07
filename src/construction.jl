"""
Mutating builders (`add_*!`) for the influence-diagram objects and the
`influence_diagram` DSL, mirroring `bayesnet` and the `add_*!` functions of
BayesianNetworks.jl. The `!` functions return the id of the part they create;
everything else in the package treats diagrams as immutable values.
"""

# Resolving user-facing identifiers
###################################

_variable_id(::AbstractVariableSpace, v::Integer) = Int(v)
_variable_id(id::AbstractVariableSpace, name::Symbol) = variable_id(id, name)

_decision_id(::AbstractInfluenceDiagram, d::Integer) = Int(d)
_decision_id(id::AbstractInfluenceDiagram, name::Symbol) = decision_id(id, name)

_utility_id(::AbstractInfluenceDiagram, u::Integer) = Int(u)
_utility_id(id::AbstractInfluenceDiagram, name::Symbol) = utility_id(id, name)

"""
    decision_id(id, name::Symbol) -> Int

Part id of the decision called `name`, or, when no decision has that name, of the
decision controlling the variable called `name`. Throws [`UnknownDecisionError`](@ref)
if there is none and `DuplicateNameError` if several decisions share the name.
"""
function decision_id(id::AbstractInfluenceDiagram, name::Symbol)
    ds = findall(==(name), subpart(id, :decision_name))
    length(ds) > 1 && throw(DuplicateNameError(:Decision, name, ds))
    isempty(ds) || return first(ds)
    if has_variable(id, name)
        d = decision_of(id, variable_id(id, name))
        d === nothing || return d
    end
    return throw(UnknownDecisionError(name))
end

"""
    utility_id(id, name::Symbol) -> Int

Part id of the utility node called `name`. Throws [`UnknownUtilityError`](@ref) if
there is none and `DuplicateNameError` if there are several.
"""
function utility_id(id::AbstractInfluenceDiagram, name::Symbol)
    us = findall(==(name), subpart(id, :utility_name))
    isempty(us) && throw(UnknownUtilityError(name))
    length(us) > 1 && throw(DuplicateNameError(:Utility, name, us))
    return first(us)
end

# Builders
##########

"""
    add_decision!(id, variable; information = Symbol[], name = variable's name) -> Int

Declare `variable` (a name or part id) as the action variable of a new decision called
`name` (by default the variable's name), informed by the variables `information` in the
given order (information positions `1:length(information)`), and return the decision's
part id. The variable keeps whatever mechanism it has; a decision whose action variable
has a chance mechanism is a validation error, not a construction error.
"""
function add_decision!(id::AbstractInfluenceDiagram, variable;
                       information::AbstractVector=Symbol[],
                       name::Symbol=_display_name(id, variable))
    v = _variable_id(id, variable)
    d = add_part!(id, :Decision; decision_variable=v, decision_name=name)
    for (i, x) in enumerate(information)
        add_part!(id, :InformationInput; information_decision=d,
                  information_variable=_variable_id(id, x), information_position=i)
    end
    return d
end

_display_name(::AbstractVariableSpace, name::Symbol) = name
_display_name(id::AbstractVariableSpace, v::Integer) = subpart(id, Int(v), :variable_name)

"""
    add_information!(id, decision, variable; position = ninformation + 1) -> Int

Append `variable` to the information set of `decision` (both names or part ids; the
decision may also be named by its action variable) and return the new
`InformationInput` part id.
"""
function add_information!(id::AbstractInfluenceDiagram, decision, variable;
                          position::Integer=length(incident(id, _decision_id(id, decision),
                                                            :information_decision)) + 1)
    d = _decision_id(id, decision)
    v = _variable_id(id, variable)
    return add_part!(id, :InformationInput; information_decision=d,
                     information_variable=v, information_position=Int(position))
end

"""
    add_utility!(id, name; scope = Symbol[], utility_ref = NoRef()) -> Int

Add a utility node called `name` reading the variables `scope` in the given order
(utility positions `1:length(scope)`) and return its part id. Utilities are not
variables: they have no states and can never be parents.
"""
function add_utility!(id::AbstractInfluenceDiagram, name::Symbol;
                      scope::AbstractVector=Symbol[], utility_ref=NoRef())
    u = add_part!(id, :Utility; utility_name=name, utility_ref=utility_ref)
    for (i, x) in enumerate(scope)
        add_part!(id, :UtilityInput; utility_node=u, utility_variable=_variable_id(id, x),
                  utility_position=i)
    end
    return u
end

"""
    add_utility_input!(id, utility, variable; position = nscope + 1) -> Int

Append `variable` to the scope of utility node `utility` (names or part ids) and return
the new `UtilityInput` part id.
"""
function add_utility_input!(id::AbstractInfluenceDiagram, utility, variable;
                            position::Integer=length(incident(id, _utility_id(id, utility),
                                                              :utility_node)) + 1)
    u = _utility_id(id, utility)
    v = _variable_id(id, variable)
    return add_part!(id, :UtilityInput; utility_node=u, utility_variable=v,
                     utility_position=Int(position))
end

"""
    add_precedence!(id, earlier => later) -> Int

Record that decision `earlier` is taken before decision `later` (names or part ids) and
return the `DecisionPrecedence` part id. Precedence is also induced by the arcs
(an action that informs, or causally affects an information variable of, another
decision precedes it); explicit rows are needed only to order otherwise unordered
decisions. Cycles are reported by [`validate`](@ref).
"""
function add_precedence!(id::AbstractInfluenceDiagram, p::Pair)
    e = _decision_id(id, first(p))
    l = _decision_id(id, last(p))
    return add_part!(id, :DecisionPrecedence; earlier=e, later=l)
end

# DSL
#####

_name_list(x::Symbol) = [x]
_name_list(x::Tuple) = collect(Symbol, x)
_name_list(x::AbstractVector) = collect(Symbol, x)

"""
    influence_diagram(variables...; mechanisms = [], decisions = [], utilities = [],
                      precedence = [], closed = true, space_refs = Dict(),
                      kernel_refs = Dict(), utility_refs = Dict()) -> InfluenceDiagram

Build an [`InfluenceDiagram`](@ref) from `name => states` pairs and

- `mechanisms`: `target => parents` pairs as in `bayesnet` (parents a name, tuple or
  vector, in `input_position` order);
- `decisions`: `action_variable => information` pairs (information a name, tuple or
  vector, in `information_position` order; the decision is named after its variable);
- `utilities`: `utility_name => scope` pairs (scope in `utility_position` order);
- `precedence`: `earlier => later` pairs of decision names.

With `closed = true` (the default) every variable that is neither a mechanism target
nor an action variable receives a mechanism without inputs, so the chance part is a
closed network. `space_refs`, `kernel_refs` and `utility_refs` map names to references;
anything not listed gets `NoRef()`.

# Example

```jldoctest
julia> id = influence_diagram(:Weather => [:sunny, :rainy], :Forecast => [:sunny, :cloudy, :rainy],
                              :Umbrella => [:take, :leave];
                              mechanisms = [:Forecast => :Weather],
                              decisions = [:Umbrella => :Forecast],
                              utilities = [:U => (:Weather, :Umbrella)]);

julia> variable_name.(Ref(id), action_variables(id)), variable_name.(Ref(id), chance_variables(id))
([:Umbrella], [:Weather, :Forecast])

julia> validate(id; closed = true)
```
"""
function influence_diagram(variables::Pair{Symbol,<:AbstractVector{Symbol}}...;
                           mechanisms::AbstractVector=Pair{Symbol,Any}[],
                           decisions::AbstractVector=Pair{Symbol,Any}[],
                           utilities::AbstractVector=Pair{Symbol,Any}[],
                           precedence::AbstractVector=Pair{Symbol,Symbol}[],
                           closed::Bool=true, space_refs=Dict{Symbol,KernelRef}(),
                           kernel_refs=Dict{Symbol,KernelRef}(),
                           utility_refs=Dict{Symbol,KernelRef}())
    id = InfluenceDiagram()
    for (name, sts) in variables
        add_variable!(id, name; states=sts, space_ref=get(space_refs, name, NoRef()))
    end
    generated = Set{Symbol}()
    for (t, ps) in mechanisms
        add_mechanism!(id, t; inputs=_name_list(ps),
                       kernel_ref=get(kernel_refs, t, NoRef()))
        push!(generated, t)
    end
    for (a, info) in decisions
        add_decision!(id, a; information=_name_list(info))
        push!(generated, a)
    end
    if closed
        for (name, _) in variables
            name in generated && continue
            add_mechanism!(id, name; kernel_ref=get(kernel_refs, name, NoRef()))
        end
    end
    for (u, sc) in utilities
        add_utility!(id, u; scope=_name_list(sc), utility_ref=get(utility_refs, u, NoRef()))
    end
    for p in precedence
        add_precedence!(id, p)
    end
    return id
end
