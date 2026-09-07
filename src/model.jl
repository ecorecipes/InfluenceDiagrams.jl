"""
The `InfluenceDiagramModel` wrapper: an influence diagram with its semantics. It
composes a `BayesModel` over the [`InfluenceDiagram`](@ref) syntax (spaces, chance
kernels, evidence, history, extras, exactly as in BayesianNetworks.jl) with the bound
utilities and the current [`Strategy`](@ref). Decision operations (SPEC §41) edit the
strategy and never the syntax, except `do_intervention` on an action variable, which
is a physical override that removes the decision (revision note on SPEC §41).

Models are immutable values: every operation returns a new model.
"""

"""
    InfluenceDiagramModel{S<:AbstractInfluenceDiagram}

An influence diagram with semantics: `model::BayesModel{S, FiniteSpace, FiniteKernel}`
carries the syntax, the spaces, the chance kernels, the evidence and the history;
`utilities` maps utility-node names to bound [`AbstractUtility`](@ref)s; `strategy`
holds the current policies.

`InfluenceDiagramModel(id)` builds the spaces from the syntax and starts with no
kernels, no utilities and an empty strategy; `InfluenceDiagramModel(bm::BayesModel)`
wraps an existing model whose syntax is an influence diagram. Both accept the keywords
`utilities` and `strategy`, and the first also `spaces`, `kernels`, `evidence`,
`history` and `extras` as `BayesModel` does.

# Example

```jldoctest
julia> m = umbrella_model();

julia> m2 = fix_decision(m, :Umbrella => :take);

julia> expected_utility(m2)
35.0

julia> strategy(m)   # the original is untouched
Strategy()
```
"""
struct InfluenceDiagramModel{S<:AbstractInfluenceDiagram}
    model::BayesModel{S,FiniteSpace,FiniteKernel}
    utilities::Dict{Symbol,AbstractUtility}
    strategy::Strategy
end

function InfluenceDiagramModel(bm::BayesModel{S,FiniteSpace,FiniteKernel};
                               utilities::AbstractDict{Symbol}=Dict{Symbol,AbstractUtility}(),
                               strategy::Strategy=Strategy()) where {S<:AbstractInfluenceDiagram}
    return InfluenceDiagramModel{S}(bm, Dict{Symbol,AbstractUtility}(utilities), strategy)
end

function InfluenceDiagramModel(id::S;
                               utilities::AbstractDict{Symbol}=Dict{Symbol,AbstractUtility}(),
                               strategy::Strategy=Strategy(),
                               kw...) where {S<:AbstractInfluenceDiagram}
    return InfluenceDiagramModel(BayesModel(id; kw...); utilities=utilities,
                                 strategy=strategy)
end

function _with(m::InfluenceDiagramModel; model=m.model, utilities=m.utilities,
               strategy=m.strategy)
    return InfluenceDiagramModel(model; utilities=copy(utilities),
                                 strategy=Strategy(copy(policies(strategy))))
end

function Base.:(==)(a::InfluenceDiagramModel, b::InfluenceDiagramModel)
    return a.model == b.model && a.utilities == b.utilities && a.strategy == b.strategy
end
function Base.hash(m::InfluenceDiagramModel, h::UInt)
    return hash(m.strategy,
                hash(m.utilities, hash(m.model, h)))
end

function Base.show(io::IO, m::InfluenceDiagramModel)
    id = syntax(m)
    print(io, "InfluenceDiagramModel(", nparts(id, :Variable), " variables, ",
          nparts(id, :Decision), " decision", nparts(id, :Decision) == 1 ? "" : "s", ", ",
          nparts(id, :Utility), " utilit", nparts(id, :Utility) == 1 ? "y" : "ies")
    nk = length(kernels(m))
    nk == 0 || print(io, ", ", nk, " kernel", nk == 1 ? "" : "s")
    nu = length(m.utilities)
    nu == 0 || print(io, ", ", nu, " bound")
    np = length(m.strategy)
    np == 0 || print(io, ", ", np, " polic", np == 1 ? "y" : "ies")
    isempty(evidence(m)) ||
        print(io, ", evidence on ", join(sort!(collect(keys(evidence(m)))), ", "))
    return print(io, ")")
end

# Accessors
###########

"""
    bayes_model(m::InfluenceDiagramModel) -> BayesModel

The inner `BayesModel` over the influence-diagram syntax (spaces, chance kernels,
evidence, history, extras). Its network is open: action variables have no mechanism
until [`instantiate`](@ref) adds policy mechanisms.
"""
bayes_model(m::InfluenceDiagramModel) = m.model

syntax(m::InfluenceDiagramModel) = syntax(m.model)
spaces(m::InfluenceDiagramModel) = spaces(m.model)
kernels(m::InfluenceDiagramModel) = kernels(m.model)
evidence(m::InfluenceDiagramModel) = evidence(m.model)
history(m::InfluenceDiagramModel) = history(m.model)
extras(m::InfluenceDiagramModel) = extras(m.model)

"""
    strategy(m::InfluenceDiagramModel) -> Strategy

The current strategy of the model (possibly incomplete). See [`set_policy`](@ref),
[`fix_decision`](@ref).
"""
strategy(m::InfluenceDiagramModel) = m.strategy

"""
    bound_utilities(m::InfluenceDiagramModel) -> Dict{Symbol,AbstractUtility}

The utilities bound to utility nodes, keyed by utility-node name. See
[`bind_utility`](@ref).
"""
bound_utilities(m::InfluenceDiagramModel) = m.utilities

space(m::InfluenceDiagramModel, x::Symbol) = space(m.model, x)
parent_space(m::InfluenceDiagramModel, x::Symbol) = parent_space(m.model, x)
kernel(m::InfluenceDiagramModel, x::Symbol) = kernel(m.model, x)
missing_kernels(m::InfluenceDiagramModel) = missing_kernels(m.model)
has_semantics(m::InfluenceDiagramModel) = has_semantics(m.model)
intervened_variables(m::InfluenceDiagramModel) = intervened_variables(m.model)
is_intervened(m::InfluenceDiagramModel, x::Symbol) = is_intervened(m.model, x)

"""
    action_space(m::InfluenceDiagramModel, decision) -> FiniteSpace

The space of the action variable of `decision` (name or part id).
"""
function action_space(m::InfluenceDiagramModel, d)
    return space(m, variable_name(syntax(m), decision_variable(syntax(m), d)))
end

_action_axis(m::InfluenceDiagramModel, d) = only(factors(action_space(m, d)))

"""
    information_space(m::InfluenceDiagramModel, decision) -> FiniteSpace

The tensor of the spaces of the information variables of `decision` in
`information_position` order: the domain of its policy kernel.
"""
function information_space(m::InfluenceDiagramModel, d)
    return FiniteSpace(_information_axes(m, d))
end

function _information_axes(m::InfluenceDiagramModel, d)
    id = syntax(m)
    return FiniteAxis[only(factors(space(m, variable_name(id, v))))
                      for v in decision_information(id, d)]
end

# Chance kernels
################

function bind_kernel(m::InfluenceDiagramModel, b; kw...)
    return _with(m; model=bind_kernel(m.model, b; kw...))
end
bind_cpt(m::InfluenceDiagramModel, b; kw...) = _with(m; model=bind_cpt(m.model, b; kw...))

# Utilities
###########

"""
    bind_utility(m::InfluenceDiagramModel, :U => table) -> InfluenceDiagramModel
    bind_utility(m, :U => f::Function)
    bind_utility(m, :U => u::AbstractUtility)
    bind_utility(m, [:U => t1, :V => t2])

Bind a utility to the utility node `U`: a table (`size == (n(X1), ..., n(Xk))` over the
node's scope in `utility_position` order, a number for an empty scope) becomes a
[`TabularUtility`](@ref); a function of the scope's state labels a
[`FunctionUtility`](@ref); a ready-made utility must have the node's scope
([`UtilityScopeError`](@ref) otherwise). A node with `NoRef` receives the reference
`NamedRef(string(name))`, so the returned model carries an updated syntax.
"""
function bind_utility(m::InfluenceDiagramModel, b::Pair{Symbol,<:AbstractUtility})
    name, u = b
    id = syntax(m)
    uid = utility_id(id, name)
    expected = utility_scope_names(id, uid)
    scope(u) == expected || throw(UtilityScopeError(name, :scope, expected, scope(u)))
    if u isa TabularUtility
        axes = _utility_axes(m, uid)
        u.scope == axes || throw(UtilityScopeError(name, :scope, axes, u.scope))
    end
    model = m.model
    if utility_ref(id, uid) isa NoRef
        syn = deepcopy(id)
        set_subpart!(syn, uid, :utility_ref, NamedRef(string(name)))
        model = BayesModel(model; syntax=syn)
    end
    us = copy(m.utilities)
    us[name] = u
    return _with(m; model=model, utilities=us)
end

function bind_utility(m::InfluenceDiagramModel, b::Pair{Symbol,<:Union{AbstractArray,Real}})
    name, table = b
    uid = utility_id(syntax(m), name)
    axes = _utility_axes(m, uid)
    expected = Tuple(length(a) for a in axes)
    size(table) == expected || throw(UtilityScopeError(name, :table, expected, size(table)))
    return bind_utility(m, name => TabularUtility(axes, table))
end

function bind_utility(m::InfluenceDiagramModel, b::Pair{Symbol,<:Function})
    name, f = b
    return bind_utility(m, name => FunctionUtility(utility_scope_names(syntax(m), name), f))
end

function bind_utility(m::InfluenceDiagramModel, bs::AbstractVector{<:Pair{Symbol}})
    return foldl(bind_utility, bs; init=m)
end

# A heterogeneous vector such as `[:U => table, :K => 5.0]` has element type
# `Pair{Symbol,Any}`, which matches none of the methods above; re-pair the value so that
# its concrete type dispatches.
function bind_utility(m::InfluenceDiagramModel, b::Pair{Symbol})
    name, value = b
    value isa Union{AbstractUtility,AbstractArray,Real,Function} ||
        throw(UtilityScopeError(name, :value,
                                Union{AbstractUtility,AbstractArray,Real,Function},
                                typeof(value)))
    return bind_utility(m, name => value)
end

function _utility_axes(m::InfluenceDiagramModel, u)
    id = syntax(m)
    return FiniteAxis[only(factors(space(m, variable_name(id, v))))
                      for v in utility_scope(id, u)]
end

"""
    utility(m::InfluenceDiagramModel, :U) -> AbstractUtility

The utility bound to node `U`. Throws [`MissingUtilityError`](@ref) if none is bound.
"""
function utility(m::InfluenceDiagramModel, name::Symbol)
    uid = utility_id(syntax(m), name)
    haskey(m.utilities, name) ||
        throw(MissingUtilityError(name, utility_ref(syntax(m), uid)))
    return m.utilities[name]
end

"""
    missing_utilities(m::InfluenceDiagramModel) -> Vector{Symbol}

Names of the utility nodes without a bound utility, in part-id order.
"""
function missing_utilities(m::InfluenceDiagramModel)
    return Symbol[u for u in utility_names(syntax(m)) if !haskey(m.utilities, u)]
end

# Policies on a model
#####################

"""
    deterministic_policy(m::InfluenceDiagramModel, decision, spec) -> DeterministicPolicy

A [`DeterministicPolicy`](@ref) for `decision` with the information and action axes
read from the model; `spec` is a table, a dictionary or a function as accepted by the
`DeterministicPolicy` constructor (or a single action label for a decision without
information).
"""
function deterministic_policy(m::InfluenceDiagramModel, d, spec)
    id = syntax(m)
    did = decision_id(id, d isa Symbol ? d : decision_name(id, d))
    return DeterministicPolicy(decision_name(id, did), _information_axes(m, did),
                               _action_axis(m, did), spec)
end

"""
    validate_policy(m::InfluenceDiagramModel, decision, p::AbstractPolicy) -> Nothing

Check that `p` fits `decision` of the model (SPEC §37 item 9); see the axis-level
method for the rules. Throws [`PolicySignatureError`](@ref).
"""
function validate_policy(m::InfluenceDiagramModel, d, p::AbstractPolicy)
    id = syntax(m)
    did = _decision_id(id, d)
    return validate_policy(decision_name(id, did), _information_axes(m, did),
                           _action_axis(m, did), p)
end

"""
    policy_kernel(p::AbstractPolicy, m::InfluenceDiagramModel, decision) -> FiniteKernel

The kernel of `p` for `decision`, with the information and action spaces read from the
model (needed for a [`ConstantPolicy`](@ref)); the policy is validated first.
"""
function policy_kernel(p::AbstractPolicy, m::InfluenceDiagramModel, d)
    validate_policy(m, d, p)
    return policy_kernel(p, information_space(m, d), action_space(m, d))
end

function n_deterministic_policies(m::InfluenceDiagramModel, d)
    return n_deterministic_policies(_information_axes(m, d), _action_axis(m, d))
end

function all_deterministic_policies(m::InfluenceDiagramModel, d)
    id = syntax(m)
    did = _decision_id(id, d)
    return all_deterministic_policies(decision_name(id, did), _information_axes(m, did),
                                      _action_axis(m, did))
end

"""
    set_policy(m::InfluenceDiagramModel, decision, p::AbstractPolicy) -> InfluenceDiagramModel
    set_policy(m, strategy::Strategy)

Replace the policy of `decision` (SPEC §41 "policy replacement"), or every policy of
the given strategy, after checking each against the model
([`PolicySignatureError`](@ref)). The syntax is untouched.
"""
function set_policy(m::InfluenceDiagramModel, d, p::AbstractPolicy)
    id = syntax(m)
    name = decision_name(id, _decision_id(id, d))
    validate_policy(m, name, p)
    ps = copy(policies(m.strategy))
    ps[name] = p
    return _with(m; strategy=Strategy(ps))
end

function set_policy(m::InfluenceDiagramModel, σ::Strategy)
    return foldl((acc, kv) -> set_policy(acc, kv[1], kv[2]), collect(policies(σ)); init=m)
end

"""
    unset_policy(m::InfluenceDiagramModel, decision) -> InfluenceDiagramModel
    unset_policy(m) -> InfluenceDiagramModel

Remove the policy of `decision`, or all policies.
"""
function unset_policy(m::InfluenceDiagramModel, d)
    id = syntax(m)
    name = decision_name(id, _decision_id(id, d))
    ps = copy(policies(m.strategy))
    delete!(ps, name)
    return _with(m; strategy=Strategy(ps))
end
unset_policy(m::InfluenceDiagramModel) = _with(m; strategy=Strategy())

"""
    fix_decision(m::InfluenceDiagramModel, :D => :a) -> InfluenceDiagramModel
    fix_decision(m, [:D => :a, :E => :b])

Give decision `D` the [`ConstantPolicy`](@ref) that always chooses `a` (SPEC §41
"fixed decision"; `Strategy.fix` in the Lean model). This is a decision operation: the
decision, its information set and the syntax stay as they are, only the strategy
changes. Compare [`do_intervention`](@ref) on an action variable, which removes the
decision. Throws `UnknownStateError` if `a` is not a state of the action variable.
"""
function fix_decision(m::InfluenceDiagramModel, f::Pair{Symbol,Symbol})
    d, a = f
    id = syntax(m)
    did = decision_id(id, d)
    x = variable_name(id, decision_variable(id, did))
    a in states(id, x) || throw(UnknownStateError(x, a))
    return set_policy(m, decision_name(id, did), ConstantPolicy(a))
end

function fix_decision(m::InfluenceDiagramModel, fs::AbstractVector{<:Pair{Symbol,Symbol}})
    return foldl(fix_decision, fs; init=m)
end

# Information structure
#######################

"""
    with_information(m::InfluenceDiagramModel, decision, variable; no_forgetting = true) -> InfluenceDiagramModel

A model whose syntax has `variable` appended to the information set of `decision`
(SPEC §34, §35: adding information enlarges the admissible policy class). The result is
validated ([`InvalidInformationSetError`](@ref) if the variable is not available
before the decision); the policies whose signature no longer matches are removed from
the strategy.

With `no_forgetting = true` (the default) the arc is propagated: a variable that becomes
known at `decision` is still known at every later decision, so it is appended to the
information set of every decision after `decision` in [`decision_order`](@ref) that does
not already have it. This is what SPEC §35's `info(X, D)` means under perfect recall,
and it is what keeps the enlarged diagram solvable by
[`DecisionVariableElimination`](@ref); without it
[`expected_value_of_information`](@ref) would produce a diagram that forgets and the
default backend would throw [`IrregularDiagramError`](@ref).

Pass `no_forgetting = false` to add the single arc only, which is what a genuinely
limited-memory diagram [LauritzenNilsson2001](@cite) wants; such a diagram must then be
solved with [`ExhaustivePolicySearch`](@ref).

# Example

```jldoctest
julia> m = with_information(two_stage_model(), :Test, :Oil);

julia> information_names(syntax(m), :Test)
1-element Vector{Symbol}:
 :Oil

julia> information_names(syntax(m), :Drill)   # propagated to the later decision
3-element Vector{Symbol}:
 :Test
 :Result
 :Oil
```
"""
function with_information(m::InfluenceDiagramModel, d, x; no_forgetting::Bool=true)
    id = syntax(m)
    did = _decision_id(id, d)
    v = _variable_id(id, x)
    syn = deepcopy(id)
    add_information!(syn, did, v)
    touched = [did]
    if no_forgetting
        ds = decision_order(id)
        k = findfirst(==(did), ds)
        for later in ds[(k + 1):end]
            v in decision_information(syn, later) && continue
            add_information!(syn, later, v)
            push!(touched, later)
        end
    end
    validate(syn)
    out = _with(m; model=BayesModel(m.model; syntax=syn))
    return foldl(unset_policy, touched; init=out)
end

"""
    with_no_forgetting(m::InfluenceDiagramModel) -> InfluenceDiagramModel
    with_no_forgetting(id::AbstractInfluenceDiagram) -> InfluenceDiagram

The diagram with every arc of [`no_forgetting_arcs`](@ref) added, so that everything
known at a decision is still known at every later decision (perfect recall). The
diagram is unchanged when it already has no-forgetting; on a model, the policies of the
decisions whose information set grew are removed from the strategy.

[`DecisionVariableElimination`](@ref) needs no-forgetting and says so with an
[`IrregularDiagramError`](@ref) naming the variables the decision maker would have to
remember; this is the repair. It is not applied automatically, because a diagram that
forgets is a legitimate limited-memory influence diagram [LauritzenNilsson2001](@cite)
that [`ExhaustivePolicySearch`](@ref) solves exactly, and adding arcs changes the model.

```jldoctest
julia> m = without_information(two_stage_model(), :Drill, :Test);

julia> no_forgetting_arcs(syntax(m))
1-element Vector{Pair{Symbol, Symbol}}:
 :Drill => :Test

julia> information_names(syntax(with_no_forgetting(m)), :Drill)
2-element Vector{Symbol}:
 :Result
 :Test
```
"""
function with_no_forgetting(m::InfluenceDiagramModel)
    missing_arcs = no_forgetting_arcs(syntax(m))
    isempty(missing_arcs) && return m
    syn = with_no_forgetting(syntax(m))
    out = _with(m; model=BayesModel(m.model; syntax=syn))
    return foldl(unset_policy, unique(first.(missing_arcs)); init=out)
end

function with_no_forgetting(id::AbstractInfluenceDiagram)
    syn = deepcopy(id)
    for (d, x) in no_forgetting_arcs(id)
        add_information!(syn, decision_id(syn, d), variable_id(syn, x))
    end
    validate(syn)
    return syn
end

no_forgetting_arcs(m::InfluenceDiagramModel) = no_forgetting_arcs(syntax(m))
is_no_forgetting(m::InfluenceDiagramModel) = is_no_forgetting(syntax(m))

"""
    without_information(m::InfluenceDiagramModel, decision, variable) -> InfluenceDiagramModel

A model whose syntax has `variable` removed from the information set of `decision`
(positions are renumbered); the decision's policy is removed from the strategy. Throws
[`InvalidInformationSetError`](@ref) (`:unknown`) if the variable is not in the
information set.
"""
function without_information(m::InfluenceDiagramModel, d, x)
    id = syntax(m)
    did = _decision_id(id, d)
    v = _variable_id(id, x)
    ids = information_ids(id, did)
    i = findfirst(j -> subpart(id, j, :information_variable) == v, ids)
    i === nothing &&
        throw(InvalidInformationSetError(decision_name(id, did), variable_name(id, v),
                                         :unknown))
    syn = deepcopy(id)
    rem_part!(syn, :InformationInput, ids[i])
    for (pos, j) in enumerate(information_ids(syn, did))
        set_subpart!(syn, j, :information_position, pos)
    end
    out = _with(m; model=BayesModel(m.model; syntax=syn))
    return unset_policy(out, did)
end

# Observation and interventions
###############################

# Evidence on an action variable is meaningless: the variable has no chance mechanism,
# so there is nothing to condition. SPEC §41 keeps observation and the decision
# operations apart, and both solvers rely on it (`_check_solvable`).
function _check_evidence_variables(id::AbstractInfluenceDiagram,
                                   ev::AbstractDict{Symbol,Symbol})
    for x in sort!(collect(keys(ev)))
        has_variable(id, x) || continue
        d = decision_of(id, variable_id(id, x))
        d === nothing ||
            throw(EvidenceOnActionError(x, decision_name(id, d), ev[x]))
    end
    return nothing
end

_evidence_dict(ev) = Dict{Symbol,Symbol}(ev)

"""
    observe(m::InfluenceDiagramModel, :X => :x) -> InfluenceDiagramModel
    observe(m, [:X => :x, :Y => :y])

Record evidence on chance variables, as `observe(::BayesModel)` does. Evidence on an
action variable is refused with an [`EvidenceOnActionError`](@ref): the value of a
decision is not observed but chosen, with [`fix_decision`](@ref) or
[`set_policy`](@ref) (SPEC §41).
"""
function observe(m::InfluenceDiagramModel, ev)
    _check_evidence_variables(syntax(m), _evidence_dict(ev))
    return _with(m; model=observe(m.model, ev))
end
unobserve(m::InfluenceDiagramModel, x::Symbol) = _with(m; model=unobserve(m.model, x))
unobserve(m::InfluenceDiagramModel) = _with(m; model=unobserve(m.model))

function _mechanism_record(id::AbstractBayesNet, mech::Integer)
    return MechanismRecord(mechanism_name(id, mech), kernel_ref(id, mech),
                           Symbol[variable_name(id, p) for p in inputs(id, mech)])
end

"""
    do_intervention(m::InfluenceDiagramModel, :X => :x; note = "") -> InfluenceDiagramModel
    do_intervention(m, [:X => :x, :Y => :y])

The hard intervention `do(X = x)` (SPEC §21.2, §41). On a chance variable it is the
local mechanism rewrite of BayesianNetworks.jl: the mechanism of `X` and its inputs are
removed and a mechanism `do[X=x]` with reference `PointMassRef(x)` is added. On an
action variable it is a physical override (revision note on SPEC §41): the decision is
removed together with its information inputs and precedence rows, its policy is
dropped from the strategy, and `X` receives the constant mechanism, so it is no longer
a decision. Both are recorded as a `:hard` event in the history; the note of the
decision case says which decision was removed. Compare [`fix_decision`](@ref), which
keeps the decision and gives it a constant policy.
"""
function do_intervention(m::InfluenceDiagramModel, iv::Pair{Symbol,Symbol};
                         note::AbstractString="")
    x, s = iv
    id = syntax(m)
    v = variable_id(id, x)
    s in states(id, v) || throw(UnknownStateError(x, s))
    syn = deepcopy(id)
    old = mechanism_of(syn, v)
    removed = old === nothing ? nothing : _mechanism_record(syn, old)
    old === nothing || cascading_rem_part!(syn, :Mechanism, old)
    d = decision_of(syn, v)
    σ = m.strategy
    if d !== nothing
        dname = decision_name(syn, d)
        note = isempty(note) ? "removed decision $(dname)" : note
        cascading_rem_part!(syn, :Decision, d)
        ps = copy(policies(σ))
        delete!(ps, dname)
        σ = Strategy(ps)
    end
    add_part!(syn, :Mechanism; target=v, mechanism_name=hard_intervention_name(x, s),
              kernel_ref=PointMassRef(s))
    added = MechanismRecord(hard_intervention_name(x, s), PointMassRef(s), Symbol[])
    ev = ModelEvent(:hard, x, removed, added; note=note)
    model = BayesModel(m.model; syntax=syn, history=vcat(history(m), [ev]))
    return _with(m; model=model, strategy=σ)
end

function do_intervention(m::InfluenceDiagramModel,
                         ivs::AbstractVector{<:Pair{Symbol,Symbol}};
                         kw...)
    return foldl((acc, iv) -> do_intervention(acc, iv; kw...), ivs; init=m)
end

"""
    soft_intervention(m::InfluenceDiagramModel, :X => k::FiniteKernel; parents, name, note) -> InfluenceDiagramModel
    soft_intervention(m, :X => ref::KernelRef; parents, name, kernel, note)

The soft intervention replacing the mechanism of chance variable `X` by one with the
given `parents` (by default the kernel's domain axis names, or the current parents)
and kernel (SPEC §21.3), as in BayesianNetworks.jl. On an action variable the decision
is removed first, as in [`do_intervention`](@ref). Recorded as a `:soft` event.
"""
function soft_intervention(m::InfluenceDiagramModel, iv::Pair{Symbol,<:FiniteKernel};
                           parents::Union{Nothing,AbstractVector{Symbol}}=nothing,
                           name::Symbol=Symbol("soft[", first(iv), "]"),
                           note::AbstractString="")
    x, k = iv
    ps = parents === nothing ? Symbol[a.name for a in factors(k.dom)] :
         collect(Symbol, parents)
    return soft_intervention(m, x => NamedRef(string(name)); parents=ps, name=name,
                             kernel=k, note=note)
end

function soft_intervention(m::InfluenceDiagramModel, iv::Pair{Symbol,<:KernelRef};
                           parents::Union{Nothing,AbstractVector{Symbol}}=nothing,
                           name::Symbol=Symbol("soft[", first(iv), "]"), kernel=nothing,
                           note::AbstractString="")
    x, ref = iv
    id = syntax(m)
    v = variable_id(id, x)
    ps = parents === nothing ?
         Symbol[variable_name(id, p) for p in BayesianNetworks.parents(id, v)] :
         collect(Symbol, parents)
    syn = deepcopy(id)
    old = mechanism_of(syn, v)
    removed = old === nothing ? nothing : _mechanism_record(syn, old)
    old === nothing || cascading_rem_part!(syn, :Mechanism, old)
    d = decision_of(syn, v)
    σ = m.strategy
    if d !== nothing
        dname = decision_name(syn, d)
        note = isempty(note) ? "removed decision $(dname)" : note
        cascading_rem_part!(syn, :Decision, d)
        ps2 = copy(policies(σ))
        delete!(ps2, dname)
        σ = Strategy(ps2)
    end
    add_mechanism!(syn, v; inputs=ps, name=name, kernel_ref=ref)
    validate(syn)
    ks = copy(kernels(m))
    kernel === nothing || (ks[ref] = kernel)
    ev = ModelEvent(:soft, x, removed, MechanismRecord(name, ref, ps); note=note)
    model = BayesModel(m.model; syntax=syn, kernels=ks, history=vcat(history(m), [ev]))
    validate(model)   # the new kernel must fit the new mechanism
    return _with(m; model=model, strategy=σ)
end

# Validation
############

"""
    validate(m::InfluenceDiagramModel; closed = false, unique_names = false, semantics = false, strategy = false, atol = 1e-8) -> Nothing

[`validate`](@ref) the syntax, the evidence and the chance semantics as
`validate(::BayesModel)` does, then the decision layer: no evidence sits on an action
variable ([`EvidenceOnActionError`](@ref)), every bound utility reads its node's scope
([`UtilityScopeError`](@ref)), every policy of the strategy names an existing decision
and fits it ([`PolicySignatureError`](@ref), SPEC §37 item 9). With `semantics = true`
every mechanism must resolve to a kernel and every utility node to a bound utility
([`MissingUtilityError`](@ref), item 7); with `strategy = true` the strategy must be
complete ([`IncompleteStrategyError`](@ref), item 10). The first violation is thrown.

`atol` is the tolerance of the kernel-normalisation check, forwarded to
`validate(::BayesModel)`; it must match the tolerance a model was read with (a network
read with `read_influence_diagram(path; atol = 1e-6)` keeps rows that are off by up to
`1e-6` and has to be validated with the same `atol`).
"""
function validate(m::InfluenceDiagramModel; closed::Bool=false, unique_names::Bool=false,
                  semantics::Bool=false, strategy::Bool=false,
                  atol::Real=BayesianNetworks.DEFAULT_ATOL)
    validate(m.model; closed=closed, unique_names=unique_names, semantics=semantics,
             atol=atol)
    id = syntax(m)
    _check_evidence_variables(id, evidence(m))
    for u in utilities(id)
        name = utility_name(id, u)
        if haskey(m.utilities, name)
            expected = utility_scope_names(id, u)
            got = scope(m.utilities[name])
            got == expected || throw(UtilityScopeError(name, :scope, expected, got))
        elseif semantics
            throw(MissingUtilityError(name, utility_ref(id, u)))
        end
    end
    for (d, p) in policies(m.strategy)
        validate_policy(m, d, p)
    end
    if strategy
        missing = missing_policies(m.strategy, id)
        isempty(missing) || throw(IncompleteStrategyError(missing))
    end
    return nothing
end

"""
    isapprox(a::InfluenceDiagramModel, b::InfluenceDiagramModel; kwargs...) -> Bool

Whether two models have the same semantics: `isapprox` inner `BayesModel`s (same
canonical syntax, same evidence, approximately equal kernels), the same strategy, and
utilities that agree on every state of their scope within the tolerances.
"""
function Base.isapprox(a::InfluenceDiagramModel, b::InfluenceDiagramModel; kwargs...)
    isapprox(a.model, b.model; kwargs...) || return false
    a.strategy == b.strategy || return false
    keys(a.utilities) == keys(b.utilities) || return false
    for (name, ua) in a.utilities
        ub = b.utilities[name]
        uid = utility_id(syntax(a), name)
        axes = _utility_axes(a, uid)
        isapprox(utility_table(ua, axes), utility_table(ub, axes); kwargs...) ||
            return false
    end
    return true
end
