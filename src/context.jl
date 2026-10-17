"""
External decision contexts. An open influence diagram (CategoricalInfluenceDiagrams.jl's
open components) has *exogenous* variables, chance variables without a mechanism whose
law comes from outside, and outputs whose value is decided downstream. A
[`DecisionContext`](@ref) supplies both: a joint prior over the exogenous variables and a
terminal utility (the continuation) over any variables. [`expected_utility`](@ref) and
[`optimize`](@ref) with [`ExhaustivePolicySearch`](@ref) accept one through their `context`
keyword and compute

    EU(σ; μ, c) = Σ_x μ(x_exo) Π chance kernels(x) Π policies σ(x) (Σ_j u_j(x) + c(x_out)).

Without a context (or with an empty one) nothing changes: the model must be closed and the
computation is the one of SPEC §31 and §32, operation for operation.
"""

"""
    DecisionContext(; prior = nothing, terminal = nothing)

An external context for valuing and optimising a diagram with exogenous variables, as an
open component of a larger diagram is valued: a joint `prior` over the diagram's
*exogenous* variables (chance variables without a mechanism, which `validate(m; closed =
true)` would reject) and a `terminal` utility added to the total utility. Pass it as the
`context` keyword of [`expected_utility`](@ref) or of [`optimize`](@ref) with
[`ExhaustivePolicySearch`](@ref).

- `prior`: `vars::Vector{Symbol} => table::AbstractArray{<:Real}`, the joint distribution of
  the listed variables, axis `i` indexed by the states of `vars[i]` in state order (so a
  vector over the joint states with the first variable varying fastest is
  `vars => reshape(μ, nstates...)`). Entries must be finite and nonnegative, no variable may
  be listed twice, and `ndims(table) == length(vars)`. When used, `vars` must be exactly
  the exogenous variables of the model, and the entries must sum to one within the solver's
  `atol` (the kernel-normalisation convention: `|Σ - 1| <= atol`); the table is never
  renormalised. `nothing` (the default) means the model has no exogenous variables.
- `terminal`: `vars::Vector{Symbol} => table::AbstractArray{<:Real}` with finite, signed
  entries, added to the total utility of every joint state, axis `i` indexed by the states
  of `vars[i]`. Variables may be any of the diagram's (chance, exogenous or action) and may
  repeat: a repeated variable is read on the diagonal of its axes, as a copied output of an
  open diagram is. `nothing` (the default) means zero.

The tables are copied as `Array{Float64}`. Malformed arguments raise `ArgumentError` here;
the checks against a model run when the context is used: an unknown variable raises
`UnknownVariableError`, an axis whose length is not its variable's number of states
[`ContextStateCountError`](@ref), a prior that does not list exactly the exogenous variables
[`ExogenousCoverageError`](@ref), and a prior that does not sum to one `ArgumentError`. A
context cannot be combined with evidence on the model (`ArgumentError`), and only
[`ExhaustivePolicySearch`](@ref) takes one ([`DecisionVariableElimination`](@ref) raises
`ArgumentError`).

A context with neither a prior nor a terminal is the same as no context: every function
that takes one then behaves, and computes, exactly as without it.

# Example

```jldoctest
julia> id = influence_diagram(:Weather => [:sunny, :rainy],
                              :Forecast => [:sunny, :cloudy, :rainy],
                              :Umbrella => [:take, :leave];
                              mechanisms = [:Forecast => :Weather],
                              decisions = [:Umbrella => :Forecast],
                              utilities = [:U => (:Weather, :Umbrella)], closed = false);

julia> m = bind_utility(bind_cpt(InfluenceDiagramModel(id),
                                 :Forecast => [0.7 0.2 0.1; 0.15 0.25 0.6]),
                        :U => [20.0 100.0; 70.0 0.0]);

julia> ctx = DecisionContext(; prior = [:Weather] => [0.7, 0.3]);

julia> optimize(m, ExhaustivePolicySearch(); context = ctx).expected_utility ≈ 77
true
```
"""
struct DecisionContext
    prior::Union{Nothing,Pair{Vector{Symbol},Array{Float64}}}
    terminal::Union{Nothing,Pair{Vector{Symbol},Array{Float64}}}
    function DecisionContext(; prior=nothing, terminal=nothing)
        return new(_context_table(prior, :prior), _context_table(terminal, :terminal))
    end
end

function Base.show(io::IO, c::DecisionContext)
    print(io, "DecisionContext(")
    c.prior === nothing || print(io, "prior over ", first(c.prior))
    c.prior === nothing || c.terminal === nothing || print(io, ", ")
    c.terminal === nothing || print(io, "terminal over ", first(c.terminal))
    return print(io, ")")
end

# The checks that need no model: the form `vars => table`, one axis per variable, finite
# entries; for the prior also nonnegative entries and no repeated variable.
_context_table(::Nothing, ::Symbol) = nothing
function _context_table(t, part::Symbol)
    t isa Pair ||
        throw(ArgumentError("the context's $part must be `vars => table` or nothing, not a $(typeof(t))"))
    vars, table = t
    (vars isa AbstractVector && all(x -> x isa Symbol, vars)) ||
        throw(ArgumentError("the variables of the context's $part must be a vector of Symbols, not $(repr(vars))"))
    vars = collect(Symbol, vars)
    table isa AbstractArray{<:Real} ||
        throw(ArgumentError("the table of the context's $part over $vars must be a real array, not a $(typeof(table))"))
    ndims(table) == length(vars) ||
        throw(ArgumentError("the table of the context's $part over $vars has $(ndims(table)) axes, but $(length(vars)) variables are listed"))
    all(isfinite, table) ||
        throw(ArgumentError("the table of the context's $part over $vars has an entry that is not finite"))
    if part === :prior
        allunique(vars) ||
            throw(ArgumentError("the context's prior lists a variable twice: $vars"))
        all(>=(0), table) ||
            throw(ArgumentError("the context's prior over $vars has a negative entry"))
    end
    return vars => convert(Array{Float64}, collect(table))
end

# A context that changes nothing is no context: the callers then take their unchanged path.
_active_context(::Nothing) = nothing
function _active_context(c::DecisionContext)
    return c.prior === nothing && c.terminal === nothing ? nothing : c
end

# The exogenous variables of a diagram: neither the target of a mechanism nor an action
# variable, in part order.
function _exogenous_names(id::AbstractInfluenceDiagram)
    return Symbol[variable_name(id, v)
                  for v in parts(id, :Variable)
                  if isempty(incident(id, v, :target)) &&
                     isempty(incident(id, v, :decision_variable))]
end

# Evidence and a context together are out of scope.
function _refuse_context_evidence(m::InfluenceDiagramModel)
    ev = evidence(m)
    isempty(ev) ||
        throw(ArgumentError("a decision context cannot be combined with evidence (the model observes $(sort!(collect(keys(ev))))); conditioning an open diagram is not supported"))
    return nothing
end

# The checks of a context against a model, with the solver's normalisation `atol`.
function _check_context(m::InfluenceDiagramModel, c::DecisionContext; atol::Real)
    _refuse_context_evidence(m)
    id = syntax(m)
    for (part, t) in ((:prior, c.prior), (:terminal, c.terminal))
        t === nothing && continue
        vars, table = t
        for (i, x) in enumerate(vars)
            has_variable(id, x) || throw(UnknownVariableError(x))
            n = nstates(id, x)
            size(table, i) == n || throw(ContextStateCountError(part, x, n, size(table, i)))
        end
    end
    exo = _exogenous_names(id)
    listed = c.prior === nothing ? Symbol[] : first(c.prior)
    uncovered = setdiff(exo, listed)
    extra = setdiff(listed, exo)
    isempty(uncovered) && isempty(extra) || throw(ExogenousCoverageError(uncovered, extra))
    if c.prior !== nothing
        total = sum(last(c.prior))
        abs(total - 1) <= atol ||
            throw(ArgumentError("the context's prior over $listed sums to $total, not to one within atol = $atol"))
    end
    return nothing
end

# The name of the utility node that carries the terminal utility in the reference
# evaluation.
const _TERMINAL_UTILITY = Symbol("context[terminal]")

# The model with the terminal utility added as an ordinary utility node over its distinct
# variables, the table read on the diagonal of repeated axes.
function _with_terminal(m::InfluenceDiagramModel, terminal)
    terminal === nothing && return m
    vars, table = terminal
    id = syntax(m)
    _TERMINAL_UTILITY in utility_names(id) &&
        throw(ArgumentError("the model already has a utility node named $(repr(_TERMINAL_UTILITY)), which a decision context reserves"))
    distinct = unique(vars)
    at = Int[findfirst(==(x), distinct) for x in vars]
    reduced = Array{Float64}(undef,
                             Tuple(size(table, findfirst(==(x), vars)) for x in distinct))
    for ci in CartesianIndices(reduced)
        reduced[ci] = table[ntuple(i -> ci[at[i]], length(vars))...]
    end
    syn = deepcopy(id)
    add_utility!(syn, _TERMINAL_UTILITY; scope=distinct)
    return bind_utility(_with(m; model=BayesModel(m.model; syntax=syn)),
                        _TERMINAL_UTILITY => reduced)
end

# The reference decomposition of a contextual expected utility: one closed model per joint
# prior state `x` of positive mass, the exogenous variables fixed at `x` by hard
# intervention and the terminal added as a utility node, with its weight `μ(x)`. Checks the
# context first.
function _context_cases(m::InfluenceDiagramModel, c::DecisionContext; atol::Real)
    _check_context(m, c; atol=atol)
    mt = _with_terminal(m, c.terminal)
    c.prior === nothing && return Tuple{Float64,InfluenceDiagramModel}[(1.0, mt)]
    vars, table = c.prior
    labels = [only(factors(space(m, x))).labels for x in vars]
    cases = Tuple{Float64,InfluenceDiagramModel}[]
    for ci in CartesianIndices(table)
        w = table[ci]
        w == 0 && continue
        fixed = Pair{Symbol,Symbol}[vars[i] => labels[i][ci[i]] for i in eachindex(vars)]
        push!(cases, (w, do_intervention(mt, fixed)))
    end
    return cases
end

# `Σ_x μ(x) EU(σ | x)` over the cases of `_context_cases`, each by the reference algorithm
# (or the stable one, with a compensated outer sum).
function _contextual_expected_utility(cases, σ::Strategy; max_states::Integer, atol::Real,
                                      stable::Bool)
    terms = Float64[w * expected_utility(mx, σ; max_states=max_states, atol=atol,
                                         stable=stable)
                    for (w, mx) in cases]
    length(terms) == 1 && return only(terms)
    stable || return sum(terms)
    scale = maximum(abs, terms; init=0.0)
    result = iszero(scale) ? 0.0 : scale * _compensated_sum(t / scale for t in terms)
    isfinite(result) ||
        throw(UtilityScopeError(:total, :value, "finite representable expected utility",
                                result))
    return result
end
