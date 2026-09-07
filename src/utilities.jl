"""
Utility functions (SPEC §29, §30). A utility is a deterministic functional
`u_j : X_{j_1} ⊗ ... ⊗ X_{j_k} -> R` over the scope of its utility node, in
`utility_position` order. Utilities are never random variables; the syntax records the
scope and a reference, the model binds the numbers. Aggregation is additive
(`totalUtility` in the Lean model).
"""

"""
    AbstractUtility

Abstract supertype of utilities: [`TabularUtility`](@ref) and
[`FunctionUtility`](@ref). Every utility answers [`utility_value`](@ref) for an
assignment and [`scope`](@ref) with its argument names.
"""
abstract type AbstractUtility end

"""
    TabularUtility(scope::Vector{FiniteAxis}, table::AbstractArray{<:Real})

A utility given as a table over its scope: `size(table) == (length.(scope)...)`, with a
0-dimensional array (or a number) for an empty scope. Throws
[`UtilityScopeError`](@ref) (`what == :table`) for a table of the wrong size.
"""
struct TabularUtility <: AbstractUtility
    scope::Vector{FiniteAxis}
    table::Array{Float64}
    function TabularUtility(scope::AbstractVector{FiniteAxis}, table::AbstractArray{<:Real})
        expected = Tuple(length(a) for a in scope)
        size(table) == expected ||
            throw(UtilityScopeError(isempty(scope) ? :utility : first(scope).name, :table,
                                    expected, size(table)))
        allunique([a.name for a in scope]) ||
            throw(UtilityScopeError(first(scope).name, :duplicate,
                                    unique([a.name for a in scope]),
                                    [a.name for a in scope]))
        return new(collect(FiniteAxis, scope), convert(Array{Float64}, collect(table)))
    end
end

TabularUtility(scope::AbstractVector{FiniteAxis}, x::Real) = TabularUtility(scope, fill(x))

Base.:(==)(a::TabularUtility, b::TabularUtility) = a.scope == b.scope && a.table == b.table
Base.hash(u::TabularUtility, h::UInt) = hash(u.table, hash(u.scope, h))
function Base.isapprox(a::TabularUtility, b::TabularUtility; kw...)
    return a.scope == b.scope && isapprox(a.table, b.table; kw...)
end

"""
    FunctionUtility(scope::Vector{Symbol}, f)

A utility given as a function of the states of its scope: `f` is called with one state
label per scope variable, in order, and must return a real number.
"""
struct FunctionUtility <: AbstractUtility
    scope::Vector{Symbol}
    f::Any
    FunctionUtility(scope::AbstractVector{Symbol}, f) = new(collect(Symbol, scope), f)
end

"""
    scope(u::AbstractUtility) -> Vector{Symbol}

The variable names a utility reads, in argument order.
"""
scope(u::TabularUtility) = Symbol[a.name for a in u.scope]
scope(u::FunctionUtility) = u.scope

"""
    utility_value(u::AbstractUtility, assignment::AbstractDict{Symbol,Symbol}) -> Float64
    utility_value(u::AbstractUtility, labels::Symbol...) -> Float64

The value of a utility at an assignment of variable names to states (only the scope
variables are read), or at the given labels in scope order. Throws
[`UtilityScopeError`](@ref) (`what == :value`) when a function utility does not return
a real number.
"""
function utility_value(u::TabularUtility, labels::Symbol...)
    length(labels) == length(u.scope) ||
        throw(UtilityScopeError(isempty(u.scope) ? :utility : first(u.scope).name, :scope,
                                length(u.scope), length(labels)))
    idx = ntuple(i -> label_index(u.scope[i], labels[i]), length(labels))
    return u.table[idx...]
end

function utility_value(u::FunctionUtility, labels::Symbol...)
    length(labels) == length(u.scope) ||
        throw(UtilityScopeError(isempty(u.scope) ? :utility : first(u.scope), :scope,
                                length(u.scope), length(labels)))
    v = u.f(labels...)
    v isa Real ||
        throw(UtilityScopeError(isempty(u.scope) ? :utility : first(u.scope), :value,
                                Real, typeof(v)))
    return Float64(v)
end

function utility_value(u::AbstractUtility, assignment::AbstractDict{Symbol,Symbol})
    sc = scope(u)
    return utility_value(u, ntuple(i -> assignment[sc[i]], length(sc))...)
end

"""
    utility_table(u::AbstractUtility, axes::Vector{FiniteAxis}) -> Array{Float64}
    utility_table(u::TabularUtility) -> Array{Float64}

The values of a utility tabulated over its scope with the given axes (which must carry
the scope names in order); a [`TabularUtility`](@ref) returns its own table.
"""
utility_table(u::TabularUtility) = u.table

function utility_table(u::TabularUtility, axes::AbstractVector{FiniteAxis})
    axes == u.scope ||
        throw(UtilityScopeError(isempty(u.scope) ? :utility : first(u.scope).name, :scope,
                                u.scope, axes))
    return u.table
end

function utility_table(u::FunctionUtility, axes::AbstractVector{FiniteAxis})
    [a.name for a in axes] == u.scope ||
        throw(UtilityScopeError(isempty(u.scope) ? :utility : first(u.scope), :scope,
                                u.scope, [a.name for a in axes]))
    dims = Tuple(length(a) for a in axes)
    table = Array{Float64}(undef, dims)
    for ci in CartesianIndices(dims)
        table[ci] = utility_value(u, ntuple(i -> axes[i].labels[ci[i]], length(axes))...)
    end
    return table
end

"""
    utility_factor(u::AbstractUtility, axes::Vector{FiniteAxis}) -> Factor
    utility_factor(u::TabularUtility) -> Factor

The utility as a `BayesianNetworkInference.Factor` over its scope, the `(1, u_j)`
initial valuation of decision variable elimination.
"""
utility_factor(u::TabularUtility) = Factor(u.scope, u.table)
function utility_factor(u::AbstractUtility, axes::AbstractVector{FiniteAxis})
    return Factor(collect(FiniteAxis, axes), utility_table(u, axes))
end
