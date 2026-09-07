"""
The valuation algebra of decision variable elimination (SPEC §33). A valuation is a
pair `(φ, ψ)` of factors: `φ` a probability potential and `ψ` a utility potential in
"already divided" form, together denoting the contribution `φ · ψ` to the expected
utility. This is the division algebra of [JensenJensenDittmer1994](@cite):

- combination: `(φ₁, ψ₁) ⊗ (φ₂, ψ₂) = (φ₁ φ₂, ψ₁ + ψ₂)`, the sum broadcasting over
  the union of the scopes;
- sum-elimination of a chance variable `X`: `φ' = Σ_X φ`,
  `ψ' = Σ_X (φ ψ) / φ'` with `0/0 := 0`;
- max-elimination of a decision `D`: `ψ' = max_D ψ`, with `φ` required to be constant
  in `D` (which the strong elimination order guarantees when every descendant of the
  action has been summed out first; an error otherwise), and the maximising action
  recorded as a policy table over the remaining scope.

A set of valuations `{(φ_i, ψ_i)}` denotes `(Π_i φ_i) (Σ_i ψ_i)`; eliminating a
variable combines only the valuations whose scope contains it, which keeps the
potentials small. The initial valuations are `(κ_X, 0)` for every chance mechanism and
`(1, u_j)` for every utility node; at the end `φ` is the probability of the evidence
(one without evidence) and `ψ` the maximal expected utility.

The correctness of the two eliminations is the identity
`Σ_X Π_T φ_i (Σ_T ψ_i + R) = Φ' (Ψ' + R)` for the touching set `T` and any `R`
independent of `X`, and its `max` counterpart when `Π_T φ_i` does not depend on `D`.
"""

"""
    Valuation(φ::Factor, ψ::Factor)
    Valuation(φ::Factor)

A valuation `(φ, ψ)` of the decision-elimination algebra; `Valuation(φ)` has a zero
utility potential. See the module documentation of `valuation.jl` for the algebra.
"""
struct Valuation{T<:Real}
    φ::Factor{T}
    ψ::Factor{T}
end

function Valuation(φ::Factor{S}, ψ::Factor{U}) where {S,U}
    T = promote_type(S, U)
    return Valuation{T}(_convert(T, φ), _convert(T, ψ))
end
Valuation(φ::Factor{T}) where {T} = Valuation{T}(φ, Factor(FiniteAxis[], fill(zero(T))))

_convert(::Type{T}, f::Factor{T}) where {T} = f
function _convert(::Type{T}, f::Factor) where {T}
    return Factor(f.vars, f.axes, convert(Array{T}, f.table))
end

"""
    scope(v::Valuation) -> Vector{Symbol}

The variables of `v`: the scope of `φ` followed by the variables of `ψ` not already
present.
"""
function scope(v::Valuation)
    vars = copy(v.φ.vars)
    for x in v.ψ.vars
        x in vars || push!(vars, x)
    end
    return vars
end

Base.:(==)(a::Valuation, b::Valuation) = a.φ == b.φ && a.ψ == b.ψ
function Base.isapprox(a::Valuation, b::Valuation; kw...)
    return isapprox(a.φ, b.φ; kw...) && isapprox(a.ψ, b.ψ; kw...)
end

function Base.show(io::IO, v::Valuation{T}) where {T}
    return print(io, "Valuation{", T, "} over ", Tuple(scope(v)), " (φ over ",
                 Tuple(v.φ.vars), ", ψ over ", Tuple(v.ψ.vars), ")")
end

# Factor helpers: broadcasting addition and division
###################################################

function _union_axes(f::Factor, g::Factor)
    vars = copy(f.vars)
    axes = copy(f.axes)
    for (x, a) in zip(g.vars, g.axes)
        i = findfirst(==(x), vars)
        if i === nothing
            push!(vars, x)
            push!(axes, a)
        elseif axes[i] != a
            throw(BayesianNetworkInference.ShapeError(:Valuation,
                                                      "factors disagree about the states of $(repr(x))",
                                                      axes[i].labels, a.labels))
        end
    end
    return vars, axes
end

# `f` extended to the scope `vars` (a superset, with `axes`) by constant broadcasting,
# in the order `vars`.
function _extend(f::Factor{T}, vars::Vector{Symbol}, axes::Vector{FiniteAxis}) where {T}
    missing = [i for i in eachindex(vars) if !(vars[i] in f.vars)]
    g = f
    if !isempty(missing)
        ones_ = Factor(vars[missing], axes[missing],
                       ones(T, Tuple(length(axes[i]) for i in missing)))
        g = multiply(f, ones_)
    end
    return reorder(g, vars)
end

# Pointwise sum with broadcasting over the union scope.
function _add(f::Factor, g::Factor)
    vars, axes = _union_axes(f, g)
    fe = _extend(f, vars, axes)
    ge = _extend(g, vars, axes)
    return Factor(vars, axes, _as_array(fe.table .+ ge.table))
end

# Broadcasting two 0-dimensional arrays yields a scalar; factors need an array.
_as_array(x::AbstractArray) = x
_as_array(x::Real) = fill(x)

# Pointwise quotient `num / den` with `0/0 := 0` (`den` broadcast over the scope of
# `num`, which must contain it).
function _divide(num::Factor, den::Factor)
    vars, axes = _union_axes(num, den)
    length(vars) == length(num.vars) ||
        throw(BayesianNetworkInference.ScopeError(:Valuation,
                                                  "the divisor's scope is not contained in the dividend's",
                                                  setdiff(den.vars, num.vars)))
    n = reorder(num, vars)
    d = _extend(den, vars, axes)
    table = map((a, b) -> b == 0 ? zero(a) : a / b, n.table, d.table)
    return Factor(vars, axes, _as_array(table))
end

# The algebra
#############

"""
    combine(v::Valuation, w::Valuation, ws::Valuation...) -> Valuation
    combine(vs::AbstractVector{<:Valuation}) -> Valuation

The combination `(φ₁ φ₂, ψ₁ + ψ₂)`.
"""
combine(v::Valuation, w::Valuation) = Valuation(multiply(v.φ, w.φ), _add(v.ψ, w.ψ))
combine(v::Valuation, w::Valuation, ws::Valuation...) = combine(combine(v, w), ws...)
function combine(vs::AbstractVector{<:Valuation})
    isempty(vs) && return Valuation(unit_factor())
    return reduce(combine, vs)
end

"""
    sum_out(v::Valuation, x::Symbol) -> Valuation

Sum-elimination of the chance variable `x`: `φ' = Σ_x φ`, `ψ' = Σ_x (φ ψ) / φ'` with
`0/0 := 0`. When `x` is in the scope of `ψ` but not of `φ`, `φ` is first broadcast over
`x`, so that `Σ_x φ = |X| φ` and `ψ' = (Σ_x ψ) / |X|`.
"""
function sum_out(v::Valuation, x::Symbol)
    x in scope(v) || return v
    φ = v.φ
    if !(x in φ.vars)
        # broadcast φ over x alone (not over the rest of ψ's scope)
        i = findfirst(==(x), v.ψ.vars)
        φ = _extend(φ, vcat(φ.vars, x), vcat(φ.axes, v.ψ.axes[i]))
    end
    φ′ = marginalize(φ, x)
    if x in v.ψ.vars
        ψ′ = _divide(marginalize(multiply(φ, v.ψ), x), φ′)
    else
        ψ′ = v.ψ
    end
    return Valuation(φ′, ψ′)
end

"""
    max_out(v::Valuation, d::Symbol; atol = 1e-9) -> (Valuation, policy::Array{Symbol}, policy_scope::Vector{Symbol})

Max-elimination of the decision variable `d`: `ψ' = max_d ψ`, `φ' = φ` with the axis
of `d` dropped after checking that `φ` is constant in `d` (up to `atol` relative to its
largest entry; [`IrregularDiagramError`](@ref) with `what == :probability` otherwise).
Also returns the maximising action for every configuration of the other variables of
`ψ` (`policy`, indexed in the order `policy_scope`; ties resolve to the first label).
When `ψ` does not depend on `d` every action is optimal and the first label of `d`
(read from `φ`) is chosen.
"""
function max_out(v::Valuation, d::Symbol; atol::Real=1e-9)
    φ = v.φ
    dlabels = Symbol[]
    if d in φ.vars
        i = findfirst(==(d), φ.vars)
        dlabels = φ.axes[i].labels
        mx = maximum(φ.table; dims=i)
        mn = minimum(φ.table; dims=i)
        tol = atol * max(1.0, maximum(abs, φ.table; init=0.0))
        if maximum(mx .- mn; init=0.0) > tol
            others = [x for x in φ.vars if x != d]
            throw(IrregularDiagramError(d, others, :probability))
        end
        keep = setdiff(1:ndims(φ), i)
        φ = Factor(φ.vars[keep], φ.axes[keep], dropdims(mx; dims=i))
    end
    ψ = v.ψ
    if d in ψ.vars
        i = findfirst(==(d), ψ.vars)
        dlabels = ψ.axes[i].labels
        policy = argmax_table(ψ, d)
        pscope = [x for x in ψ.vars if x != d]
        ψ = maximize(ψ, d)
    else
        isempty(dlabels) &&
            throw(BayesianNetworkInference.ScopeError(:max_out,
                                                      "the decision is not in the scope of the valuation",
                                                      [d]))
        policy = fill(first(dlabels))
        pscope = Symbol[]
    end
    return Valuation(φ, ψ), policy, pscope
end
