"""
Policies and strategies (SPEC §26, §27). A policy for decision `D` with information set
`I_D` (in `information_position` order) and action space `A_D` is a stochastic kernel
`⊗ I_D → A_D`; a deterministic policy is a function `I_D → A_D`, a constant policy
ignores its information. `policy_kernel` turns any of them into the `FiniteKernel` that
[`instantiate`](@ref) binds to the decision's policy mechanism.

Correspondence with the Lean model (`proofs/`): `DeterministicPolicy` is `Policy.ofFun`,
`ConstantPolicy` is `Policy.const`, `StochasticPolicy` a general `Policy`, and
`Strategy` collects one policy per decision.
"""

"""
    AbstractPolicy

Abstract supertype of policies: [`DeterministicPolicy`](@ref),
[`StochasticPolicy`](@ref) and [`ConstantPolicy`](@ref). Every policy can be turned
into a kernel with [`policy_kernel`](@ref).
"""
abstract type AbstractPolicy end

# Deterministic policies
########################

"""
    DeterministicPolicy(decision, information::Vector{FiniteAxis}, action::FiniteAxis, table)

A deterministic policy `δ_D : I_D -> A_D` for `decision`: `information` are the axes of
the information set in `information_position` order, `action` the axis of the action
variable, and `table` gives the chosen action for every information state. `table` may
be

- an `Array{Symbol}` of size `(length.(information)...)` (a 0-dimensional array, or a
  single `Symbol`, for an empty information set) holding action labels;
- a dictionary from tuples of information labels to action labels, which must cover
  every information state;
- a function called with one label per information axis (`f(i1, i2, ...)`) returning an
  action label.

Throws [`PolicySignatureError`](@ref) (`what == :table`) for a table of the wrong size
or a label that is not a state of the action. Use [`deterministic_policy`](@ref) to
read the axes from a model. Ties and defaults are the caller's business; the
[`DecisionVariableElimination`](@ref) backend resolves ties to the first action label.
"""
struct DeterministicPolicy <: AbstractPolicy
    decision::Symbol
    information::Vector{FiniteAxis}
    action::FiniteAxis
    table::Array{Symbol}
    function DeterministicPolicy(decision::Symbol, information::AbstractVector{FiniteAxis},
                                 action::FiniteAxis, table::AbstractArray{Symbol})
        expected = Tuple(length(a) for a in information)
        size(table) == expected ||
            throw(PolicySignatureError(decision, :table, expected, size(table)))
        for label in table
            label in action.labels ||
                throw(PolicySignatureError(decision, :table, action.labels, label))
        end
        return new(decision, collect(FiniteAxis, information), action,
                   convert(Array{Symbol}, collect(table)))
    end
end

function DeterministicPolicy(decision::Symbol, information::AbstractVector{FiniteAxis},
                             action::FiniteAxis, label::Symbol)
    return DeterministicPolicy(decision, information, action, fill(label))
end

function DeterministicPolicy(decision::Symbol, information::AbstractVector{FiniteAxis},
                             action::FiniteAxis, d::AbstractDict)
    dims = Tuple(length(a) for a in information)
    table = Array{Symbol}(undef, dims)
    for ci in CartesianIndices(dims)
        key = ntuple(i -> information[i].labels[ci[i]], length(information))
        haskey(d, key) ||
            throw(PolicySignatureError(decision, :table,
                                       "an action for every information state",
                                       "missing entry for $key"))
        table[ci] = d[key]
    end
    return DeterministicPolicy(decision, information, action, table)
end

function DeterministicPolicy(decision::Symbol, information::AbstractVector{FiniteAxis},
                             action::FiniteAxis, f)
    dims = Tuple(length(a) for a in information)
    table = Array{Symbol}(undef, dims)
    for ci in CartesianIndices(dims)
        table[ci] = f(ntuple(i -> information[i].labels[ci[i]], length(information))...)
    end
    return DeterministicPolicy(decision, information, action, table)
end

function Base.:(==)(a::DeterministicPolicy, b::DeterministicPolicy)
    return a.decision == b.decision && a.information == b.information &&
           a.action == b.action && a.table == b.table
end
function Base.hash(p::DeterministicPolicy, h::UInt)
    return hash(p.table, hash(p.action, hash(p.information, hash(p.decision, h))))
end

"""
    policy_table(p::DeterministicPolicy) -> Array{Symbol}

The action chosen for every information state, indexed in `information_position`
order.
"""
policy_table(p::DeterministicPolicy) = p.table

"""
    (p::DeterministicPolicy)(labels...) -> Symbol
    (p::DeterministicPolicy)(assignment::AbstractDict{Symbol,Symbol}) -> Symbol

The action chosen for the given information labels (one per information axis, in
order), or for the information state read from an assignment of variable names to
states.
"""
function (p::DeterministicPolicy)(labels::Symbol...)
    length(labels) == length(p.information) ||
        throw(PolicySignatureError(p.decision, :information, length(p.information),
                                   length(labels)))
    idx = ntuple(i -> label_index(p.information[i], labels[i]), length(labels))
    return p.table[idx...]
end
function (p::DeterministicPolicy)(assignment::AbstractDict{Symbol,Symbol})
    return p(ntuple(i -> assignment[p.information[i].name], length(p.information))...)
end

# Stochastic policies
#####################

"""
    StochasticPolicy(decision, kernel::FiniteKernel)
    StochasticPolicy(kernel::FiniteKernel)

A randomised policy `δ_D(a | i)`: a normalised kernel whose domain is the tensor of the
information axes in `information_position` order and whose codomain is the action
axis. Without an explicit `decision` the codomain axis name is used.
"""
struct StochasticPolicy <: AbstractPolicy
    decision::Symbol
    kernel::FiniteKernel
    function StochasticPolicy(decision::Symbol, kernel::FiniteKernel)
        ndims(kernel.codom) == 1 ||
            throw(PolicySignatureError(decision, :action, "one action axis",
                                       names(kernel.codom)))
        return new(decision, kernel)
    end
end

StochasticPolicy(kernel::FiniteKernel) = StochasticPolicy(only(names(kernel.codom)), kernel)

function Base.:(==)(a::StochasticPolicy, b::StochasticPolicy)
    return a.decision == b.decision &&
           a.kernel == b.kernel
end
Base.hash(p::StochasticPolicy, h::UInt) = hash(p.kernel, hash(p.decision, h))

# Constant policies
###################

"""
    ConstantPolicy(action::Symbol)

The policy that always chooses `action`, whatever the information (SPEC §41 "fixed
decision"; `Policy.const` in the Lean model). It is valid for every information set, so
it carries no axes; [`policy_kernel`](@ref) needs the spaces of the model.
"""
struct ConstantPolicy <: AbstractPolicy
    action::Symbol
end

# Kernels from policies
#######################

"""
    policy_kernel(p::DeterministicPolicy) -> FiniteKernel
    policy_kernel(p::StochasticPolicy) -> FiniteKernel
    policy_kernel(p::AbstractPolicy, information::FiniteSpace, action::FiniteSpace) -> FiniteKernel
    policy_kernel(p::AbstractPolicy, m::InfluenceDiagramModel, decision) -> FiniteKernel

The stochastic kernel `⊗ I_D -> A_D` implementing a policy: the one-hot kernel of a
deterministic policy, the kernel of a stochastic one, and the discard-then-point-mass
kernel of a constant one (which needs the information and action spaces, read from the
model or given explicitly). The three-argument forms check the spaces against the policy
and throw [`PolicySignatureError`](@ref) on a mismatch.
"""
function policy_kernel(p::DeterministicPolicy)
    X = FiniteSpace(p.information)
    Y = FiniteSpace(p.action)
    return deterministic(X, Y, (labels...) -> p(labels...))
end

policy_kernel(p::StochasticPolicy) = p.kernel

function policy_kernel(p::ConstantPolicy, information::FiniteSpace, action::FiniteSpace)
    a = only(factors(action))
    p.action in a.labels ||
        throw(PolicySignatureError(a.name, :table, a.labels, p.action))
    pm = point_mass(action, p.action)
    return isempty(information) ? pm :
           compose_kernel(discard_kernel(information), pm)
end

function policy_kernel(p::Union{DeterministicPolicy,StochasticPolicy},
                       information::FiniteSpace, action::FiniteSpace)
    k = policy_kernel(p)
    k.dom == information ||
        throw(PolicySignatureError(p.decision, :information, information, k.dom))
    k.codom == action || throw(PolicySignatureError(p.decision, :action, action, k.codom))
    return k
end

# Signature checks
##################

"""
    validate_policy(decision::Symbol, information::Vector{FiniteAxis}, action::FiniteAxis, p) -> Nothing
    validate_policy(m::InfluenceDiagramModel, decision, p) -> Nothing

Check that policy `p` fits a decision whose information set has the given axes (in
`information_position` order) and whose action variable has axis `action` (SPEC §37
item 9): a deterministic or stochastic policy must name the decision, read exactly
these information axes in this order and produce this action axis; a stochastic policy
must be normalised; a constant policy must name a state of the action. Throws
[`PolicySignatureError`](@ref) otherwise.
"""
function validate_policy(decision::Symbol, information::AbstractVector{FiniteAxis},
                         action::FiniteAxis, p::DeterministicPolicy)
    p.decision == decision ||
        throw(PolicySignatureError(decision, :decision, decision, p.decision))
    p.information == information ||
        throw(PolicySignatureError(decision, :information, information, p.information))
    p.action == action || throw(PolicySignatureError(decision, :action, action, p.action))
    return nothing
end

function validate_policy(decision::Symbol, information::AbstractVector{FiniteAxis},
                         action::FiniteAxis, p::StochasticPolicy)
    p.decision == decision ||
        throw(PolicySignatureError(decision, :decision, decision, p.decision))
    k = p.kernel
    k.dom == FiniteSpace(information) ||
        throw(PolicySignatureError(decision, :information, FiniteSpace(information),
                                   k.dom))
    k.codom == FiniteSpace(action) ||
        throw(PolicySignatureError(decision, :action, FiniteSpace(action), k.codom))
    is_normalized(k) ||
        throw(PolicySignatureError(decision, :normalisation, "a stochastic kernel",
                                   "column sums differ from one"))
    return nothing
end

function validate_policy(decision::Symbol, ::AbstractVector{FiniteAxis}, action::FiniteAxis,
                         p::ConstantPolicy)
    p.action in action.labels ||
        throw(PolicySignatureError(decision, :table, action.labels, p.action))
    return nothing
end

# Enumeration
#############

"""
    n_deterministic_policies(information::Vector{FiniteAxis}, action::FiniteAxis) -> BigInt
    n_deterministic_policies(m::InfluenceDiagramModel, decision) -> BigInt

The number `|A_D|^{|I_D|}` of deterministic policies of a decision, exactly, as a
`BigInt`. The count grows doubly exponentially in the information set (seven binary
information variables and two actions already give `2^128`), so it is computed in
arbitrary precision rather than in machine integers, which would silently wrap to zero.
[`all_deterministic_policies`](@ref) and [`ExhaustivePolicySearch`](@ref) compare it
against their limits and throw [`PolicySearchTooLargeError`](@ref).
"""
function n_deterministic_policies(information::AbstractVector{FiniteAxis},
                                  action::FiniteAxis)
    return BigInt(length(action))^prod(BigInt[length(a) for a in information];
                                       init=BigInt(1))
end

"""
    all_deterministic_policies(decision, information::Vector{FiniteAxis}, action::FiniteAxis) -> Vector{DeterministicPolicy}
    all_deterministic_policies(m::InfluenceDiagramModel, decision) -> Vector{DeterministicPolicy}

Every deterministic policy of a decision, in lexicographic order of the action labels
over the information states (column-major over the information axes). There are
`|A_D|^{|I_D|}` of them, so this is only for small decisions; more than `typemax(Int)`
throws [`PolicySearchTooLargeError`](@ref), and the [`ExhaustivePolicySearch`](@ref)
backend caps the total much lower.
"""
function all_deterministic_policies(decision::Symbol,
                                    information::AbstractVector{FiniteAxis},
                                    action::FiniteAxis)
    dims = Tuple(length(a) for a in information)
    nstates = prod(dims; init=1)
    na = length(action.labels)
    total = n_deterministic_policies(information, action)
    total > typemax(Int) && throw(PolicySearchTooLargeError(total, typemax(Int)))
    n = Int(total)
    out = DeterministicPolicy[]
    sizehint!(out, n)
    # Mixed-radix counter over the information states, first state fastest.
    digits_ = zeros(Int, nstates)
    for _ in 1:n
        table = reshape(Symbol[action.labels[d + 1] for d in digits_], dims)
        push!(out, DeterministicPolicy(decision, information, action, table))
        i = 1
        while i <= nstates
            digits_[i] += 1
            digits_[i] < na && break
            digits_[i] = 0
            i += 1
        end
    end
    return out
end

# Strategies
############

"""
    Strategy(policies::Dict{Symbol,AbstractPolicy})
    Strategy(pairs::Pair{Symbol,<:AbstractPolicy}...)
    Strategy()

A set of policies keyed by decision name (SPEC §27). A strategy is complete for a
diagram when it has a policy for every decision ([`is_complete`](@ref)). Strategies
are immutable values; [`set_policy`](@ref) and [`fix_decision`](@ref) return new
models with new strategies.
"""
struct Strategy
    policies::Dict{Symbol,AbstractPolicy}
    Strategy(policies::AbstractDict{Symbol}) = new(Dict{Symbol,AbstractPolicy}(policies))
end

Strategy() = Strategy(Dict{Symbol,AbstractPolicy}())
function Strategy(pairs::Pair{Symbol,<:AbstractPolicy}...)
    return Strategy(Dict{Symbol,AbstractPolicy}(pairs))
end

"""
    policies(σ::Strategy) -> Dict{Symbol,AbstractPolicy}

The policies of a strategy, keyed by decision name.
"""
policies(σ::Strategy) = σ.policies

Base.getindex(σ::Strategy, d::Symbol) = σ.policies[d]
Base.haskey(σ::Strategy, d::Symbol) = haskey(σ.policies, d)
Base.keys(σ::Strategy) = keys(σ.policies)
Base.length(σ::Strategy) = length(σ.policies)
Base.isempty(σ::Strategy) = isempty(σ.policies)
Base.:(==)(a::Strategy, b::Strategy) = a.policies == b.policies
Base.hash(σ::Strategy, h::UInt) = hash(σ.policies, h)

function Base.show(io::IO, σ::Strategy)
    ds = sort!(collect(keys(σ.policies)))
    return print(io, "Strategy(",
                 join(("$d => $(nameof(typeof(σ.policies[d])))"
                       for d in ds), ", "), ")")
end

"""
    missing_policies(σ::Strategy, id::AbstractInfluenceDiagram) -> Vector{Symbol}

The decisions of `id` (by name, in part-id order) without a policy in `σ`.
"""
function missing_policies(σ::Strategy, id::AbstractInfluenceDiagram)
    return Symbol[d for d in decision_names(id) if !haskey(σ.policies, d)]
end

"""
    is_complete(σ::Strategy, id::AbstractInfluenceDiagram) -> Bool

Whether `σ` has a policy for every decision of `id` (SPEC §37 item 10).
"""
is_complete(σ::Strategy, id::AbstractInfluenceDiagram) = isempty(missing_policies(σ, id))
