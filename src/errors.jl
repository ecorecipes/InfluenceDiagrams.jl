"""
Typed exceptions of the influence-diagram layer (SPEC §37, §54). Every error carries the
offending names so that its message can be read without the diagram at hand. All of
them are `BayesNetError`s, so code that catches the BayesianNetworks.jl family catches
these too.
"""

"""
    InfluenceDiagramError

Abstract supertype of every exception introduced by InfluenceDiagrams.jl. It is a
subtype of `BayesianNetworks.BayesNetError`.
"""
abstract type InfluenceDiagramError <: BayesNetError end

"""
    UnknownDecisionError(name)

No decision is called `name`, and no decision controls a variable called `name`.
"""
struct UnknownDecisionError <: InfluenceDiagramError
    name::Symbol
end

"""
    UnknownUtilityError(name)

No utility node is called `name`.
"""
struct UnknownUtilityError <: InfluenceDiagramError
    name::Symbol
end

"""
    DecisionUniquenessError(decision, variable, reason)

SPEC §37 items 1 and 2. `reason` is `:duplicate_decision` (variable `variable` is
controlled by more than one decision; `decision` is the second one) or
`:has_mechanism` (the action variable of `decision` also has a chance mechanism, which
an uninstantiated decision must not have).
"""
struct DecisionUniquenessError <: InfluenceDiagramError
    decision::Symbol
    variable::Symbol
    reason::Symbol
end

"""
    InvalidInformationSetError(decision, variable, reason)

SPEC §37 items 3 and 4. `variable` cannot be in the information set of `decision`
because of `reason`: `:self` (it is the decision's own action), `:duplicate` (listed
twice), `:downstream` (it is causally or informationally downstream of the action, so it
cannot be known when the decision is taken) or `:unknown` (no such variable).
"""
struct InvalidInformationSetError <: InfluenceDiagramError
    decision::Symbol
    variable::Symbol
    reason::Symbol
end

"""
    DecisionPrecedenceCycleError(decisions)

SPEC §37 items 8 and 11. The decision precedence (explicit `DecisionPrecedence` rows
together with the order induced by causal and information arcs) has a cycle through
`decisions`.
"""
struct DecisionPrecedenceCycleError <: InfluenceDiagramError
    decisions::Vector{Symbol}
end

"""
    PolicySignatureError(decision, what, expected, got)

SPEC §37 item 9. A policy does not match its decision: `what` is `:information` (the
policy reads other variables than the information set, in another order, or with other
states), `:action` (the policy's action axis is not the action variable's), `:table`
(a policy table has the wrong size or an action label that does not exist),
`:normalisation` (a stochastic policy is not a stochastic kernel) or `:decision` (the
policy names another decision).
"""
struct PolicySignatureError <: InfluenceDiagramError
    decision::Symbol
    what::Symbol
    expected::Any
    got::Any
end

"""
    UtilityScopeError(utility, what, expected, got)

SPEC §37 items 6 and 7. A utility node or a utility bound to it is malformed: `what` is
`:duplicate` (a variable appears twice in the scope), `:scope` (a bound utility reads
other variables than the node's scope), `:table` (a table has the wrong size) or
`:value` (a utility function returned something that is not a real number).
"""
struct UtilityScopeError <: InfluenceDiagramError
    utility::Symbol
    what::Symbol
    expected::Any
    got::Any
end

"""
    IncompleteStrategyError(missing)

SPEC §37 item 10. The strategy has no policy for the decisions in `missing`.
"""
struct IncompleteStrategyError <: InfluenceDiagramError
    missing::Vector{Symbol}
end

"""
    MissingUtilityError(utility, ref)

SPEC §37 item 7. Utility node `utility` carries the reference `ref`, which does not
resolve to a bound utility of the model.
"""
struct MissingUtilityError <: InfluenceDiagramError
    utility::Symbol
    ref::KernelRef
end

"""
    PolicySearchTooLargeError(nstrategies, limit)

[`ExhaustivePolicySearch`](@ref) or [`all_deterministic_policies`](@ref) was asked to
enumerate `nstrategies` deterministic strategies, more than the `max_policies` limit
(or more than `typemax(Int)`, which cannot be enumerated at all). Both counts are
`BigInt`s, because `|A_D|^{|I_D|}` overflows machine integers on very small diagrams
(seven binary information variables and two actions already give `2^128`).
"""
struct PolicySearchTooLargeError <: InfluenceDiagramError
    nstrategies::BigInt
    limit::BigInt
end
function PolicySearchTooLargeError(nstrategies::Integer, limit::Integer)
    return PolicySearchTooLargeError(BigInt(nstrategies), BigInt(limit))
end

"""
    EvidenceOnActionError(variable, decision, state)

Evidence was set on `variable`, which is the action variable of `decision`. An action
variable has no chance mechanism, so there is nothing to condition: the value of a
decision is set by [`fix_decision`](@ref) or [`set_policy`](@ref) (a decision
operation), not by [`observe`](@ref) (a probabilistic one). See SPEC §41, which keeps
observation, intervention and fixing a decision distinct.
"""
struct EvidenceOnActionError <: InfluenceDiagramError
    variable::Symbol
    decision::Symbol
    state::Symbol
end

"""
    UneliminatedVariablesError(variables)

[`DecisionVariableElimination`](@ref) finished its blocks with `variables` still in the
scope of the combined valuation. This is an internal inconsistency (every variable of
the diagram belongs to exactly one block), reported as a typed exception rather than a
bare `error`.
"""
struct UneliminatedVariablesError <: InfluenceDiagramError
    variables::Vector{Symbol}
end

"""
    DVEExportError(code, owner_kind, owner_id, owner_name, coordinates, message)

A model cannot be represented by the requested DVE certificate profile.
`code` identifies the unsupported mode, scalar, companion, structure or resource
condition. The owner and zero-based coordinates identify an offending table cell
when applicable. No partial certificate is returned.
"""
struct DVEExportError <: InfluenceDiagramError
    code::Symbol
    owner_kind::Symbol
    owner_id::Union{Nothing,Int}
    owner_name::String
    coordinates::Vector{Int}
    message::String
end

function Base.showerror(io::IO, e::DVEExportError)
    print(io, "DVEExportError(", e.code, ") in ", e.owner_kind, " ", repr(e.owner_name))
    e.owner_id === nothing || print(io, " [part ", e.owner_id, "]")
    isempty(e.coordinates) || print(io, " at ", Tuple(e.coordinates))
    return print(io, ": ", e.message)
end

"""
    UnsupportedAggregationError(node, weights)

A multi-attribute utility node of a GeNIe file weights its utilities by `weights`, which
are not all one; only additive aggregation (SPEC §30) is supported.
"""
struct UnsupportedAggregationError <: InfluenceDiagramError
    node::Symbol
    weights::Vector{Float64}
end

"""
    IrregularDiagramError(decision, variables, what)

[`DecisionVariableElimination`](@ref) cannot solve the diagram exactly. `what` is
`:information` (when `decision` is maximised out, the utility potential still depends on
`variables`, which the decision maker does not observe: the diagram lacks no-forgetting
(perfect recall) and is a limited-memory influence diagram in the sense of
[LauritzenNilsson2001](@cite)), `:evidence` (the named evidence variables have
`decision`'s action as a causal ancestor), or `:probability` (a numerical bucket
probability row is not constant in the decision within the specified tolerance).

A diagram that is merely missing the no-forgetting arcs is repaired by
[`with_no_forgetting`](@ref); a diagram that is deliberately limited-memory must be
solved with [`ExhaustivePolicySearch`](@ref).
"""
struct IrregularDiagramError <: InfluenceDiagramError
    decision::Symbol
    variables::Vector{Symbol}
    what::Symbol
end

function Base.showerror(io::IO, e::UnknownDecisionError)
    return print(io, "UnknownDecisionError: no decision named :", e.name,
                 " and no decision controls a variable named :", e.name)
end

function Base.showerror(io::IO, e::UnknownUtilityError)
    return print(io, "UnknownUtilityError: no utility node named :", e.name)
end

function Base.showerror(io::IO, e::DecisionUniquenessError)
    if e.reason == :duplicate_decision
        print(io, "DecisionUniquenessError: variable :", e.variable,
              " is controlled by more than one decision (including :", e.decision, ")")
    else
        print(io, "DecisionUniquenessError: the action variable :", e.variable,
              " of decision :", e.decision, " also has a chance mechanism")
    end
    return nothing
end

function Base.showerror(io::IO, e::InvalidInformationSetError)
    reasons = Dict(:self => "is the decision's own action variable",
                   :duplicate => "is listed more than once",
                   :downstream => "is downstream of the decision's action, so it is not available when the decision is taken",
                   :unknown => "does not exist")
    return print(io, "InvalidInformationSetError: variable :", e.variable,
                 " cannot inform decision :", e.decision, ": it ",
                 get(reasons, e.reason, string(e.reason)))
end

function Base.showerror(io::IO, e::DecisionPrecedenceCycleError)
    return print(io,
                 "DecisionPrecedenceCycleError: the decision order has a cycle through ",
                 join(e.decisions, ", "))
end

function Base.showerror(io::IO, e::PolicySignatureError)
    return print(io, "PolicySignatureError: the policy of decision :", e.decision,
                 " has the wrong ", e.what, "; expected ", e.expected, ", got ", e.got)
end

function Base.showerror(io::IO, e::UtilityScopeError)
    return print(io, "UtilityScopeError: utility :", e.utility, ": ", e.what,
                 " mismatch; expected ", e.expected, ", got ", e.got)
end

function Base.showerror(io::IO, e::IncompleteStrategyError)
    return print(io, "IncompleteStrategyError: the strategy has no policy for decision(s) ",
                 join(e.missing, ", "))
end

function Base.showerror(io::IO, e::MissingUtilityError)
    return print(io, "MissingUtilityError: utility node :", e.utility, " has reference ",
                 e.ref, ", which does not resolve to a bound utility")
end

function Base.showerror(io::IO, e::PolicySearchTooLargeError)
    return print(io, "PolicySearchTooLargeError: ", e.nstrategies,
                 " deterministic strategies exceed the limit of ", e.limit,
                 " (raise max_policies or use DecisionVariableElimination)")
end

function Base.showerror(io::IO, e::UnsupportedAggregationError)
    return print(io, "UnsupportedAggregationError: multi-attribute utility node :", e.node,
                 " has weights ", e.weights, "; only unit weights (additive utility) ",
                 "are supported")
end

function Base.showerror(io::IO, e::EvidenceOnActionError)
    return print(io, "EvidenceOnActionError: cannot observe :", e.variable, " = :",
                 e.state, "; it is the action variable of decision :", e.decision,
                 ", whose value is set by fix_decision or set_policy, not by observe")
end

function Base.showerror(io::IO, e::UneliminatedVariablesError)
    return print(io,
                 "UneliminatedVariablesError: decision variable elimination left ",
                 join(e.variables, ", "), " uneliminated")
end

function Base.showerror(io::IO, e::IrregularDiagramError)
    if e.what == :information
        print(io, "IrregularDiagramError: when decision :", e.decision,
              " is maximised, the utility potential still depends on ",
              join(e.variables, ", "),
              ", which the decision maker does not observe; decision variable ",
              "elimination is exact only for diagrams with no-forgetting (perfect ",
              "recall). Add the missing information arcs with with_no_forgetting, or ",
              "solve this limited-memory diagram with ExhaustivePolicySearch")
    elseif e.what == :evidence
        print(io, "IrregularDiagramError: evidence on ", join(e.variables, ", "),
              " is downstream of decision :", e.decision,
              "; its probability may depend on the policy. Use ExhaustivePolicySearch ",
              "for action-descendant evidence")
    else
        print(io, "IrregularDiagramError: the probability potential depends on decision :",
              e.decision, " (variables ", join(e.variables, ", "),
              "); the probability-constancy precondition failed. Use ExhaustivePolicySearch")
    end
    return nothing
end
