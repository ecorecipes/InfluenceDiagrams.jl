"""
Policy substitution (SPEC §28), the central reduction: an influence diagram together
with a complete strategy is an ordinary Bayesian network. Every decision becomes a
mechanism whose inputs are its information set (in `information_position` order) and
whose kernel is the policy's kernel; the Bayesian-network part of the diagram is then
copied into a fresh `BayesNet` (the pullback data migration along the schema
inclusion) and validated as a closed network.

This is `instantiate` / `strategyKernel` of the Lean model, whose theorem
`closed_instantiate` (Proposition 5) is checked numerically here by `validate(closed =
true)` and by the normalisation of the resulting joint.
"""

"""
    policy_mechanism_name(decision::Symbol) -> Symbol

The name of the mechanism that [`instantiate`](@ref) adds for a decision:
`Symbol("policy[D]")`.
"""
policy_mechanism_name(d::Symbol) = Symbol("policy[", d, "]")

"""
    instantiate(m::InfluenceDiagramModel, strategy = strategy(m); atol = 1e-8) -> BayesModel

The Bayesian network `BN_σ` of the diagram under the complete strategy `σ` (SPEC §28,
Proposition 5). For every decision `D` a mechanism [`policy_mechanism_name`](@ref)`(D)`
with kernel reference `PolicyRef(D)` and inputs `I_D` (in `information_position` order)
is added, the policy's kernel ([`policy_kernel`](@ref)) is bound under that reference,
the Bayesian-network parts are copied into a fresh `BayesNet`, and the result is checked
with `validate(closed = true, unique_names = true)`. Chance kernels, spaces, evidence
and history are carried over; the bound utilities are stored in `extras(bn)[:utilities]`
(with `extras(bn)[:decisions]` naming the decisions and `extras(bn)[:source] ==
:influence_diagram`) so that [`expected_utility`](@ref) can be computed on the result.

`atol` is the kernel-normalisation tolerance of the validation steps, to be matched to
the `atol` a model read from a file was parsed with.

Throws [`IncompleteStrategyError`](@ref) when a decision has no policy and
[`PolicySignatureError`](@ref) when a policy does not fit its decision. Information
arcs become causal inputs of the policy mechanism only here, and only for the supplied
policies (SPEC §34, §37 item 12).

# Example

```jldoctest
julia> m = umbrella_model();

julia> bn = instantiate(m, Strategy(:Umbrella => ConstantPolicy(:leave)));

julia> validate(bn; closed = true, semantics = true)

julia> mechanism_name.(Ref(syntax(bn)), mechanisms(syntax(bn)))
3-element Vector{Symbol}:
 :Forecast_mechanism
 :Weather_mechanism
 Symbol("policy[Umbrella]")

julia> sum(joint_distribution(bn).table) ≈ 1
true
```
"""
function instantiate(m::InfluenceDiagramModel, σ::Strategy=m.strategy;
                     atol::Real=BayesianNetworks.DEFAULT_ATOL)
    id = syntax(m)
    validate(id; unique_names=true)
    missing = missing_policies(σ, id)
    isempty(missing) || throw(IncompleteStrategyError(missing))
    work = deepcopy(id)
    ks = copy(kernels(m))
    for d in decisions(id)
        name = decision_name(id, d)
        p = σ[name]
        k = policy_kernel(p, m, d)
        mech = add_part!(work, :Mechanism; target=decision_variable(id, d),
                         mechanism_name=policy_mechanism_name(name),
                         kernel_ref=PolicyRef(name))
        for (i, v) in enumerate(decision_information(id, d))
            add_part!(work, :Input; input_mechanism=mech, input_variable=v,
                      input_position=i)
        end
        ks[PolicyRef(name)] = k
    end
    bn = BayesNet(work)
    validate(bn; closed=true, unique_names=true)
    ex = copy(extras(m))
    ex[:utilities] = copy(m.utilities)
    ex[:decisions] = decision_names(id)
    ex[:source] = :influence_diagram
    out = BayesModel(bn; spaces=spaces(m), kernels=ks, evidence=evidence(m),
                     history=history(m), extras=ex)
    validate(out; closed=true, atol=atol)
    return out
end
