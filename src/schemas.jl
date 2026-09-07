"""
The influence-diagram schema (SPEC §24 with the revision note's `information_position`
and `utility_position`). `SchInfluenceDiagram` extends `SchBayesNet`; decisions,
information inputs, utilities, utility inputs and decision precedence are separate
objects, so the three kinds of arc (causal `Input`, informational `InformationInput`,
value `UtilityInput`) can never be confused (SPEC §23, §34); the representation
choices this settles are the ones surveyed by [BielzaGomezShenoy2011](@cite). The declaration is
normative: the Lean project in `proofs/` emits the same schema as
`proofs/schemas/influence_diagram.schema.json`, and the test suite compares the two.
"""

"""
    SchInfluenceDiagram

Schema of a structural influence diagram, extending `SchBayesNet` with

- `Decision` (attribute `decision_name`) and `decision_variable: Decision -> Variable`,
  the action variable a decision controls (SPEC §25);
- `InformationInput` with `information_decision` and `information_variable` and the
  attribute `information_position`, the ordered information set of a decision
  (SPEC §26, §34);
- `Utility` (attributes `utility_name`, `utility_ref`) and `UtilityInput` with
  `utility_node`, `utility_variable` and `utility_position`, the ordered scope of a
  utility node (SPEC §29);
- `DecisionPrecedence` with `earlier` and `later`, explicit decision ordering
  (SPEC §36).

Utilities are not variables, so a utility node can never be the parent of a mechanism
or an information input (SPEC §37 item 5 holds by construction). There are no path
equations.

Like `SchBayesNet`, this is an ACSets.jl `BasicSchema` rather than a Catlab `@present`
presentation (ADR 0009); the generators of `SchBayesNet` come first, exactly as
`@present SchInfluenceDiagram <: SchBayesNet` ordered them, so the emitted schema JSON
is unchanged.
"""
const SchInfluenceDiagram = BasicSchema(vcat(collect(objects(SchBayesNet)),
                                             [:Decision, :InformationInput, :Utility,
                                              :UtilityInput, :DecisionPrecedence]),
                                        vcat(collect(homs(SchBayesNet)),
                                             [(:decision_variable, :Decision, :Variable),
                                              (:information_decision, :InformationInput,
                                               :Decision),
                                              (:information_variable, :InformationInput,
                                               :Variable),
                                              (:utility_node, :UtilityInput, :Utility),
                                              (:utility_variable, :UtilityInput,
                                               :Variable),
                                              (:earlier, :DecisionPrecedence, :Decision),
                                              (:later, :DecisionPrecedence, :Decision)]),
                                        collect(attrtypes(SchBayesNet)),
                                        vcat(collect(attrs(SchBayesNet)),
                                             [(:decision_name, :Decision, :Label),
                                              (:utility_name, :Utility, :Label),
                                              (:utility_ref, :Utility, :Ref),
                                              (:information_position, :InformationInput,
                                               :Position),
                                              (:utility_position, :UtilityInput,
                                               :Position)]))

"""
    AbstractInfluenceDiagram{S, Ts, P} <: AbstractBayesNet{S, Ts, P}

Abstract supertype of ACSets whose schema contains `SchInfluenceDiagram`. Every
inspection, graph and validation function of BayesianNetworks.jl accepts one, because
it is also an `AbstractBayesNet`.
"""
@abstract_acset_type AbstractInfluenceDiagram <: AbstractBayesNet

"""
    InfluenceDiagramUntyped{Label, Position, Ref}

ACSet type for `SchInfluenceDiagram` with attribute types left open. Use
[`InfluenceDiagram`](@ref) for the standard instantiation. All homs are indexed with
plain (non-unique) indexes, so uniqueness violations are reported by
[`validate`](@ref), never raised inside ACSet operations.
"""
@acset_type InfluenceDiagramUntyped(SchInfluenceDiagram;
                                    index=[:state_variable, :variable_name, :target,
                                           :input_mechanism, :input_variable,
                                           :decision_variable, :information_decision,
                                           :information_variable, :utility_node,
                                           :utility_variable, :earlier, :later]) <:
            AbstractInfluenceDiagram

"""
    InfluenceDiagram

A structural influence diagram with `Symbol` labels, `Int` positions and `KernelRef`
references: `InfluenceDiagramUntyped{Symbol, Int, KernelRef}`.

`InfluenceDiagram()` is empty; `InfluenceDiagram(bn::BayesNet)` copies the variables,
states, mechanisms and inputs of a Bayesian network so that decisions and utilities can
be added on top. It carries no numerical tables: kernels, policies and utilities are
bound in an [`InfluenceDiagramModel`](@ref).

# Example

```jldoctest
julia> id = influence_diagram(:Weather => [:sunny, :rainy], :Forecast => [:sunny, :cloudy, :rainy],
                              :Umbrella => [:take, :leave];
                              mechanisms = [:Forecast => :Weather],
                              decisions = [:Umbrella => [:Forecast]],
                              utilities = [:U => [:Weather, :Umbrella]]);

julia> nparts(id, :Decision), nparts(id, :InformationInput), nparts(id, :Utility)
(1, 1, 1)

julia> variable_name.(Ref(id), decision_information(id, :Umbrella))
1-element Vector{Symbol}:
 :Forecast
```
"""
const InfluenceDiagram = InfluenceDiagramUntyped{Symbol,Int,KernelRef}

const _BN_OBJECTS = (:Variable, :State, :Mechanism, :Input)

function InfluenceDiagram(bn::AbstractBayesNet)
    id = InfluenceDiagram()
    copy_parts!(id, bn, _BN_OBJECTS)
    return id
end

"""
    BayesNet(id::AbstractInfluenceDiagram) -> BayesNet

The Bayesian-network part of an influence diagram: its variables, states, mechanisms
and inputs, with the decisions, information inputs, utilities and precedence rows
dropped. This is the pullback data migration along the schema inclusion
`SchBayesNet -> SchInfluenceDiagram`. The action variables keep their states but have
no mechanism, so the result is an open network unless every decision was instantiated
first (see [`instantiate`](@ref)).
"""
function BayesianNetworks.BayesNet(id::AbstractInfluenceDiagram)
    bn = BayesNet()
    copy_parts!(bn, id, _BN_OBJECTS)
    return bn
end
