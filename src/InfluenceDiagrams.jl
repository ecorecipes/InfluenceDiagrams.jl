"""
    InfluenceDiagrams

Influence diagrams over compositional Bayesian networks: decisions, information sets,
utilities, policies, expected utility, decision variable elimination, and value of
information. The representation is the classical one of
[HowardMatheson2005](@cite) (a reprint of the 1984 chapter), evaluated in the sense
of [Shachter1986](@cite).

The structural layer is the [`SchInfluenceDiagram`](@ref) schema (an extension of
`SchBayesNet` from BayesianNetworks.jl) and the [`InfluenceDiagram`](@ref) ACSet type,
with builders ([`influence_diagram`](@ref), `add_decision!`, `add_utility!`, ...),
inspection and [`validate`](@ref). The semantic layer is the
[`InfluenceDiagramModel`](@ref) wrapper: kernels and utilities bound to the syntax, a
[`Strategy`](@ref) of policies, evidence and provenance. The central reduction is
[`instantiate`](@ref), which turns an influence diagram plus a complete strategy into an
ordinary `BayesModel` (Proposition 5), from which [`expected_utility`](@ref) follows
(Proposition 6). [`optimize`](@ref) finds optimal strategies either by
[`ExhaustivePolicySearch`](@ref) (the oracle) or by [`DecisionVariableElimination`](@ref)
over the [`Valuation`](@ref) algebra (Proposition 7, property-tested), and
[`expected_value_of_information`](@ref) measures what observing a variable is worth.

Decision variable elimination is exact only on diagrams with *no-forgetting* (perfect
recall): everything known at a decision is still known at every later one. That is not a
validity condition, because a diagram that forgets is a well-formed limited-memory
influence diagram [LauritzenNilsson2001](@cite) which [`ExhaustivePolicySearch`](@ref)
solves exactly; [`validate`](@ref) therefore accepts it, [`no_forgetting_arcs`](@ref)
reports what is missing, [`with_no_forgetting`](@ref) adds the arcs, and the solver
points at both in its [`IrregularDiagramError`](@ref). The *regular* of
[Shachter1986](@cite) is the weaker property that a directed path runs through all the
decisions; the two terms are kept apart throughout.

The representation choices behind the three kinds of arc, the separate utility nodes
and the no-forgetting convention are surveyed by [BielzaGomezShenoy2011](@cite).

Part of the ecorecipes compositional Bayesian-network ecosystem.
"""
module InfluenceDiagrams

using ACSets
using ACSets: BasicSchema, objects, homs, attrtypes, attrs
using GATlab: Presentation
using Graphs: SimpleDiGraph, add_edge!, nv, edges, src, dst, outneighbors
using JSON3: JSON3
using StructTypes: StructTypes
using Random: AbstractRNG, default_rng
using FiniteKernels
using FiniteKernels: label_index
using BayesianNetworks
using BayesianNetworks: Graphviz
using BayesianNetworks: AbstractVariableSpace, AbstractBayesNet, BayesNetError,
                        MissingMechanismError, DuplicateGeneratorError,
                        DanglingReferenceError, MissingAttributeError, PositionError,
                        DuplicateNameError,
                        CyclicBayesNetError, UnknownVariableError, UnknownStateError,
                        MissingKernelError, ModelTooLargeError, UnsupportedNodeKindError,
                        KernelBindingError, MechanismRecord, ModelEvent,
                        hard_intervention_name, json_bayesnet, FormatError
# OrderedCollections' type, which BayesianNetworks imports and returns for its CatColab
# documents; taking that binding adds no dependency here (see CLAUDE.md).
using BayesianNetworks: OrderedDict
using BayesianNetworkInference: BayesianNetworkInference, Factor, scope, unit_factor,
                                multiply, marginalize, maximize,
                                argmax_table, condition, reorder, FactorGraph,
                                elimination_order, EliminationStrategy, MinFill
using BayesianNetworkFormats: NetworkIR, IRVariable, MAUNode, ChanceNode, DecisionNode,
                              UtilityNode, read_network, write_network, fixture_path

import BayesianNetworks: validate, to_graphviz
import BayesianNetworks: validation_errors, observe, unobserve, do_intervention,
                         soft_intervention, bind_kernel, bind_cpt, kernel, space,
                         parent_space, syntax, spaces, kernels, evidence, history, extras,
                         canonicalize, is_isomorphic, marginal, joint_distribution,
                         joint_table, missing_kernels, has_semantics, intervened_variables,
                         is_intervened, schema_json, sample
import BayesianNetworkFormats: NetworkIR
import BayesianNetworkInference: Factor, scope

# Re-exported names from the structural and semantic layers of BayesianNetworks.jl that
# influence-diagram users need directly.
export nparts, parts, subpart, incident, add_part!, set_subpart!, cascading_rem_part!
export KernelRef, NamedRef, PointMassRef, PolicyRef, NoRef, BayesNet, BayesModel,
       SchBayesNet, AbstractBayesNet, add_variable!, add_state!, add_mechanism!,
       add_input!, variable_id, variables, variable_names, variable_name, has_variable,
       states, nstates, mechanisms, mechanism_of, has_mechanism, parents, children,
       inputs, target, mechanism_name, kernel_ref, topological_order, is_acyclic,
       variable_graph, validate, validation_errors, canonicalize, is_isomorphic,
       syntax, spaces, kernels, evidence, history, extras, bind_kernel, bind_cpt, kernel,
       space, parent_space, observe, unobserve, do_intervention, soft_intervention,
       joint_distribution, joint_table, marginal, missing_kernels, has_semantics,
       intervened_variables, is_intervened, schema_json, sample, fixture_path
export FiniteAxis, FiniteSpace, FiniteKernel, cpt, state, point_mass, deterministic,
       uniform, probability, labels, joint_states, is_normalized, random_kernel
export Factor, scope, NetworkIR
# Re-exported exception types (ADR 0013). This package re-exports much of the
# BayesianNetworks and BayesianNetworkInference APIs, so it re-exports, wholesale, every
# exception type (and root, and the `AnyBayesNetError` union) those two export: among them
# `ImpossibleEvidenceError`, which every solver here raises for evidence of probability
# exactly zero (ADRs 0012 and 0014), `IndeterminatePosteriorError`, and Inference's
# `ScopeError`. A type added to either package later
# arrives by itself. Every binding is its owner's, never a second definition, so the names
# stay unambiguous and the frozen ones print unqualified. Neither package exports
# BayesianNetworkFormats' concrete error types, so none is re-exported here: the conformance
# adapters load this package with `using` and record those types under qualified names.
for M in (BayesianNetworks, BayesianNetworkInference), name in names(M)
    T = getglobal(M, name)
    T isa Type && T <: Exception || continue
    if M === BayesianNetworkInference && name ∉ names(BayesianNetworks)
        @eval using BayesianNetworkInference: $name
    end
    @eval export $name
end

# errors.jl
export InfluenceDiagramError, UnknownDecisionError, UnknownUtilityError,
       DecisionUniquenessError, InvalidInformationSetError, DecisionPrecedenceCycleError,
       PolicySignatureError, UtilityScopeError, IncompleteStrategyError,
       MissingUtilityError, PolicySearchTooLargeError, UnsupportedAggregationError,
       IrregularDiagramError, EvidenceOnActionError, UneliminatedVariablesError,
       DVEExportError
# schemas.jl
export SchInfluenceDiagram, AbstractInfluenceDiagram, InfluenceDiagramUntyped,
       InfluenceDiagram
# construction.jl
export decision_id, utility_id, add_decision!, add_information!, add_utility!,
       add_utility_input!, add_precedence!, influence_diagram
# inspection.jl
export decisions, decision_names, decision_name, decision_variable, decision_of,
       is_decision, decision_information, information_ids, information_names, utilities,
       utility_names, utility_name, utility_scope, utility_input_ids, utility_scope_names,
       utility_ref, precedences, decision_order, action_variables, chance_variables,
       action_names, chance_names, information_graph, no_forgetting_arcs,
       is_no_forgetting
# serialization.jl
export json_influence_diagram, parse_json_influence_diagram, write_json_influence_diagram,
       read_json_influence_diagram
# policies.jl
export AbstractPolicy, DeterministicPolicy, StochasticPolicy, ConstantPolicy,
       policy_kernel, policy_table, Strategy, policies, is_complete, missing_policies,
       validate_policy, all_deterministic_policies, n_deterministic_policies,
       deterministic_policy
# utilities.jl
export AbstractUtility, TabularUtility, FunctionUtility, utility_value, utility_factor,
       utility_table
# model.jl
export InfluenceDiagramModel, bayes_model, strategy, bound_utilities, bind_utility,
       utility, missing_utilities, fix_decision, set_policy, unset_policy, with_information,
       without_information, with_no_forgetting, action_space, information_space
# instantiate.jl
export instantiate, policy_mechanism_name
# expected_utility.jl
export total_utility, expected_utility
# exhaustive.jl
export DecisionBackend, ExhaustivePolicySearch, DecisionSolution, optimize
# valuation.jl
export Valuation, combine, sum_out, max_out
# decision_elimination.jl
export DecisionVariableElimination, strong_elimination_order, decision_elimination,
       expected_value_of_information, expected_value_of_perfect_information,
       admissible_information
# formats_bridge.jl
export read_influence_diagram, write_influence_diagram
# certificates.jl
export export_dve_certificate
export trace_decision_elimination
# graphics.jl
export to_graphviz
# examples.jl
export umbrella_diagram, umbrella_model, reference_grazing_diagram,
       reference_grazing_model, two_stage_diagram, two_stage_model

include("errors.jl")
include("schemas.jl")
include("construction.jl")
include("inspection.jl")
include("validation.jl")
include("serialization.jl")
include("policies.jl")
include("utilities.jl")
include("model.jl")
include("instantiate.jl")
include("expected_utility.jl")
include("exhaustive.jl")
include("valuation.jl")
include("exact_arithmetic.jl")
include("decision_elimination.jl")
include("certificates.jl")
include("execution_trace.jl")
include("formats_bridge.jl")
include("graphics.jl")
include("examples.jl")

end # module
