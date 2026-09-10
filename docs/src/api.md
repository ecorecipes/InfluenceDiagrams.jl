# API Reference

```@docs
InfluenceDiagrams
```

## Schema and types

```@docs
SchInfluenceDiagram
AbstractInfluenceDiagram
InfluenceDiagramUntyped
InfluenceDiagram
BayesNet(::AbstractInfluenceDiagram)
canonicalize(::AbstractInfluenceDiagram)
is_isomorphic(::AbstractInfluenceDiagram, ::AbstractInfluenceDiagram)
```

## Construction

```@docs
influence_diagram
add_decision!
add_information!
add_utility!
add_utility_input!
add_precedence!
decision_id
utility_id
```

## Inspection

```@docs
decisions
decision_names
decision_name
decision_variable
decision_of
is_decision
decision_information
information_ids
information_names
action_variables
action_names
chance_variables
chance_names
utilities
utility_names
utility_name
utility_ref
utility_input_ids
utility_scope
utility_scope_names
precedences
information_graph
decision_order
no_forgetting_arcs
is_no_forgetting
admissible_information
```

## Validation and errors

```@docs
validate(::AbstractInfluenceDiagram)
validate(::InfluenceDiagramModel)
validation_errors
InfluenceDiagramError
UnknownDecisionError
UnknownUtilityError
DecisionUniquenessError
InvalidInformationSetError
DecisionPrecedenceCycleError
PolicySignatureError
UtilityScopeError
IncompleteStrategyError
MissingUtilityError
PolicySearchTooLargeError
UnsupportedAggregationError
IrregularDiagramError
EvidenceOnActionError
UneliminatedVariablesError
DVEExportError
```

## Policies and strategies

```@docs
AbstractPolicy
DeterministicPolicy
StochasticPolicy
ConstantPolicy
policy_kernel
policy_table
validate_policy
deterministic_policy
all_deterministic_policies
n_deterministic_policies
Strategy
policies
is_complete
missing_policies
```

## Utilities

```@docs
AbstractUtility
TabularUtility
FunctionUtility
scope(::TabularUtility)
utility_value
utility_table
utility_factor
```

## Models

```@docs
InfluenceDiagramModel
bayes_model
strategy
bound_utilities
bind_utility
utility
missing_utilities
action_space
information_space
set_policy
unset_policy
fix_decision
with_information
without_information
with_no_forgetting
observe(::InfluenceDiagramModel, ::Any)
do_intervention(::InfluenceDiagramModel, ::Pair{Symbol,Symbol})
soft_intervention(::InfluenceDiagramModel, ::Pair{Symbol,<:FiniteKernel})
Base.isapprox(::InfluenceDiagramModel, ::InfluenceDiagramModel)
```

## Instantiation and expected utility

```@docs
instantiate
policy_mechanism_name
total_utility
expected_utility
```

## Optimisation

The complete model-data interface is documented under
[Exact-data model certificates](certificates.md).

```@docs
export_dve_certificate
trace_decision_elimination
```

```@docs
DecisionBackend
ExhaustivePolicySearch
DecisionVariableElimination
DecisionSolution
optimize
decision_elimination
strong_elimination_order
Valuation
scope(::Valuation)
combine
sum_out
max_out
```

## Value of information

```@docs
expected_value_of_information
expected_value_of_perfect_information
```

## Formats, serialisation and drawing

```@docs
read_influence_diagram
write_influence_diagram
NetworkIR(::InfluenceDiagramModel)
to_graphviz(::AbstractInfluenceDiagram)
json_influence_diagram
parse_json_influence_diagram
write_json_influence_diagram
read_json_influence_diagram
```

## Examples

```@docs
umbrella_diagram
umbrella_model
reference_grazing_diagram
reference_grazing_model
two_stage_diagram
two_stage_model
```
