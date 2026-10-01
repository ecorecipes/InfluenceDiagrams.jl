/-
Axiom audit: `lake env lean Audit.lean` (or `make audit`). Every theorem below must report at
most `propext`, `Classical.choice` and `Quot.sound`. The completed Roadmap theorem now
lives in the default library; the remaining-work module itself is not needed here.
-/
import InfluenceDiagramsProofs
import Mathlib.Util.AssertNoSorry

assert_no_sorry InfluenceDiagramsProofs.firstArgmax_stable
assert_no_sorry InfluenceDiagramsProofs.FinInfluenceDiagram.orderedTable_reconstruct
#print axioms InfluenceDiagramsProofs.maximizing_nonempty
#print axioms InfluenceDiagramsProofs.firstArgmax_maximizes
#print axioms InfluenceDiagramsProofs.firstArgmax_first
#print axioms InfluenceDiagramsProofs.firstArgmax_stable
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.Policy.ofOrderedScore
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.orderedTable_reconstruct
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.orderedPolicy_table
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.orderedPolicy_is_local
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.orderedPolicy_maximizes

-- The driver parameterised by its selector; the first-label (least-state) selector's tables.
assert_no_sorry InfluenceDiagramsProofs.DVE.solveWith_spec
assert_no_sorry InfluenceDiagramsProofs.DVE.solveGuardedWith_spec
assert_no_sorry InfluenceDiagramsProofs.DVE.solveEvidenceWith_spec
assert_no_sorry InfluenceDiagramsProofs.DVE.solveOrdered_table
assert_no_sorry InfluenceDiagramsProofs.DVE.solveOrdered_semantic
#print axioms InfluenceDiagramsProofs.DVE.runWith_state
#print axioms InfluenceDiagramsProofs.DVE.run_state
#print axioms InfluenceDiagramsProofs.DVE.runWith_classical
#print axioms InfluenceDiagramsProofs.DVE.runWith_snd_of_notMem
#print axioms InfluenceDiagramsProofs.DVE.runWith_deterministic
#print axioms InfluenceDiagramsProofs.DVE.Inv.chance
#print axioms InfluenceDiagramsProofs.DVE.Inv.decisionOf
#print axioms InfluenceDiagramsProofs.DVE.Inv.decisionWith
#print axioms InfluenceDiagramsProofs.DVE.runWith_inv
#print axioms InfluenceDiagramsProofs.DVE.independent_one
#print axioms InfluenceDiagramsProofs.DVE.independent_evidence
#print axioms InfluenceDiagramsProofs.DVE.solveWith_classical
#print axioms InfluenceDiagramsProofs.DVE.solveWith_value
#print axioms InfluenceDiagramsProofs.DVE.solveWith_spec
#print axioms InfluenceDiagramsProofs.DVE.solveEvidenceWith_value
#print axioms InfluenceDiagramsProofs.DVE.solveEvidenceWith_spec
#print axioms InfluenceDiagramsProofs.DVE.checkedRunWith_eq_runWith
#print axioms InfluenceDiagramsProofs.DVE.solveGuardedWith_eq
#print axioms InfluenceDiagramsProofs.DVE.solveGuardedWith_spec
#print axioms InfluenceDiagramsProofs.DVE.solveEvidenceGuardedWith_eq
#print axioms InfluenceDiagramsProofs.DVE.score_le_iff_weight_le
#print axioms InfluenceDiagramsProofs.DVE.firstArgmax_congr
#print axioms InfluenceDiagramsProofs.DVE.firstArgmax_score_eq_weight
#print axioms InfluenceDiagramsProofs.DVE.decisionScore_local
#print axioms InfluenceDiagramsProofs.DVE.runWith_kernel
#print axioms InfluenceDiagramsProofs.DVE.solveScore_local
#print axioms InfluenceDiagramsProofs.DVE.solveOrdered_table
#print axioms InfluenceDiagramsProofs.DVE.freeJoint_nonneg
#print axioms InfluenceDiagramsProofs.DVE.reach_nonneg
#print axioms InfluenceDiagramsProofs.DVE.reach_continuation_at_step
#print axioms InfluenceDiagramsProofs.DVE.runWith_ordered_semantic
#print axioms InfluenceDiagramsProofs.DVE.solveOrdered_semantic
#print axioms InfluenceDiagramsProofs.DVE.solveEvidenceOrdered_semantic

-- Explicit (sliced) evidence conditioning versus the likelihood representation.
assert_no_sorry InfluenceDiagramsProofs.DVE.conditionedMass_eq
assert_no_sorry InfluenceDiagramsProofs.DVE.solveConditioned_spec
assert_no_sorry InfluenceDiagramsProofs.DVE.solveConditioned_policy_eq
assert_no_sorry InfluenceDiagramsProofs.DVE.solveConditioned_semantic
#print axioms InfluenceDiagramsProofs.DVE.Valuation.condition
#print axioms InfluenceDiagramsProofs.DVE.collect_condition_prob
#print axioms InfluenceDiagramsProofs.DVE.collect_condition_util
#print axioms InfluenceDiagramsProofs.DVE.collect_condition_scope
#print axioms InfluenceDiagramsProofs.DVE.State.chanceSkip
#print axioms InfluenceDiagramsProofs.DVE.runSkipWith
#print axioms InfluenceDiagramsProofs.DVE.runSkipWith_deterministic
#print axioms InfluenceDiagramsProofs.DVE.HardEvidence.toEvidence
#print axioms InfluenceDiagramsProofs.DVE.Inv.vanish
#print axioms InfluenceDiagramsProofs.DVE.Inv.clamp_eq
#print axioms InfluenceDiagramsProofs.DVE.Coupled.util_eq
#print axioms InfluenceDiagramsProofs.DVE.Coupled.chance_unobserved
#print axioms InfluenceDiagramsProofs.DVE.Coupled.chance_observed
#print axioms InfluenceDiagramsProofs.DVE.Coupled.decision
#print axioms InfluenceDiagramsProofs.DVE.Coupled.score_le_iff
#print axioms InfluenceDiagramsProofs.DVE.Coupled.maximizes
#print axioms InfluenceDiagramsProofs.DVE.initial_coupled
#print axioms InfluenceDiagramsProofs.DVE.conditioned_run
#print axioms InfluenceDiagramsProofs.DVE.conditioned_policy
#print axioms InfluenceDiagramsProofs.DVE.conditioned_final
#print axioms InfluenceDiagramsProofs.DVE.conditionedMass_eq
#print axioms InfluenceDiagramsProofs.DVE.solveConditioned_spec
#print axioms InfluenceDiagramsProofs.DVE.solveConditionedChecked_eq
#print axioms InfluenceDiagramsProofs.DVE.solveConditionedChecked_none_iff
#print axioms InfluenceDiagramsProofs.DVE.solveConditioned_policy_eq
#print axioms InfluenceDiagramsProofs.DVE.solveConditioned_semantic
#print axioms InfluenceDiagramsProofs.DVE.runSkipWith_kernel_clamp
#print axioms InfluenceDiagramsProofs.DVE.solveConditioned_kernel_clamp

-- First-label tables do not depend on the elimination plan (positive-reach rows).
assert_no_sorry InfluenceDiagramsProofs.DVE.solvePlanOrdered_table_eq
assert_no_sorry InfluenceDiagramsProofs.DVE.solveEvidencePlanOrdered_table_eq
assert_no_sorry InfluenceDiagramsProofs.DVE.solveConditionedPlan_table_eq
#print axioms InfluenceDiagramsProofs.DVE.MassAll.chance
#print axioms InfluenceDiagramsProofs.DVE.MassAll.prob_update
#print axioms InfluenceDiagramsProofs.DVE.MassAll.decision
#print axioms InfluenceDiagramsProofs.DVE.massAll_initial
#print axioms InfluenceDiagramsProofs.DVE.massAll_initialEvidence
#print axioms InfluenceDiagramsProofs.DVE.reach_strategy_independent
#print axioms InfluenceDiagramsProofs.DVE.weight_eq_optimalContinuation
#print axioms InfluenceDiagramsProofs.DVE.runWith_ordered_optimal
#print axioms InfluenceDiagramsProofs.DVE.solveWith_eq_solvePlanWith
#print axioms InfluenceDiagramsProofs.DVE.solveEvidenceWith_eq_solveEvidencePlanWith
#print axioms InfluenceDiagramsProofs.DVE.solveConditioned_eq_solveConditionedPlan
#print axioms InfluenceDiagramsProofs.DVE.solvePlanOrdered_optimal
#print axioms InfluenceDiagramsProofs.DVE.solvePlanOrdered_table_eq
#print axioms InfluenceDiagramsProofs.DVE.solveOrdered_table_plan_independent
#print axioms InfluenceDiagramsProofs.DVE.solveEvidencePlanOrdered_optimal
#print axioms InfluenceDiagramsProofs.DVE.solveEvidencePlanOrdered_table_eq
#print axioms InfluenceDiagramsProofs.DVE.solveConditionedPlan_policy_eq
#print axioms InfluenceDiagramsProofs.DVE.solveConditionedPlan_table_eq

-- Julia's sum-out utility representative on zero-probability rows (`keep`).
assert_no_sorry InfluenceDiagramsProofs.DVE.solveRepPlan_agrees
assert_no_sorry InfluenceDiagramsProofs.DVE.solveRepPlanWith_spec
assert_no_sorry InfluenceDiagramsProofs.DVE.solveRepPlanWith_kernel_eq
assert_no_sorry InfluenceDiagramsProofs.DVE.solveRepPlanOrdered_table
#print axioms InfluenceDiagramsProofs.DVE.Valuation.sumOutKeep_false
#print axioms InfluenceDiagramsProofs.DVE.Valuation.sumOutKeep_util_of_const
#print axioms InfluenceDiagramsProofs.DVE.Valuation.sumOutKeep_weight
#print axioms InfluenceDiagramsProofs.DVE.Valuation.Agrees.util_eq
#print axioms InfluenceDiagramsProofs.DVE.Valuation.agrees_collect
#print axioms InfluenceDiagramsProofs.DVE.Valuation.agrees_sumOut
#print axioms InfluenceDiagramsProofs.DVE.Valuation.agrees_maxOut
#print axioms InfluenceDiagramsProofs.DVE.Valuation.agrees_chanceStep
#print axioms InfluenceDiagramsProofs.DVE.Valuation.agrees_decisionStep
#print axioms InfluenceDiagramsProofs.DVE.Valuation.chanceStepKeep_collect
#print axioms InfluenceDiagramsProofs.DVE.runRepWith_state
#print axioms InfluenceDiagramsProofs.DVE.runRepWith_false
#print axioms InfluenceDiagramsProofs.DVE.runRepWith_deterministic
#print axioms InfluenceDiagramsProofs.DVE.Inv.chanceKeep
#print axioms InfluenceDiagramsProofs.DVE.runRepWith_inv
#print axioms InfluenceDiagramsProofs.DVE.decisionScoreRep_local
#print axioms InfluenceDiagramsProofs.DVE.runRepWith_kernel
#print axioms InfluenceDiagramsProofs.DVE.runRep_agrees
#print axioms InfluenceDiagramsProofs.DVE.bucketScore_agree
#print axioms InfluenceDiagramsProofs.DVE.decisionScoreRep_eq
#print axioms InfluenceDiagramsProofs.DVE.solveRepPlanWith_false
#print axioms InfluenceDiagramsProofs.DVE.solveRepPlan_agrees
#print axioms InfluenceDiagramsProofs.DVE.solveRepPlanWith_spec
#print axioms InfluenceDiagramsProofs.DVE.solveRepPlanWith_value
#print axioms InfluenceDiagramsProofs.DVE.solveRepPlanScore_eq
#print axioms InfluenceDiagramsProofs.DVE.solveRepPlanWith_kernel_eq
#print axioms InfluenceDiagramsProofs.DVE.solveRepPlanOrdered_table
#print axioms InfluenceDiagramsProofs.DVE.solveRepPlanOrdered_optimal

-- Action labels in checked state-position order (records -> action order -> selector).
assert_no_sorry InfluenceDiagramsProofs.Records.Diagram.solveRecords_table
assert_no_sorry InfluenceDiagramsProofs.Records.Diagram.solveRepRecords_table
assert_no_sorry InfluenceDiagramsProofs.Records.Diagram.solveRepRecords_optimal
#print axioms InfluenceDiagramsProofs.firstArgmax_least_position
#print axioms InfluenceDiagramsProofs.eq_firstArgmax_of_least_position
#print axioms InfluenceDiagramsProofs.Records.Diagram.check_iff
#print axioms InfluenceDiagramsProofs.Records.Diagram.stateRecord_var
#print axioms InfluenceDiagramsProofs.Records.Diagram.stateRecord_position
#print axioms InfluenceDiagramsProofs.Records.Diagram.stateRecord_of_mem
#print axioms InfluenceDiagramsProofs.Records.Diagram.statePosition_injective
#print axioms InfluenceDiagramsProofs.Records.Diagram.stateLabel_injective
#print axioms InfluenceDiagramsProofs.Records.Diagram.actionOrder_le_iff
#print axioms InfluenceDiagramsProofs.Records.Diagram.solveRecords_table
#print axioms InfluenceDiagramsProofs.Records.Diagram.solveRepRecords_table
#print axioms InfluenceDiagramsProofs.Records.Diagram.solveRepRecords_optimal

-- Exact multi-decision bucket DVE; the schedule is generated from no-forgetting.
assert_no_sorry InfluenceDiagramsProofs.DVE.solve_spec
assert_no_sorry InfluenceDiagramsProofs.DVE.solveEvidence_spec
assert_no_sorry InfluenceDiagramsProofs.DVE.solveEvidence_eq_optimal
assert_no_sorry InfluenceDiagramsProofs.DVE.NoForgettingOrder.plan
assert_no_sorry InfluenceDiagramsProofs.DVE.Example.checked_solution
assert_no_sorry InfluenceDiagramsProofs.DVE.all_guards_complete
assert_no_sorry InfluenceDiagramsProofs.DVE.all_guards_complete_evidence
assert_no_sorry InfluenceDiagramsProofs.DVE.checkedRun_generated_eq
assert_no_sorry InfluenceDiagramsProofs.DVE.checkedRun_generated_evidence_eq
assert_no_sorry InfluenceDiagramsProofs.DVE.solveGuarded_spec
assert_no_sorry InfluenceDiagramsProofs.DVE.solveEvidenceGuarded_none_iff

-- Exact all-row diagnostic completeness, including zero-outside contexts.
#print axioms InfluenceDiagramsProofs.DVE.spread_zero_iff
#print axioms InfluenceDiagramsProofs.DVE.exactGuard_iff_diagnostic
#print axioms InfluenceDiagramsProofs.DVE.checkedRun_eq_run
#print axioms InfluenceDiagramsProofs.DVE.guards_of_positive
#print axioms InfluenceDiagramsProofs.DVE.guards_of_positive_weighted
#print axioms InfluenceDiagramsProofs.DVE.Guard.represents_guards_iff
#print axioms InfluenceDiagramsProofs.DVE.Guard.initial_represents
#print axioms InfluenceDiagramsProofs.DVE.Guard.initialEvidence_represents
#print axioms InfluenceDiagramsProofs.DVE.Guard.argmax_value_eq_sup
#print axioms InfluenceDiagramsProofs.DVE.Guard.continuousAt_argmax_value
#print axioms InfluenceDiagramsProofs.DVE.Guard.Expr.continuousAt
#print axioms InfluenceDiagramsProofs.DVE.Guard.eq_at_zero_of_positive
#print axioms InfluenceDiagramsProofs.DVE.smoothKernel_zero
#print axioms InfluenceDiagramsProofs.DVE.smoothKernel_local
#print axioms InfluenceDiagramsProofs.DVE.smoothKernel_normalised
#print axioms InfluenceDiagramsProofs.DVE.smoothKernel_positive
#print axioms InfluenceDiagramsProofs.DVE.smoothKernel_continuousAt_zero
#print axioms InfluenceDiagramsProofs.DVE.all_guards_complete
#print axioms InfluenceDiagramsProofs.DVE.all_guards_complete_evidence
#print axioms InfluenceDiagramsProofs.DVE.checkedRun_generated_eq
#print axioms InfluenceDiagramsProofs.DVE.checkedRun_generated_evidence_eq
#print axioms InfluenceDiagramsProofs.DVE.solveGuarded_eq
#print axioms InfluenceDiagramsProofs.DVE.solveGuarded_spec
#print axioms InfluenceDiagramsProofs.DVE.solveEvidenceGuarded_eq
#print axioms InfluenceDiagramsProofs.DVE.solveEvidenceGuarded_none_iff
#print axioms InfluenceDiagramsProofs.DVE.GuardBoundary.closed
#print axioms InfluenceDiagramsProofs.DVE.GuardBoundary.κ_normalised
#print axioms InfluenceDiagramsProofs.DVE.GuardBoundary.zero_outside_context
#print axioms InfluenceDiagramsProofs.DVE.GuardBoundary.summed_child_retains_action_axis
#print axioms InfluenceDiagramsProofs.DVE.GuardBoundary.checked_zero_outside_model
#print axioms InfluenceDiagramsProofs.DVE.GuardBoundary.guard_accepts_zero_evidence
#print axioms InfluenceDiagramsProofs.DVE.GuardBoundary.mass_check_rejects_zero_evidence

#print axioms InfluenceDiagramsProofs.DVE.Valuation.sumOut_weight
#print axioms InfluenceDiagramsProofs.DVE.Valuation.chanceStep_prob
#print axioms InfluenceDiagramsProofs.DVE.Valuation.chanceStep_weight
#print axioms InfluenceDiagramsProofs.DVE.Valuation.choice_local
#print axioms InfluenceDiagramsProofs.DVE.Valuation.decisionStep_eval
#print axioms InfluenceDiagramsProofs.DVE.Valuation.decisionStep_dominates
#print axioms InfluenceDiagramsProofs.DVE.Valuation.bucket_probability_constant_on_support
#print axioms InfluenceDiagramsProofs.DVE.Valuation.step_scope_eq
#print axioms InfluenceDiagramsProofs.DVE.probability_independent_weighted
#print axioms InfluenceDiagramsProofs.DVE.probability_independent
#print axioms InfluenceDiagramsProofs.DVE.decision_marginal
#print axioms InfluenceDiagramsProofs.DVE.decision_marginal_pure
#print axioms InfluenceDiagramsProofs.DVE.State.policy
#print axioms InfluenceDiagramsProofs.DVE.run
#print axioms InfluenceDiagramsProofs.DVE.run_correct
#print axioms InfluenceDiagramsProofs.DVE.initial_correct
#print axioms InfluenceDiagramsProofs.DVE.initial_covers_chance
#print axioms InfluenceDiagramsProofs.DVE.chanceBucketsPresent_of_covers
#print axioms InfluenceDiagramsProofs.DVE.run_deterministic
#print axioms InfluenceDiagramsProofs.DVE.solvePlan_spec
#print axioms InfluenceDiagramsProofs.DVE.buildPlan
#print axioms InfluenceDiagramsProofs.DVE.NoForgettingOrder.plan
#print axioms InfluenceDiagramsProofs.DVE.RankedOrder.ofOrder
#print axioms InfluenceDiagramsProofs.DVE.solve
#print axioms InfluenceDiagramsProofs.DVE.solve_spec
#print axioms InfluenceDiagramsProofs.DVE.Evidence.hard
#print axioms InfluenceDiagramsProofs.DVE.Evidence.ranked
#print axioms InfluenceDiagramsProofs.DVE.Evidence.probability_independent
#print axioms InfluenceDiagramsProofs.DVE.evidenceMass_independent
#print axioms InfluenceDiagramsProofs.DVE.evidenceMass_nonneg
#print axioms InfluenceDiagramsProofs.DVE.run_weighted_correct
#print axioms InfluenceDiagramsProofs.DVE.initialEvidence_correct
#print axioms InfluenceDiagramsProofs.DVE.solveEvidence_spec
#print axioms InfluenceDiagramsProofs.DVE.runEvidence_mass
#print axioms InfluenceDiagramsProofs.DVE.solveEvidenceChecked_eq
#print axioms InfluenceDiagramsProofs.DVE.solveEvidenceChecked_none_iff
#print axioms InfluenceDiagramsProofs.DVE.expectedUtility_weighted
#print axioms InfluenceDiagramsProofs.DVE.solveEvidence_eq_optimal
#print axioms InfluenceDiagramsProofs.DVE.Example.closed
#print axioms InfluenceDiagramsProofs.DVE.Example.order
#print axioms InfluenceDiagramsProofs.DVE.Example.noForgetting
#print axioms InfluenceDiagramsProofs.DVE.Example.local_kernels
#print axioms InfluenceDiagramsProofs.DVE.Example.normalised_kernels
#print axioms InfluenceDiagramsProofs.DVE.Example.nonnegative_kernels
#print axioms InfluenceDiagramsProofs.DVE.Example.local_utility
#print axioms InfluenceDiagramsProofs.DVE.Example.hidden_state_never_observed
#print axioms InfluenceDiagramsProofs.DVE.Example.unreachable_row
#print axioms InfluenceDiagramsProofs.DVE.Example.checked_solution

-- Finite/Optimization.lean: exact mixtures and genuinely multi-decision global optimality.
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.tableStrategy_deterministic
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.tableStrategy_nonneg
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.sum_table_indicator
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.sum_policyWeight
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.policyWeight_indicator
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.sum_tableWeight
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.tableWeight_nonneg
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.joint_table_mixture
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.expectedUtility_table_mixture
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.exists_deterministic_optimal_all
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.exists_deterministic_optimal
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.signed_weights_exceed_every_action
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.optimalValue_attained
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.expectedUtility_le_optimalValue
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.optimalValue_info_mono
#print axioms InfluenceDiagramsProofs.FinInfluenceDiagram.optimal_information_value_nonneg

open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram

#print axioms smoke

-- Influence-diagram shape, validity, policies
#print axioms closed_iff
#print axioms Closed.of
#print axioms Policy.ofFun
#print axioms Policy.const
#print axioms Policy.const_localOn
#print axioms Strategy.fix_self
#print axioms Strategy.fix_of_ne

-- Proposition 5 — policy instantiation
#print axioms closed_instantiate
#print axioms IDOrder.toTopoOrder
#print axioms local_instantiate
#print axioms normalised_instantiate
#print axioms sum_joint_instantiate_eq_one
#print axioms joint_instantiate

-- Proposition 6 — expected utility
#print axioms expectedUtility_eq
#print axioms expectedUtility_add
#print axioms expectedUtility_smul
#print axioms expectedUtility_eq_sum
#print axioms expectedUtility_const

-- fix_decision = hard intervention
#print axioms strategyKernel_fix_eq_intervene
#print axioms joint_fix
#print axioms expectedUtility_fix

-- Information monotonicity (SPEC §55.7)
#print axioms localOn_mono
#print axioms strategyKernel_enlarge
#print axioms expectedUtility_enlarge
#print axioms exists_strategy_enlarged_eq
