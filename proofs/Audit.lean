/-
Axiom audit: `lake env lean Audit.lean` (or `make audit`). Every theorem below must report at
most `propext`, `Classical.choice` and `Quot.sound`. `InfluenceDiagramsProofs.Roadmap` (which
contains `sorry`) is intentionally not imported here.
-/
import InfluenceDiagramsProofs

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
