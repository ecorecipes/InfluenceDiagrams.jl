import InfluenceDiagramsProofs.Finite.Instantiate
import BayesianNetworksProofs.Finite.Intervention

/-!
# InfluenceDiagramsProofs.Finite.ExpectedUtility

**Proposition 6 (expected utility)** for the concrete finite model (SPEC §29–§31, §41, §61).

Utilities are deterministic functionals `u j : Assignment → R`, one per utility node, each
reading only its scope (`Utility.Local`); the first implementation aggregates additively,
`totalUtility u x = ∑ j, u j x` (SPEC §30). The expected utility of a strategy is the expectation
of the total utility under the law `P_σ` of the instantiated network (SPEC §31):

`expectedUtility κ σ u = ∑ x, joint (strategyKernel κ σ) x * totalUtility u x`.

* `expectedUtility_add`, `expectedUtility_smul` — `EU` is linear in the utility;
* `expectedUtility_eq_sum` — additive decomposition: `EU = ∑ j, ∑ x, P_σ(x) * u j x`;
* `expectedUtility_const` — a constant total utility `c` has expected utility `c`
  (Proposition 5's normalisation);
* `fix_decision`: `strategyKernel_fix_eq_intervene` — fixing decision `d` to `a` in the strategy
  is the hard intervention `do(action d = a)` on the instantiated network (Proposition 4 of the
  BN project), so `joint_fix` gives the truncated factorisation and `expectedUtility_fix` the
  expected utility of a fixed decision.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet

namespace FinInfluenceDiagram

variable {id : FinInfluenceDiagram} {R : Type}

/-! ## Utilities -/

/-- A family of utility functionals, one per utility node (`utility_ref` in the ACSet). -/
abbrev Utility (id : FinInfluenceDiagram) (R : Type) := id.U → id.Assignment → R

/-- `u j` depends on the assignment only through the scope of `j` (its `UtilityInput` rows). -/
def Utility.Local (u : Utility id R) (j : id.U) : Prop :=
  ∀ x x' : id.Assignment, (∀ p ∈ id.uscope j, x p = x' p) → u j x = u j x'

variable [CommSemiring R]

/-- Additive aggregation `U(x) = ∑ j, u j (x_{scope j})` (SPEC §30). -/
def totalUtility (u : Utility id R) (x : id.Assignment) : R := ∑ j, u j x

/-- Expected utility of a strategy: `EU(σ) = ∑ x, P_σ(x) U(x)` (SPEC §31; the Julia
`expected_utility(id, strategy)` reference algorithm). -/
def expectedUtility (κ : id.Kernel R) (σ : Strategy id R) (u : Utility id R) : R :=
  ∑ x, joint (strategyKernel κ σ) x * totalUtility u x

/-- **Proposition 6.** `EU(σ) = E_{P_σ}[U]`: the expectation of the total utility under the
instantiated joint, written out via `joint_instantiate`. -/
theorem expectedUtility_eq (κ : id.Kernel R) (σ : Strategy id R) (u : Utility id R) :
    expectedUtility κ σ u =
      ∑ x, ((∏ m, κ m x (x (id.target m))) * ∏ d, (σ d).kernel x (x (id.action d))) *
        ∑ j, u j x := by
  unfold expectedUtility totalUtility
  exact Finset.sum_congr rfl fun x _ => by rw [joint_instantiate]

/-! ### Linearity -/

theorem totalUtility_add (u₁ u₂ : Utility id R) (x : id.Assignment) :
    totalUtility (u₁ + u₂) x = totalUtility u₁ x + totalUtility u₂ x := by
  simp [totalUtility, Finset.sum_add_distrib]

theorem totalUtility_smul (c : R) (u : Utility id R) (x : id.Assignment) :
    totalUtility (fun j y => c * u j y) x = c * totalUtility u x := by
  simp [totalUtility, Finset.mul_sum]

/-- Expected utility is additive in the utility. -/
theorem expectedUtility_add (κ : id.Kernel R) (σ : Strategy id R) (u₁ u₂ : Utility id R) :
    expectedUtility κ σ (u₁ + u₂) = expectedUtility κ σ u₁ + expectedUtility κ σ u₂ := by
  unfold expectedUtility
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by rw [totalUtility_add, mul_add]

/-- Expected utility is homogeneous in the utility. -/
theorem expectedUtility_smul (κ : id.Kernel R) (σ : Strategy id R) (c : R) (u : Utility id R) :
    expectedUtility κ σ (fun j y => c * u j y) = c * expectedUtility κ σ u := by
  unfold expectedUtility
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [totalUtility_smul, mul_left_comm]

/-- Additive decomposition: the expected utility is the sum of the expected utilities of the
individual utility nodes (SPEC §30–§31). -/
theorem expectedUtility_eq_sum (κ : id.Kernel R) (σ : Strategy id R) (u : Utility id R) :
    expectedUtility κ σ u = ∑ j, ∑ x, joint (strategyKernel κ σ) x * u j x := by
  unfold expectedUtility totalUtility
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _

/-- A utility whose total is the constant `c` has expected utility `c` (uses Proposition 5:
the instantiated joint sums to one). -/
theorem expectedUtility_const (κ : id.Kernel R) (σ : Strategy id R) (hclosed : id.Closed)
    (ord : id.IDOrder) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (u : Utility id R) (c : R) (hu : ∀ x, totalUtility u x = c) :
    expectedUtility κ σ u = c := by
  unfold expectedUtility
  simp_rw [hu]
  rw [← Finset.sum_mul, sum_joint_instantiate_eq_one κ σ hclosed ord hloc hnorm, one_mul]

/-! ## Fixing a decision -/

/-- **`fix_decision` is a hard intervention.** Replacing the policy of `d` by the constant policy
at `a` gives exactly the kernel family `do(action d = a)` of the instantiated network
(`intervene` of the BN project on the mechanism `inr d`). -/
theorem strategyKernel_fix_eq_intervene (κ : id.Kernel R) (σ : Strategy id R) (d : id.D)
    (a : id.states (id.action d)) :
    strategyKernel κ (σ.fix d a) = intervene (strategyKernel κ σ) (.inr d) a := by
  funext m
  cases m with
  | inl m =>
    rw [intervene_of_ne _ Sum.inl_ne_inr]
    rfl
  | inr d' =>
    by_cases h : d' = d
    · subst h
      funext x y
      show (σ.fix d' a d').kernel x y = _
      rw [Strategy.fix_self, Policy.const_kernel, intervene_self]
      rfl
    · rw [intervene_of_ne _ (fun h' => h (Sum.inr_injective h'))]
      show (σ.fix d a d').kernel = (σ d').kernel
      rw [Strategy.fix_of_ne σ h]

/-- The joint under a fixed decision: the truncated factorisation of Proposition 4. -/
theorem joint_fix (κ : id.Kernel R) (σ : Strategy id R) (d : id.D) (a : id.states (id.action d))
    (x : id.Assignment) :
    joint (strategyKernel κ (σ.fix d a)) x =
      (if x (id.action d) = a then 1 else 0) *
        ∏ m ∈ Finset.univ.erase (Sum.inr d), strategyKernel κ σ m x (x (id.instantiate.target m)) := by
  rw [strategyKernel_fix_eq_intervene]
  exact joint_intervene (strategyKernel κ σ) (.inr d) a x

/-- Expected utility of a fixed decision, via the truncated factorisation. -/
theorem expectedUtility_fix (κ : id.Kernel R) (σ : Strategy id R) (d : id.D)
    (a : id.states (id.action d)) (u : Utility id R) :
    expectedUtility κ (σ.fix d a) u =
      ∑ x, (if x (id.action d) = a then 1 else 0) *
        (∏ m ∈ Finset.univ.erase (Sum.inr d), strategyKernel κ σ m x (x (id.instantiate.target m))) *
          totalUtility u x := by
  unfold expectedUtility
  exact Finset.sum_congr rfl fun x _ => by rw [joint_fix]

end FinInfluenceDiagram

end InfluenceDiagramsProofs
