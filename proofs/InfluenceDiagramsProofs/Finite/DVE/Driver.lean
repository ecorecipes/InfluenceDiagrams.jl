import InfluenceDiagramsProofs.Finite.DVE.Semantics

/-!
# Bucket driver and policy reconstruction

`Plan` contains only variable identities and information-set equalities. In particular it
contains no probability independence, value bound, solver correctness, or oracle premise.
`run` executes bucket chance elimination and local utility maximisation, recording each
chosen policy. The semantic invariant is proved by induction; decision probability independence
is obtained from the structural theorem in `Semantics.lean`, not from the plan.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram
open Valuation

noncomputable section

variable {id : FinInfluenceDiagram}

inductive Plan (id : FinInfluenceDiagram) : Finset id.V → Type
  | done : Plan id ∅
  | chance {R} (v : id.V) (hv : v ∈ R) (chance : ∀ d, id.action d ≠ v)
      (next : Plan id (R.erase v)) : Plan id R
  | decision {R} (d : id.D) (hd : id.action d ∈ R)
      (information : R.erase (id.action d) = id.info d)
      (next : Plan id (R.erase (id.action d))) : Plan id R

structure State (id : FinInfluenceDiagram) (R : Finset id.V) where
  valuations : List (Valuation id.toFinBayesNet)
  supported : (collect valuations).scope ⊆ R

namespace State

variable {R : Finset id.V}

def chance (v : id.V) (s : State id R) : State id (R.erase v) where
  valuations := chanceStep v s.valuations
  supported := (step_scope v s.valuations (sumOut v) (fun _ => rfl)).trans
    (Finset.erase_subset_erase v s.supported)

def decision (d : id.D) (s : State id R) : State id (R.erase (id.action d)) where
  valuations := decisionStep (id.action d) s.valuations
  supported := (step_scope (id.action d) s.valuations (maxOut (id.action d)) (fun _ => rfl)).trans
    (Finset.erase_subset_erase _ s.supported)

def policy (d : id.D) (s : State id R) (hi : R.erase (id.action d) = id.info d) :
    Policy id ℝ d :=
  Policy.ofFun (choice (id.action d) (collect (bucket (id.action d) s.valuations))) (by
    intro x y h
    apply choice_local
    intro v hv
    apply h
    rw [← hi]
    exact Finset.erase_subset_erase _ ((filter_scope_subset _ s.valuations).trans s.supported) hv)

end State

/-- The actual solver: local bucket updates, not enumeration or argmax over strategies. -/
def run {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ) :
    State id ∅ × Strategy id ℝ :=
  match plan with
  | .done => (s, σ)
  | .chance v _ _ next => run next (s.chance v) σ
  | .decision d _ hi next => run next (s.decision d) (Function.update σ d (s.policy d hi))

/-- Exact mass and payoff realization, together with the upper bound for every competitor.
This is an invariant to prove, not data required by `Plan` or `run`. -/
structure Correct (κ : id.Kernel ℝ) (u : Utility id ℝ) {R : Finset id.V}
    (s : State id R) (σ : Strategy id ℝ) : Prop where
  mass : ∀ x, (collect s.valuations).prob x = marg Rᶜ (freeJoint κ Rᶜ σ) x
  realizes : ∀ x, (collect s.valuations).weight x =
    marg Rᶜ (fun y => freeJoint κ Rᶜ σ y * totalUtility u y) x
  dominates : ∀ τ : Strategy id ℝ, τ.Nonneg → ∀ x,
    marg Rᶜ (fun y => freeJoint κ Rᶜ τ y * totalUtility u y) x ≤
      (collect s.valuations).weight x

theorem compl_erase (R : Finset id.V) (v : id.V) :
    (R.erase v)ᶜ = insert v Rᶜ := by
  ext w
  by_cases h : w = v <;> simp [h]

theorem Correct.chance {κ : id.Kernel ℝ} {u : Utility id ℝ} {R : Finset id.V}
    {s : State id R} {σ : Strategy id ℝ} (h : Correct κ u s σ)
    (v : id.V) (hv : v ∈ R) (hc : ∀ d, id.action d ≠ v) :
    Correct κ u (s.chance v) σ := by
  have hn : v ∉ Rᶜ := by simpa using hv
  constructor
  · intro x
    change (collect (chanceStep v s.valuations)).prob x = _
    rw [chanceStep_prob, compl_erase, freeJoint_insert_chance κ Rᶜ σ v hc, marg_insert hn]
    exact Finset.sum_congr rfl fun b _ => h.mass _
  · intro x
    change (collect (chanceStep v s.valuations)).weight x = _
    rw [chanceStep_weight, compl_erase, freeJoint_insert_chance κ Rᶜ σ v hc, marg_insert hn]
    exact Finset.sum_congr rfl fun b _ => h.realizes _
  · intro τ hτ x
    change _ ≤ (collect (chanceStep v s.valuations)).weight x
    rw [chanceStep_weight, compl_erase, freeJoint_insert_chance κ Rᶜ τ v hc, marg_insert hn]
    exact Finset.sum_le_sum fun b _ => h.dominates τ hτ _

theorem info_disjoint {R : Finset id.V} (d : id.D)
    (hi : R.erase (id.action d) = id.info d) :
    ∀ v ∈ id.info d, v ∉ insert (id.action d) Rᶜ := by
  intro v hv
  rw [← hi, Finset.mem_erase] at hv
  simp [hv.1, hv.2]

theorem information_boundary {R : Finset id.V} (d : id.D)
    (hi : R.erase (id.action d) = id.info d) :
    R ⊆ insert (id.action d) (id.info d) := by
  intro v hv
  by_cases he : v = id.action d
  · exact Finset.mem_insert.2 (Or.inl he)
  · exact Finset.mem_insert.2 (Or.inr (hi ▸ Finset.mem_erase.2 ⟨he, hv⟩))

theorem Correct.decision {κ : id.Kernel ℝ} {u : Utility id ℝ} {R : Finset id.V}
    {s : State id R} {σ : Strategy id ℝ} (h : Correct κ u s σ)
    (hclosed : id.Closed) (ord : RankedOrder id)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (d : id.D) (hd : id.action d ∈ R) (hi : R.erase (id.action d) = id.info d) :
    Correct κ u (s.decision d) (Function.update σ d (s.policy d hi)) := by
  have hn : id.action d ∉ Rᶜ := by simpa using hd
  have hinj := (id.closed_iff.1 hclosed).2.1
  have hinfo := info_disjoint d hi
  let f := choice (id.action d) (collect (bucket (id.action d) s.valuations))
  have hpi : ∀ x a, (s.policy d hi).kernel x a = if a = f x then 1 else 0 := by
    intro x a
    rfl
  have heval : ∀ (F : id.Assignment → ℝ) (x : id.Assignment),
      marg (insert (id.action d) Rᶜ)
      (fun y => freeJoint κ (insert (id.action d) Rᶜ)
        (Function.update σ d (s.policy d hi)) y * F y) x =
      marg Rᶜ (fun y => freeJoint κ Rᶜ σ y * F y) (Function.update x (id.action d) (f x)) := by
    intro F x
    rw [decision_marginal κ Rᶜ σ hinj d hn hinfo]
    simp [hpi, ite_mul]
  have hp : ∀ x a, (collect s.valuations).prob (Function.update x (id.action d) a) =
      (collect s.valuations).prob x := by
    intro x a
    rw [h.mass, h.mass]
    exact probability_independent κ hclosed ord hloc hnorm Rᶜ σ d hn
      (by simpa using information_boundary d hi) x a
  constructor
  · intro x
    change (collect (decisionStep (id.action d) s.valuations)).prob x = _
    rw [(decisionStep_eval _ _ hp x).1, h.mass, compl_erase]
    simpa using (heval (fun _ => 1) x).symm
  · intro x
    change (collect (decisionStep (id.action d) s.valuations)).weight x = _
    rw [weight, (decisionStep_eval _ _ hp x).1, (decisionStep_eval _ _ hp x).2]
    change (collect s.valuations).weight (Function.update x (id.action d) (f x)) = _
    rw [h.realizes, compl_erase, heval]
  · intro τ hτ x
    change _ ≤ (collect (decisionStep (id.action d) s.valuations)).weight x
    rw [compl_erase]
    have hc := decision_marginal κ Rᶜ τ hinj d hn hinfo (τ d) (totalUtility u) x
    simp only [Function.update_eq_self] at hc
    rw [hc]
    calc
      _ ≤ ∑ a, (τ d).kernel x a * (collect (decisionStep (id.action d) s.valuations)).weight x :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          ((h.dominates τ hτ _).trans (decisionStep_dominates _ _ hp x a)) (hτ d x a)
      _ = _ := by rw [← Finset.sum_mul, (τ d).normalised x, one_mul]

/-- The structural/order/normalisation assumptions establish the invariant throughout the
actual recursive bucket driver. In particular, no semantic invariant is assumed by the run. -/
theorem run_correct {κ : id.Kernel ℝ} {u : Utility id ℝ} (hclosed : id.Closed)
    (ord : RankedOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ)
    (h : Correct κ u s σ) :
    Correct κ u (run plan s σ).1 (run plan s σ).2 := by
  induction plan generalizing σ with
  | done => exact h
  | chance v hv hc next ih => exact ih (s.chance v) σ (h.chance v hv hc)
  | decision d hd hi next ih =>
    exact ih (s.decision d) _ (h.decision hclosed ord hloc hnorm d hd hi)

end
end InfluenceDiagramsProofs.DVE
