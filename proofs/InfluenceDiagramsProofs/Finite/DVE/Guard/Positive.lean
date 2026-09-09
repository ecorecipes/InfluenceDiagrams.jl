import InfluenceDiagramsProofs.Finite.DVE.Evidence

/-!
# The exact all-row guard and its positive-input intermediate lemma

`ExactGuard` is equality on every assignment and every action, not merely reachable rows.
The checked driver uses the source-style maximum of row maximum-minus-minimum, proved
equivalent to `ExactGuard` at exact zero tolerance. Strict positivity is used only in an intermediate
cancellation argument; the final completeness theorem will remove it by continuous
probability-expression provenance and normalized positive smoothing.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram Valuation

noncomputable section

variable {id : FinInfluenceDiagram}

def ExactGuard (a : id.V) (vs : List (Valuation id.toFinBayesNet)) : Prop :=
  ∀ x b, (collect (bucket a vs)).prob (Function.update x a b) = (collect (bucket a vs)).prob x

def spread {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) : ℝ :=
  f (argmax f) - f (argmax fun a => -f a)

theorem spread_nonneg {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) : 0 ≤ spread f :=
  sub_nonneg.mpr (le_argmax f _)

theorem spread_zero_iff {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) :
    spread f = 0 ↔ ∀ a b, f a = f b := by
  constructor
  · intro h a b
    have he : f (argmax f) = f (argmax fun a => -f a) := sub_eq_zero.mp h
    have hlo (c : A) : f (argmax fun a => -f a) ≤ f c :=
      neg_le_neg_iff.mp (le_argmax (fun a => -f a) c)
    exact le_antisymm ((le_argmax f a).trans (he ▸ hlo b))
      ((le_argmax f b).trans (he ▸ hlo a))
  · intro h
    exact sub_eq_zero.mpr (h _ _)

def rowSpread (a : id.V) (vs : List (Valuation id.toFinBayesNet)) (x : id.Assignment) : ℝ :=
  spread fun b => (collect (bucket a vs)).prob (Function.update x a b)

def diagnosticSpread (a : id.V) (vs : List (Valuation id.toFinBayesNet)) : ℝ :=
  rowSpread a vs (argmax (rowSpread a vs))

/-- This is exactly the source diagnostic at atol=0: reject iff some row has positive
maximum-minus-minimum. No reachability restriction is hidden in the equivalence. -/
theorem exactGuard_iff_diagnostic (a : id.V) (vs : List (Valuation id.toFinBayesNet)) :
    ExactGuard a vs ↔ diagnosticSpread a vs ≤ 0 := by
  have hrow : ExactGuard a vs ↔ ∀ x, rowSpread a vs x = 0 := by
    constructor
    · intro h x
      apply (spread_zero_iff _).2
      intro b c
      exact (h x b).trans (h x c).symm
    · intro h x b
      have he := (spread_zero_iff _).1 (h x) b (x a)
      simpa only [Function.update_eq_self] using he
  rw [hrow]
  constructor
  · intro h
    exact le_of_eq (h _)
  · intro h x
    exact le_antisymm ((le_argmax (rowSpread a vs) x).trans h) (spread_nonneg _)

def AllGuards {R : Finset id.V} (plan : Plan id R)
    (vs : List (Valuation id.toFinBayesNet)) : Prop :=
  match plan with
  | .done => True
  | .chance v _ _ next => AllGuards next (chanceStep v vs)
  | .decision d _ _ next =>
    ExactGuard (id.action d) vs ∧ AllGuards next (decisionStep (id.action d) vs)

def checkedRun {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ) :
    Option (State id ∅ × Strategy id ℝ) := by
  classical
  exact match plan with
  | .done => some (s, σ)
  | .chance v _ _ next => checkedRun next (s.chance v) σ
  | .decision d _ hi next =>
    if 0 < diagnosticSpread (id.action d) s.valuations then none
    else checkedRun next (s.decision d) (Function.update σ d (s.policy d hi))

theorem checkedRun_eq_run {R : Finset id.V} (plan : Plan id R) (s : State id R)
    (σ : Strategy id ℝ) (h : AllGuards plan s.valuations) :
    checkedRun plan s σ = some (run plan s σ) := by
  classical
  induction plan generalizing σ with
  | done => rfl
  | chance v _ _ next ih => exact ih (s.chance v) σ h
  | decision d _ hi next ih =>
    change (if 0 < diagnosticSpread (id.action d) s.valuations then none else _) = _
    rw [if_neg (not_lt.mpr ((exactGuard_iff_diagnostic _ _).1 h.1))]
    exact ih (s.decision d) _ h.2

def Positive {bn : FinBayesNet} (vs : List (Valuation bn)) : Prop :=
  ∀ v ∈ vs, ∀ x, 0 < v.prob x

theorem Positive.filter {bn : FinBayesNet} {vs : List (Valuation bn)} (h : Positive vs)
    (p : Valuation bn → Bool) : Positive (vs.filter p) :=
  fun v hv => h v (List.mem_of_mem_filter hv)

theorem Positive.collect {bn : FinBayesNet} {vs : List (Valuation bn)}
    (h : Positive vs) (x : bn.Assignment) : 0 < (Valuation.collect vs).prob x := by
  induction vs with
  | nil => exact zero_lt_one
  | cons v vs ih =>
    exact mul_pos (h v (List.mem_cons_self ..) x)
      (ih (fun w hw => h w (List.mem_cons_of_mem v hw)))

theorem Positive.chanceStep {bn : FinBayesNet} {vs : List (Valuation bn)}
    (h : Positive vs) (a : bn.V) : Positive (chanceStep a vs) := by
  intro v hv x
  rcases List.mem_cons.1 hv with rfl | hv
  · change 0 < ∑ b, (Valuation.collect (bucket a vs)).prob (Function.update x a b)
    exact Finset.sum_pos (fun b _ => (h.filter _).collect _) Finset.univ_nonempty
  · exact h v (List.mem_of_mem_filter hv) x

theorem Positive.decisionStep {bn : FinBayesNet} {vs : List (Valuation bn)}
    (h : Positive vs) (a : bn.V) : Positive (decisionStep a vs) := by
  intro v hv x
  rcases List.mem_cons.1 hv with rfl | hv
  · exact (h.filter _).collect _
  · exact h v (List.mem_of_mem_filter hv) x

theorem initial_positive (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (hp : ∀ m x a, 0 < κ m x a) :
    Positive (initial κ hloc hnonneg u hu).valuations := by
  intro v hv x
  rcases List.mem_append.1 hv with hv | hv
  · obtain ⟨m, _, rfl⟩ := List.mem_map.1 hv
    exact hp m x _
  · obtain ⟨j, _, rfl⟩ := List.mem_map.1 hv
    exact zero_lt_one

theorem initialEvidence_positive (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (e : Evidence id) (hp : ∀ m x a, 0 < κ m x a) (he : ∀ x, 0 < e.likelihood x) :
    Positive (initialEvidence κ hloc hnonneg u hu e).valuations := by
  intro v hv x
  rcases List.mem_cons.1 hv with rfl | hv
  · exact he x
  · exact initial_positive κ hloc hnonneg u hu hp v hv x

/-- Intermediate result only: positive probabilities make every outside product cancellable.
Its structural independence premise is derived from the existing causal/normalization theorem. -/
theorem guards_of_positive {κ : id.Kernel ℝ} {u : Utility id ℝ}
    (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ)
    (hc : Correct κ u s σ) (hp : Positive s.valuations) :
    AllGuards plan s.valuations := by
  induction plan generalizing σ with
  | done => trivial
  | chance v hv hchance next ih =>
    exact ih (s.chance v) σ (hc.chance v hv hchance) (hp.chanceStep v)
  | @decision R d hd hi next ih =>
    have hg : ∀ x a, (collect s.valuations).prob (Function.update x (id.action d) a) =
        (collect s.valuations).prob x := by
      intro x a
      rw [hc.mass, hc.mass]
      exact probability_independent κ hclosed (RankedOrder.ofOrder ord) hloc hnorm Rᶜ σ d
        (by simpa using hd) (by simpa using information_boundary d hi) x a
    constructor
    · intro x a
      exact bucket_probability_constant_on_support _ _ hg x (ne_of_gt ((hp.filter _).collect x)) a
    · exact ih (s.decision d) _ (hc.decision hclosed (RankedOrder.ofOrder ord) hloc hnorm d hd hi)
        (hp.decisionStep _)

theorem guards_of_positive_weighted {κ : id.Kernel ℝ} {u : Utility id ℝ} {e : Evidence id}
    (hclosed : id.Closed) (ord : id.IDOrder)
    (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    {R : Finset id.V} (plan : Plan id R) (s : State id R) (σ : Strategy id ℝ)
    (hc : WeightedCorrect κ u e s σ) (hp : Positive s.valuations) :
    AllGuards plan s.valuations := by
  induction plan generalizing σ with
  | done => trivial
  | chance v hv hchance next ih =>
    exact ih (s.chance v) σ (hc.chance v hv hchance) (hp.chanceStep v)
  | @decision R d hd hi next ih =>
    have hg : ∀ x a, (collect s.valuations).prob (Function.update x (id.action d) a) =
        (collect s.valuations).prob x := by
      intro x a
      rw [hc.mass, hc.mass]
      exact e.probability_independent κ hclosed ord hloc hnorm Rᶜ σ d
        (by simpa using hd) (by simpa using information_boundary d hi) x a
    constructor
    · intro x a
      exact bucket_probability_constant_on_support _ _ hg x (ne_of_gt ((hp.filter _).collect x)) a
    · exact ih (s.decision d) _ (hc.decision hclosed ord hloc hnorm d hd hi) (hp.decisionStep _)

end
end InfluenceDiagramsProofs.DVE
