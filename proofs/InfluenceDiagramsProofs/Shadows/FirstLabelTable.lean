import InfluenceDiagramsProofs.Finite.DVE.Selector

/-!
# SA-Pass shadow module: first-label policy tables are unique and semantic on reachable rows

Claim `id.first-label-table`, from `DVE.solveOrdered_table` and `DVE.solveOrdered_semantic`:
"`solveOrdered_table` proves that every policy row, reachable or not, is the least action
maximizing that row's bucket utility, so the returned table is uniquely determined, and
`solveOrdered_semantic` proves that on every row of positive probability it is the least action
maximizing the (unnormalized) expected utility of acting there and then following the returned
later policies."

"That row's bucket utility" is `solveScore`, the bucket utility row recorded when the decision is
eliminated. The semantic score is `continuation`, with the returned strategy as the later
policies, and "positive probability" is `reach`, both with weight one (no evidence).
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.Shadows.FirstLabelTable

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet
open InfluenceDiagramsProofs InfluenceDiagramsProofs.FinInfluenceDiagram InfluenceDiagramsProofs.DVE

/-- `solveOrdered_table` and `solveOrdered_semantic`, restated abstractly with every hypothesis. -/
abbrev Candidate : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder) (nf : NoForgettingOrder id)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j),
    (∀ (d : id.D) (x : id.Assignment) (a : id.states (id.action d)),
      ((solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d).kernel x a =
        if a = orderedTable (solveScore κ hloc hnonneg u hu ord nf d) (infoAssignment d x)
        then 1 else 0) ∧
    (∀ (d : id.D) (x : id.Assignment),
      reach κ (fun _ => 1) (solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy
        d x ≠ 0 → ∀ a : id.states (id.action d),
      ((solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d).kernel x a =
        if a = firstArgmax (continuation κ u (fun _ => 1)
          (solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d x)
        then 1 else 0)

/-- "every policy row, reachable or not, is ... maximizing that row's bucket utility": on every
row the returned policy puts all weight on one action, which maximizes the row's score. -/
abbrev Shadow1 : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder) (nf : NoForgettingOrder id)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (d : id.D) (x : id.Assignment),
    ∃ c : id.states (id.action d),
      (∀ a, ((solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d).kernel x a =
        if a = c then 1 else 0) ∧
      ∀ b, solveScore κ hloc hnonneg u hu ord nf d x b ≤ solveScore κ hloc hnonneg u hu ord nf d x c

/-- "the least action", "so the returned table is uniquely determined": the chosen action
precedes every maximizer in the supplied order. -/
abbrev Shadow2 : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder) (nf : NoForgettingOrder id)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (d : id.D) (x : id.Assignment)
      (c b : id.states (id.action d)),
    ((solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d).kernel x c = 1 →
    (∀ b', solveScore κ hloc hnonneg u hu ord nf d x b' ≤ solveScore κ hloc hnonneg u hu ord nf d x b) →
    c ≤ b

/-- "on every row of positive probability it is the least action maximizing the (unnormalized)
expected utility of acting there and then following the returned later policies". -/
abbrev Shadow3 : Prop :=
  ∀ (id : FinInfluenceDiagram) [∀ d : id.D, LinearOrder (id.states (id.action d))]
      (κ : id.Kernel ℝ) (_hclosed : id.Closed) (ord : id.IDOrder) (nf : NoForgettingOrder id)
      (hloc : ∀ m, Local κ m) (_hnorm : ∀ m, Normalised κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
      (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) (d : id.D) (x : id.Assignment),
    0 < reach κ (fun _ => 1) (solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy
      d x → ∀ a : id.states (id.action d),
      ((solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d).kernel x a =
        if a = firstArgmax (continuation κ u (fun _ => 1)
          (solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d x)
        then 1 else 0

theorem forward1 : Candidate → Shadow1 := by
  intro h id _ κ hc ord nf hloc hnorm hnonneg u hu d x
  refine ⟨orderedTable (solveScore κ hloc hnonneg u hu ord nf d) (infoAssignment d x),
    fun a => (h id κ hc ord nf hloc hnorm hnonneg u hu).1 d x a, fun b => ?_⟩
  rw [orderedTable_reconstruct _ (solveScore_local κ hc hloc hnonneg u hu ord nf d)]
  exact firstArgmax_maximizes _ b

theorem forward2 : Candidate → Shadow2 := by
  intro h id _ κ hc ord nf hloc hnorm hnonneg u hu d x c b hc1 hb
  have ht := (h id κ hc ord nf hloc hnorm hnonneg u hu).1 d x c
  rw [hc1] at ht
  have hct : c = orderedTable (solveScore κ hloc hnonneg u hu ord nf d) (infoAssignment d x) := by
    by_contra hne
    rw [if_neg hne] at ht
    exact one_ne_zero ht
  rw [hct, orderedTable_reconstruct _ (solveScore_local κ hc hloc hnonneg u hu ord nf d)]
  exact firstArgmax_first _ b hb

theorem forward3 : Candidate → Shadow3 := by
  intro h id _ κ hc ord nf hloc hnorm hnonneg u hu d x hx
  exact (h id κ hc ord nf hloc hnorm hnonneg u hu).2 d x (ne_of_gt hx)

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := by
  intro h1 h2 h3 id _ κ hc ord nf hloc hnorm hnonneg u hu
  refine ⟨fun d x a => ?_, fun d x hx a => ?_⟩
  · obtain ⟨c, hk, hmax⟩ := h1 id κ hc ord nf hloc hnorm hnonneg u hu d x
    have hc1 : ((solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy d).kernel
        x c = 1 := by
      rw [hk]
      simp
    have hle : c ≤ firstArgmax (solveScore κ hloc hnonneg u hu ord nf d x) :=
      h2 id κ hc ord nf hloc hnorm hnonneg u hu d x c _ hc1 (fun b => firstArgmax_maximizes _ b)
    have hge : firstArgmax (solveScore κ hloc hnonneg u hu ord nf d x) ≤ c :=
      firstArgmax_first _ c hmax
    rw [hk, orderedTable_reconstruct _ (solveScore_local κ hc hloc hnonneg u hu ord nf d),
      le_antisymm hle hge]
  · have hσ : (solveWith (Selector.ordered id) κ hloc hnonneg u hu ord nf).strategy.Nonneg :=
      deterministic_nonneg _ (runWith_deterministic (Selector.ordered id)
        (nf.plan ord.no_self_info) (initial κ hloc hnonneg u hu) defaultStrategy
        defaultStrategy_deterministic)
    have hpos := lt_of_le_of_ne
      (reach_nonneg κ hnonneg (fun _ => 1) (fun _ => zero_le_one) _ hσ d x) (Ne.symm hx)
    exact h3 id κ hc ord nf hloc hnorm hnonneg u hu d x hpos a

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate := by
  intro id _ κ hc ord nf hloc hnorm hnonneg u hu
  exact ⟨fun d x a => InfluenceDiagramsProofs.DVE.solveOrdered_table κ hc hloc hnonneg u hu
      ord nf d x a,
    fun d x hx a => InfluenceDiagramsProofs.DVE.solveOrdered_semantic κ hc ord nf hloc hnorm
      hnonneg u hu d x hx a⟩

end InfluenceDiagramsProofs.Shadows.FirstLabelTable
