import InfluenceDiagramsProofs.Finite.DVE.Solver

/-!
# No-forgetting generates the strong schedule

The input is an ordinary duplicate-free complete decision list, in reverse chronological
order, satisfying perfect recall. At each decision, all variables outside its information
set and action are summed out, then that action is maximised. The remaining variables are
exactly its information set. No-forgetting proves that the summed block contains only chance
variables and that recursion can continue. The final block contains no actions.

This is the source's first-observation block construction in reverse. The finite enumeration
within a block is arbitrary; numerical correctness does not depend on min-fill.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram

noncomputable section

variable {id : FinInfluenceDiagram}

structure NoForgettingOrder (id : FinInfluenceDiagram) where
  reverseDecisions : List id.D
  nodup : reverseDecisions.Nodup
  complete : ∀ d, d ∈ reverseDecisions
  remembers : reverseDecisions.Pairwise
    (fun later earlier => insert (id.action earlier) (id.info earlier) ⊆ id.info later)

def prependChances (xs : List id.V) (hn : xs.Nodup) {R : Finset id.V}
    (hR : xs.toFinset ⊆ R) (hc : ∀ v ∈ xs, ∀ d, id.action d ≠ v)
    (next : Plan id (R \ xs.toFinset)) : Plan id R := by
  induction xs generalizing R with
  | nil => simpa using next
  | cons v xs ih =>
    have hv : v ∈ R := hR (by simp)
    have htail : xs.toFinset ⊆ R.erase v := by
      intro w hw
      refine Finset.mem_erase.2 ⟨?_, hR (by simp [List.mem_toFinset.1 hw])⟩
      intro he
      exact (List.nodup_cons.1 hn).1 (he ▸ List.mem_toFinset.1 hw)
    have heq : R.erase v \ xs.toFinset = R \ (v :: xs).toFinset := by
      ext w
      by_cases hw : w = v <;> simp [hw]
    apply Plan.chance v hv (hc v (List.mem_cons_self ..))
    exact ih (List.nodup_cons.1 hn).2 htail
      (fun w hw => hc w (List.mem_cons_of_mem v hw)) (by simpa [heq] using next)

/-- Structural construction, with no numerical assumptions or semantic invariant fields. -/
def buildPlan (ds : List id.D)
    (hnf : ds.Pairwise (fun d e => insert (id.action e) (id.info e) ⊆ id.info d))
    (hself : ∀ d, id.action d ∉ id.info d) (R : Finset id.V)
    (ha : ∀ d, id.action d ∈ R ↔ d ∈ ds) (hi : ∀ d ∈ ds, id.info d ⊆ R) :
    Plan id R := by
  induction ds generalizing R with
  | nil =>
    apply prependChances R.toList (Finset.nodup_toList R) (by simp)
    · intro v hv d he
      have h := (ha d).1 (he ▸ Finset.mem_toList.1 hv)
      simp at h
    · simpa using (Plan.done (id := id))
  | cons d ds ih =>
    have hp := List.pairwise_cons.1 hnf
    have hd : id.action d ∈ R := (ha d).2 (List.mem_cons_self ..)
    have hI : id.info d ⊆ R := hi d (List.mem_cons_self ..)
    have hat : ∀ e, id.action e ∈ id.info d ↔ e ∈ ds := by
      intro e
      constructor
      · intro he
        rcases List.mem_cons.1 ((ha e).1 (hI he)) with rfl | ht
        · exact False.elim (hself e he)
        · exact ht
      · intro he
        exact hp.1 e he (Finset.mem_insert_self _ _)
    have hit : ∀ e ∈ ds, id.info e ⊆ id.info d := by
      intro e he v hv
      exact hp.1 e he (Finset.mem_insert_of_mem hv)
    have tail := ih hp.2 (id.info d) hat hit
    let K := insert (id.action d) (id.info d)
    let B := R \ K
    have hK : K ⊆ R := Finset.insert_subset_iff.2 ⟨hd, hI⟩
    have hrem : R \ B = K := by
      ext v
      by_cases hr : v ∈ R <;> by_cases hk : v ∈ K <;> simp_all [B]
    have he : K.erase (id.action d) = id.info d := Finset.erase_insert (hself d)
    have pd : Plan id K := Plan.decision d (Finset.mem_insert_self _ _) he
      (by simpa [he] using tail)
    apply prependChances B.toList (Finset.nodup_toList B)
      (by
        intro v hv
        exact (Finset.mem_sdiff.1 (Finset.mem_toList.1 (List.mem_toFinset.1 hv))).1)
    · intro v hv e hev
      have hvB := Finset.mem_toList.1 hv
      have hvR := (Finset.mem_sdiff.1 hvB).1
      have hnot := (Finset.mem_sdiff.1 hvB).2
      have heR : id.action e ∈ R := hev.symm ▸ hvR
      rcases List.mem_cons.1 ((ha e).1 heR) with rfl | het
      · exact hnot (hev ▸ Finset.mem_insert_self _ _)
      · exact hnot (hev ▸ Finset.mem_insert_of_mem (hat e |>.2 het))
    · simpa [hrem] using pd

def NoForgettingOrder.plan (nf : NoForgettingOrder id) (hself : ∀ d, id.action d ∉ id.info d) :
    Plan id Finset.univ :=
  buildPlan nf.reverseDecisions nf.remembers hself Finset.univ
    (fun d => by simp [nf.complete d]) (fun _ _ => Finset.subset_univ _)

theorem idxOf_lt_of_no_reverse {A : Type} [DecidableEq A] (l : List A) {a b : A}
    (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hp : l.Pairwise (fun x y => x = b → y ≠ a)) : l.idxOf a < l.idxOf b := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    by_cases hac : a = c
    · subst a
      simp [hne]
    · by_cases hbc : b = c
      · subst b
        have hal : a ∈ l := (List.mem_cons.1 ha).resolve_left hac
        exact False.elim ((List.pairwise_cons.1 hp).1 a hal rfl rfl)
      · have hal : a ∈ l := (List.mem_cons.1 ha).resolve_left hac
        have hbl : b ∈ l := (List.mem_cons.1 hb).resolve_left hbc
        simpa [List.idxOf_cons, Ne.symm hac, Ne.symm hbc] using
          ih hal hbl (List.pairwise_cons.1 hp).2

/-- The rank witness is constructed from the existing model's topological order. -/
def RankedOrder.ofOrder (ord : id.IDOrder) : RankedOrder id where
  order := ord
  rank v := ord.order.idxOf v
  parents_lt m v hv := by
    apply idxOf_lt_of_no_reverse ord.order (ord.complete v) (ord.complete (id.target m))
      (fun he => ord.no_self m (he ▸ hv))
    exact ord.parents_before.imp (by
      intro x y h hx hy
      exact h m hx.symm (hy.symm ▸ hv))
  info_lt d v hv := by
    apply idxOf_lt_of_no_reverse ord.order (ord.complete v) (ord.complete (id.action d))
      (fun he => ord.no_self_info d (he ▸ hv))
    exact ord.info_before_action.imp (by
      intro x y h hx hy
      exact h d hx.symm (hy.symm ▸ hv))

/-- The solver obtains its schedule from perfect recall, not from a user-supplied legality
certificate. Choices are local utility argmaxes; no exhaustive strategy search is used. -/
def solve (κ : id.Kernel ℝ) (hloc : ∀ m, Local κ m) (hnonneg : ∀ m x a, 0 ≤ κ m x a)
    (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j)
    (ord : id.IDOrder) (nf : NoForgettingOrder id) : Solution id :=
  solvePlan κ hloc hnonneg u hu (nf.plan ord.no_self_info)

/-- **Finite multi-decision DVE correctness, no evidence.** The generated strong-order bucket
driver returns an admissible deterministic strategy, realizes its reported value, and attains
the existing global optimum over all nonnegative strategies. Zero-probability rows are allowed.
This is exact arithmetic, not an assertion about Float64 tolerance or first-label tie identity. -/
theorem solve_spec (κ : id.Kernel ℝ) (hclosed : id.Closed) (ord : id.IDOrder)
    (nf : NoForgettingOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (hnonneg : ∀ m x a, 0 ≤ κ m x a) (u : Utility id ℝ) (hu : ∀ j, Utility.Local u j) :
    let sol := solve κ hloc hnonneg u hu ord nf
    sol.strategy.Deterministic ∧ expectedUtility κ sol.strategy u = sol.value ∧
      sol.value = optimalValue κ u :=
  solvePlan_spec κ hclosed (RankedOrder.ofOrder ord) hloc hnorm hnonneg u hu _

end
end InfluenceDiagramsProofs.DVE
