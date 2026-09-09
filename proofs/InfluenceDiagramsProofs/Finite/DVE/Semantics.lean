import InfluenceDiagramsProofs.Finite.DVE.Valuation

/-!
# Structural probability independence

Uneliminated decisions are free inputs: their factors are one, not probability distributions.
Eliminated decisions carry the reconstructed, local normalised policies. The decisive theorem
below derives action-independence of a remaining probability marginal from acyclicity,
generative uniqueness, normalisation and the strong-order information boundary.
It does not take a semantic legality certificate or solver/oracle equality as a premise.
-/

set_option autoImplicit false

namespace InfluenceDiagramsProofs.DVE

open BayesianNetworksProofs BayesianNetworksProofs.FinBayesNet FinInfluenceDiagram

noncomputable section

variable {id : FinInfluenceDiagram}

/-- Numeric topological ranks for the causal and information arcs. -/
structure RankedOrder (id : FinInfluenceDiagram) where
  order : id.IDOrder
  rank : id.V → ℕ
  parents_lt : ∀ m v, v ∈ id.parents m → rank v < rank (id.target m)
  info_lt : ∀ d v, v ∈ id.info d → rank v < rank (id.action d)

def freeJoint (κ : id.Kernel ℝ) (E : Finset id.V) (σ : Strategy id ℝ)
    (x : id.Assignment) : ℝ :=
  (∏ m, κ m x (x (id.target m))) *
    ∏ d, if id.action d ∈ E then (σ d).kernel x (x (id.action d)) else 1

def activeKernel (κ : id.Kernel ℝ) (E : Finset id.V) (σ : Strategy id ℝ) :
    id.instantiate.Kernel ℝ
  | .inl m => κ m
  | .inr d => if id.action d ∈ E then (σ d).kernel else fun _ _ => 1

theorem joint_active (κ : id.Kernel ℝ) (E : Finset id.V) (σ : Strategy id ℝ) :
    joint (activeKernel κ E σ) = freeJoint κ E σ := by
  funext x
  unfold joint freeJoint
  rw [Fintype.prod_sum_type]
  congr 1
  apply Finset.prod_congr rfl
  intro d _
  by_cases h : id.action d ∈ E <;> simp [activeKernel, h, instantiate]

theorem active_local (κ : id.Kernel ℝ) (hκ : ∀ m, Local κ m)
    (E : Finset id.V) (σ : Strategy id ℝ) : ∀ m, Local (activeKernel κ E σ) m := by
  rintro (m | d)
  · exact hκ m
  · by_cases h : id.action d ∈ E
    · exact (show Local (activeKernel κ E σ) (.inr d) from by
        simpa [Local, activeKernel, h, instantiate] using (σ d).localOn)
    · intro x y _
      simp [activeKernel, h]

theorem freeJoint_empty (κ : id.Kernel ℝ) (σ : Strategy id ℝ) (x : id.Assignment) :
    freeJoint κ ∅ σ x = ∏ m, κ m x (x (id.target m)) := by simp [freeJoint]

theorem freeJoint_univ (κ : id.Kernel ℝ) (σ : Strategy id ℝ) :
    freeJoint κ Finset.univ σ = joint (strategyKernel κ σ) := by
  funext x
  rw [joint_instantiate]
  simp [freeJoint]

theorem freeJoint_insert_chance (κ : id.Kernel ℝ) (E : Finset id.V) (σ : Strategy id ℝ)
    (v : id.V) (hv : ∀ d, id.action d ≠ v) :
    freeJoint κ (insert v E) σ = freeJoint κ E σ := by
  funext x
  simp [freeJoint, hv]

theorem freeJoint_activate (κ : id.Kernel ℝ) (E : Finset id.V) (σ : Strategy id ℝ)
    (hinj : Function.Injective id.action) (d : id.D) (hd : id.action d ∉ E)
    (π : Policy id ℝ d) (x : id.Assignment) :
    freeJoint κ (insert (id.action d) E) (Function.update σ d π) x =
      freeJoint κ E σ x * π.kernel x (x (id.action d)) := by
  have hfac : ∀ e,
      (if id.action e ∈ insert (id.action d) E then
        (Function.update σ d π e).kernel x (x (id.action e)) else 1) =
      (if id.action e ∈ E then (σ e).kernel x (x (id.action e)) else 1) *
        (if e = d then π.kernel x (x (id.action d)) else 1) := by
    intro e
    by_cases he : e = d
    · subst e
      simp [hd]
    · have ha : id.action e ≠ id.action d := fun h => he (hinj h)
      simp [he, ha]
  unfold freeJoint
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib]
  simp [mul_assoc]

section Marginals

variable {bn : FinBayesNet}

theorem marg_mono {S : Finset bn.V} {f g : bn.Assignment → ℝ}
    (h : ∀ x, f x ≤ g x) (x : bn.Assignment) : marg S f x ≤ marg S g x :=
  Finset.sum_le_sum fun y _ => h y

theorem marg_preserves_independence (S : Finset bn.V) (v : bn.V) (hv : v ∉ S)
    (F : bn.Assignment → ℝ) (hF : ∀ x a, F (Function.update x v a) = F x)
    (x : bn.Assignment) (a : bn.states v) :
    marg S F (Function.update x v a) = marg S F x := by
  induction S using Finset.induction_on generalizing x with
  | empty => simpa [marg_empty] using hF x a
  | @insert w S hw ih =>
    have hvw : v ≠ w := fun h => hv (Finset.mem_insert.2 (Or.inl h))
    have hvS : v ∉ S := fun h => hv (Finset.mem_insert_of_mem h)
    rw [marg_insert hw, marg_insert hw]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Function.update_comm hvw, ih hvS]

theorem marg_policy_factor (E : Finset id.V) (d : id.D) (hd : id.action d ∉ E)
    (hinfo : ∀ v ∈ id.info d, v ∉ insert (id.action d) E)
    (π : Policy id ℝ d) (F : id.Assignment → ℝ) (x : id.Assignment) :
    marg (insert (id.action d) E) (fun y => F y * π.kernel y (y (id.action d))) x =
      ∑ a, π.kernel x a * marg E F (Function.update x (id.action d) a) := by
  rw [marg_insert hd]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold marg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hya : y (id.action d) = a := by
    simpa using mem_fibre.1 hy (id.action d) hd
  have hπ : π.kernel y = π.kernel x := by
    apply π.localOn
    intro v hv
    have hnot := hinfo v hv
    have hne : v ≠ id.action d := fun he => hnot (Finset.mem_insert.2 (Or.inl he))
    rw [mem_fibre.1 hy v (fun h => hnot (Finset.mem_insert_of_mem h)),
      Function.update_of_ne hne]
  dsimp only
  rw [hπ, hya, mul_comm]

theorem decision_marginal (κ : id.Kernel ℝ) (E : Finset id.V) (σ : Strategy id ℝ)
    (hinj : Function.Injective id.action) (d : id.D) (hd : id.action d ∉ E)
    (hinfo : ∀ v ∈ id.info d, v ∉ insert (id.action d) E) (π : Policy id ℝ d)
    (F : id.Assignment → ℝ) (x : id.Assignment) :
    marg (insert (id.action d) E)
        (fun y => freeJoint κ (insert (id.action d) E) (Function.update σ d π) y * F y) x =
      ∑ a, π.kernel x a * marg E (fun y => freeJoint κ E σ y * F y)
        (Function.update x (id.action d) a) := by
  have heq : (fun y => freeJoint κ (insert (id.action d) E) (Function.update σ d π) y * F y) =
      (fun y => (freeJoint κ E σ y * F y) * π.kernel y (y (id.action d))) := by
    funext y
    rw [freeJoint_activate κ E σ hinj d hd π]
    ring
  rw [heq]
  exact marg_policy_factor E d hd hinfo π _ x

theorem decision_marginal_pure (κ : id.Kernel ℝ) (E : Finset id.V) (σ : Strategy id ℝ)
    (hinj : Function.Injective id.action) (d : id.D) (hd : id.action d ∉ E)
    (hinfo : ∀ v ∈ id.info d, v ∉ insert (id.action d) E)
    (f : id.Assignment → id.states (id.action d))
    (hf : ∀ x y, (∀ v ∈ id.info d, x v = y v) → f x = f y)
    (F : id.Assignment → ℝ) (x : id.Assignment) :
    marg (insert (id.action d) E)
        (fun y => freeJoint κ (insert (id.action d) E)
          (Function.update σ d (Policy.ofFun f hf)) y * F y) x =
      marg E (fun y => freeJoint κ E σ y * F y) (Function.update x (id.action d) (f x)) := by
  rw [decision_marginal κ E σ hinj d hd hinfo]
  simp [Policy.ofFun_kernel, ite_mul]

end Marginals

/-- Under a strong information boundary, the probability marginal cannot depend on the
current free action. Nonempty state spaces and all policy normalisations come from the model
and `Policy`; chance normalisation and locality are explicit. Zero masses are allowed. -/
theorem probability_independent_weighted (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : RankedOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (E : Finset id.V) (σ : Strategy id ℝ) (d : id.D) (hd : id.action d ∉ E)
    (hboundary : Eᶜ ⊆ insert (id.action d) (id.info d))
    (G : id.Assignment → ℝ)
    (hG : Depends (Finset.univ.filter fun v => ord.rank v ≤ ord.rank (id.action d)) G)
    (hGv : ∀ y b, G (Function.update y (id.action d) b) = G y)
    (x : id.Assignment) (a : id.states (id.action d)) :
    marg E (fun y => freeJoint κ E σ y * G y) (Function.update x (id.action d) a) =
      marg E (fun y => freeJoint κ E σ y * G y) x := by
  let U : Finset id.V := Finset.univ.filter fun v => ord.rank v ≤ ord.rank (id.action d)
  have hRU : Eᶜ ⊆ U := by
    intro v hv
    rcases Finset.mem_insert.1 (hboundary hv) with rfl | hi
    · simp [U]
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (ord.info_lt d v hi).le⟩
  have hUE : Uᶜ ⊆ E := by
    intro v hv
    by_contra he
    exact Finset.mem_compl.1 hv (hRU (Finset.mem_compl.2 he))
  have hU : UpstreamClosed (bn := id.instantiate) U := by
    rintro (m | e) hm v hv
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
        (ord.parents_lt m v hv).le.trans (Finset.mem_filter.1 hm).2⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
        (ord.info_lt e v hv).le.trans (Finset.mem_filter.1 hm).2⟩
  have hn : ∀ m, id.instantiate.target m ∉ U → Normalised (activeKernel κ E σ) m := by
    rintro (m | e) hm
    · exact hnorm m
    · have he : id.action e ∈ E := hUE (Finset.mem_compl.2 hm)
      simpa [Normalised, activeKernel, he] using (σ e).normalised
  let F : id.Assignment → ℝ := fun y =>
    ∏ m ∈ Finset.univ.filter (fun m => id.instantiate.target m ∈ U),
      activeKernel κ E σ m y (y (id.instantiate.target m))
  have hdown : ∀ y, marg Uᶜ (freeJoint κ E σ) y = F y := by
    intro y
    rw [← joint_active]
    exact marg_joint_downstream _ (closed_instantiate hclosed).1 ord.order.toTopoOrder
      (active_local κ hloc E σ) U hn hU (fun v _ => (closed_instantiate hclosed).2 v) y
  have hF : ∀ y b, F (Function.update y (id.action d) b) = F y := by
    intro y b
    refine Finset.prod_congr rfl fun g hg => ?_
    have hgU := (Finset.mem_filter.1 hg).2
    cases g with
    | inl m =>
      have hne : id.target m ≠ id.action d := (id.closed_iff.1 hclosed).2.2.1 m d
      have hparent : id.action d ∉ id.parents m := by
        intro h
        exact (Nat.not_lt_of_ge (Finset.mem_filter.1 hgU).2) (ord.parents_lt m _ h)
      change κ m (Function.update y (id.action d) b)
        (Function.update y (id.action d) b (id.target m)) = _
      rw [Function.update_of_ne hne, hloc m _ y (fun v hv =>
        Function.update_of_ne (show v ≠ id.action d from fun he => hparent (he ▸ hv)) _ _)]
      rfl
    | inr e =>
      by_cases he : id.action e = id.action d
      · have hed : e = d := (id.closed_iff.1 hclosed).2.1 he
        subst e
        simp [activeKernel, hd]
      · have hinfo : id.action d ∉ id.info e := by
          intro h
          exact (Nat.not_lt_of_ge (Finset.mem_filter.1 hgU).2) (ord.info_lt e _ h)
        by_cases hE : id.action e ∈ E
        · simp only [activeKernel, hE, ↓reduceIte]
          change (σ e).kernel (Function.update y (id.action d) b)
            (Function.update y (id.action d) b (id.action e)) =
              (σ e).kernel y (y (id.action e))
          rw [Function.update_of_ne he, (σ e).localOn _ y (fun v hv =>
            Function.update_of_ne (show v ≠ id.action d from fun he => hinfo (he ▸ hv)) _ _)]
        · simp [activeKernel, hE]
  have hset : E = (E ∩ U) ∪ Uᶜ := by
    ext v
    by_cases hu : v ∈ U
    · simp [hu]
    · have he := hUE (Finset.mem_compl.2 hu)
      simp [hu, he]
  have hdisj : Disjoint (E ∩ U) Uᶜ :=
    Finset.disjoint_left.2 fun _ hi hc => Finset.mem_compl.1 hc (Finset.mem_inter.1 hi).2
  have hweighted : ∀ y, marg Uᶜ (fun z => freeJoint κ E σ z * G z) y = F y * G y := by
    intro y
    calc
      _ = marg Uᶜ (fun z => G z * freeJoint κ E σ z) y := by
        apply congrArg (fun f => marg Uᶜ f y)
        funext z
        ring
      _ = G y * marg Uᶜ (freeJoint κ E σ) y :=
        marg_mul_left (fun z hz => hG z y fun v hv =>
          mem_fibre.1 hz v (fun hc => Finset.mem_compl.1 hc hv))
      _ = _ := by rw [hdown]; ring
  have hm : ∀ y, marg E (fun z => freeJoint κ E σ z * G z) y =
      marg (E ∩ U) (fun z => F z * G z) y := by
    intro y
    calc
      _ = marg ((E ∩ U) ∪ Uᶜ) (fun z => freeJoint κ E σ z * G z) y :=
        congrArg (fun S => marg S (fun z => freeJoint κ E σ z * G z) y) hset
      _ = marg (E ∩ U) (fun z => marg Uᶜ (fun w => freeJoint κ E σ w * G w) z) y :=
        marg_union_disjoint hdisj _ _
      _ = _ := congrArg (fun f => marg (E ∩ U) f y) (funext hweighted)
  rw [hm, hm]
  apply marg_preserves_independence _ _ (fun h => hd (Finset.mem_inter.1 h).1) _ _ x a
  intro y b
  rw [hF, hGv]

/-- The no-evidence specialization of structural probability independence. -/
theorem probability_independent (κ : id.Kernel ℝ) (hclosed : id.Closed)
    (ord : RankedOrder id) (hloc : ∀ m, Local κ m) (hnorm : ∀ m, Normalised κ m)
    (E : Finset id.V) (σ : Strategy id ℝ) (d : id.D) (hd : id.action d ∉ E)
    (hboundary : Eᶜ ⊆ insert (id.action d) (id.info d))
    (x : id.Assignment) (a : id.states (id.action d)) :
    marg E (freeJoint κ E σ) (Function.update x (id.action d) a) =
      marg E (freeJoint κ E σ) x := by
  simpa using probability_independent_weighted κ hclosed ord hloc hnorm E σ d hd hboundary
    (fun _ => 1) (fun _ _ _ => rfl) (fun _ _ => rfl) x a

end
end InfluenceDiagramsProofs.DVE
