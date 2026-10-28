module

public import Theory.AlgebraicGroup.RootData.Extrema
public import Theory.AlgebraicGroup.RootData.Realization

universe u v

open scoped BigOperators

/-!
Relative-root projections, heights, fibers, and their basic combinatorics.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The roots in the integral span of `J`.  Since `D.rootWeight` enumerates
the actual roots, this is precisely `ℤ J ∩ Σ`. -/
@[expose]
public def RootSubsystemSpan
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (J : Set D.Root) : Set D.Root :=
  {α | D.rootWeight α ∈ Subgroup.closure (D.rootWeight '' J)}

public noncomputable def RootHeight {ι : Type v} [Finite ι]
    (coeff : ι → ι → ℤ) (base : Finset ι) (β : ι) : ℤ :=
  letI := Fintype.ofFinite ι
  ∑ γ ∈ base, coeff β γ

@[expose]
public noncomputable def RelativeRootProjection {ι : Type v} [Finite ι]
    (coeff : ι → ι → ℤ) (base J : Set ι) (β : ι) : ι →₀ ℤ := by
  classical
  exact Finsupp.equivFunOnFinite.symm fun γ =>
    if γ ∈ base \ J then coeff β γ else 0

@[expose]
public noncomputable def RelativeRootHeight {ι : Type v} [Finite ι]
    (coeff : ι → ι → ℤ) (base : Finset ι) (J : Set ι) (β : ι) : ℤ := by
  classical
  letI := Fintype.ofFinite ι
  exact ∑ γ ∈ base, if γ ∉ J then coeff β γ else 0

@[expose]
public def RelativeRootFiber {ι : Type v} [Finite ι]
    (coeff : ι → ι → ℤ) (base J roots : Set ι)
    (γ : ι →₀ ℤ) : Set ι :=
  {α | α ∈ roots ∧ RelativeRootProjection coeff base J α = γ}

end

section

/-- Relative root height is additive when a root differs from another by a
list sum of roots. -/
public theorem relativeRootHeight_eq_add_list_of_root_eq_add_sum
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N)
    (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {α γ : ι} (l : List ι)
    (hroot : P.root γ = P.root α + (l.map P.root).sum) :
    RelativeRootHeight coeff base.support J γ =
      RelativeRootHeight coeff base.support J α +
        (l.map (RelativeRootHeight coeff base.support J)).sum := by
  classical
  have hListExpansion (l : List ι) : (l.map P.root).sum =
      ∑ δ ∈ base.support, (((l.map fun β => coeff β δ).sum : ℤ) : R) • P.root δ := by
    induction l with
    | nil => simp
    | cons β l ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [(hCoeff β).1, ih]
        simp only [Int.cast_add, add_smul, Finset.sum_add_distrib]
  have hCoeffUnique (η δ : ι) (hδ : δ ∈ base.support) {f : ι → ℤ}
      (hf : P.root η = ∑ j ∈ base.support, (f j : R) • P.root j) :
      coeff η δ = f δ := by
    have hc := (hCoeff η).1
    rw [base.support.sum_subtype (p := (· ∈ base.support)) (by simp)
      (F := inferInstance)] at hc hf
    have heq : ∑ j : base.support, (coeff η j : R) • P.root j =
        ∑ j : base.support, (f j : R) • P.root j := hc.symm.trans hf
    have heqCoeff : (coeff η δ : R) = (f δ : R) :=
      Fintype.linearIndependent_iffₛ.mp base.linearIndepOn_root
        (fun j : base.support => (coeff η j : R))
        (fun j : base.support => (f j : R)) heq ⟨δ, hδ⟩
    exact_mod_cast heqCoeff
  let f : ι → ℤ := fun δ => coeff α δ + (l.map fun β => coeff β δ).sum
  have hrootExpansion : P.root γ =
      ∑ δ ∈ base.support, (f δ : R) • P.root δ := by
    rw [hroot, (hCoeff α).1, hListExpansion]
    simp only [f, Int.cast_add, add_smul, Finset.sum_add_distrib]
  have hcoeffAdd (δ : ι) (hδ : δ ∈ base.support) :
      coeff γ δ = coeff α δ + (l.map fun β => coeff β δ).sum := by
    exact hCoeffUnique γ δ hδ hrootExpansion
  have hheightListAux (xs : List ι) :
      (xs.map (RelativeRootHeight coeff base.support J)).sum =
        ∑ δ ∈ base.support, if δ ∉ J then (xs.map fun β => coeff β δ).sum else 0 := by
    induction xs with
    | nil => simp
    | cons β xs ih =>
        simp only [List.map_cons, List.sum_cons, RelativeRootHeight]
        rw [ih, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro δ hδ
        by_cases hδJ : δ ∈ J <;> simp [hδJ]
  have hheightList := hheightListAux l
  simp only [RelativeRootHeight]
  rw [hheightList, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro δ hδ
  by_cases hδJ : δ ∈ J <;> simp [hδJ, hcoeffAdd δ hδ]

end

section

/-- Relative root height is additive along an equality expressing one root
as the sum of two roots. -/
public theorem relativeRootHeight_eq_add_of_root_eq_add
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N)
    (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {α β γ : ι} (hroot : P.root α = P.root β + P.root γ) :
    RelativeRootHeight coeff base.support J α =
      RelativeRootHeight coeff base.support J β +
        RelativeRootHeight coeff base.support J γ := by
  classical
  have hCoeffUnique (η δ : ι) (hδ : δ ∈ base.support) {f : ι → ℤ}
      (hf : P.root η = ∑ j ∈ base.support, (f j : R) • P.root j) :
      coeff η δ = f δ := by
    have hc := (hCoeff η).1
    rw [base.support.sum_subtype (p := (· ∈ base.support)) (by simp)
      (F := inferInstance)] at hc hf
    have heq : ∑ j : base.support, (coeff η j : R) • P.root j =
        ∑ j : base.support, (f j : R) • P.root j := hc.symm.trans hf
    have heqCoeff : (coeff η δ : R) = (f δ : R) :=
      Fintype.linearIndependent_iffₛ.mp base.linearIndepOn_root
        (fun j : base.support => (coeff η j : R))
        (fun j : base.support => (f j : R)) heq ⟨δ, hδ⟩
    exact_mod_cast heqCoeff
  let f : ι → ℤ := fun δ => coeff β δ + coeff γ δ
  have hrootExpansion : P.root α =
      ∑ δ ∈ base.support, (f δ : R) • P.root δ := by
    rw [hroot, (hCoeff β).1, (hCoeff γ).1]
    simp only [f, Int.cast_add, add_smul, Finset.sum_add_distrib]
  have hcoeffAdd (δ : ι) (hδ : δ ∈ base.support) :
      coeff α δ = coeff β δ + coeff γ δ := by
    exact hCoeffUnique α δ hδ hrootExpansion
  simp only [RelativeRootHeight]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro δ hδ
  by_cases hδJ : δ ∈ J
  · simp [hδJ]
  · simp [hδJ, hcoeffAdd δ hδ]

end

section

private lemma relativeRootHeight_base_coeff
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N)
    (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {δ : ι} (hδ : δ ∈ base.support) :
    ∀ γ, γ ∈ base.support →
      (γ = δ → coeff δ γ = 1) ∧ (γ ≠ δ → coeff δ γ = 0) := by
  classical
  intro γ hγ
  have hCoeffUnique (γ : ι) (hγ : γ ∈ base.support) :
      coeff δ γ = if γ = δ then 1 else 0 := by
    have hc := (hCoeff δ).1
    have hroot : P.root δ = ∑ j ∈ base.support,
        ((if j = δ then 1 else 0 : ℤ) : R) • P.root j := by
      rw [Finset.sum_eq_single_of_mem δ hδ]
      · simp
      · intro b hb hbne
        simp [hbne]
    rw [base.support.sum_subtype (p := (· ∈ base.support)) (by simp)
      (F := inferInstance)] at hc hroot
    have heq : ∑ j : base.support, (coeff δ j : R) • P.root j =
        ∑ j : base.support, ((if j = δ then 1 else 0 : ℤ) : R) • P.root j :=
      hc.symm.trans hroot
    have heqCoeff : (coeff δ γ : R) =
        ((if γ = δ then 1 else 0 : ℤ) : R) :=
      Fintype.linearIndependent_iffₛ.mp base.linearIndepOn_root
        (fun j : base.support => (coeff δ j : R))
        (fun j : base.support => ((if j = δ then 1 else 0 : ℤ) : R))
        heq ⟨γ, hγ⟩
    exact_mod_cast heqCoeff
  have hcu := hCoeffUnique γ hγ
  constructor
  · intro hγδ
    subst γ
    simpa using hcu
  · intro hγδ
    simpa [hγδ] using hcu

private lemma relativeRootHeight_base_eq_zero
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N)
    (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {δ : ι} (hδ : δ ∈ base.support) (hδJ : δ ∈ J) :
      RelativeRootHeight coeff base.support J δ = 0 := by
  classical
    simp only [RelativeRootHeight]
    apply Finset.sum_eq_zero
    intro γ hγ
    by_cases hγδ : γ = δ
    · subst γ
      simp [hδJ]
    · simp [(relativeRootHeight_base_coeff P base coeff hCoeff hδ γ hγ).2 hγδ]

private lemma relativeRootHeight_base_eq_one
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N)
    (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {δ : ι} (hδ : δ ∈ base.support) (hδJ : δ ∉ J) :
      RelativeRootHeight coeff base.support J δ = 1 := by
  classical
    simp only [RelativeRootHeight]
    rw [Finset.sum_eq_single_of_mem δ hδ]
    · simp [hδJ, (relativeRootHeight_base_coeff P base coeff hCoeff hδ δ hδ).1 rfl]
    · intro γ hγ hγδ
      simp [(relativeRootHeight_base_coeff P base coeff hCoeff hδ γ hγ).2 hγδ]

/-- A base root has relative height zero exactly when it belongs to `J`. -/
public theorem relativeRootHeight_eq_zero_iff_mem
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N)
    (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {δ : ι} (hδ : δ ∈ base.support) :
    RelativeRootHeight coeff base.support J δ = 0 ↔ δ ∈ J := by
  classical
  constructor
  · intro hzero
    by_contra hδJ
    rw [relativeRootHeight_base_eq_one P base J coeff hCoeff hδ hδJ] at hzero
    omega
  · intro hδJ
    exact relativeRootHeight_base_eq_zero P base J coeff hCoeff hδ hδJ

/-- A base root has relative height one exactly when it lies outside `J`. -/
public theorem relativeRootHeight_eq_one_iff_not_mem
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N)
    (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {δ : ι} (hδ : δ ∈ base.support) :
    RelativeRootHeight coeff base.support J δ = 1 ↔ δ ∉ J := by
  classical
  constructor
  · intro hone
    by_contra hδJ
    rw [relativeRootHeight_base_eq_zero P base J coeff hCoeff hδ hδJ] at hone
    omega
  · intro hδJ
    exact relativeRootHeight_base_eq_one P base J coeff hCoeff hδ hδJ

end

section

/-- Reflection in a simple root belonging to `J` preserves relative root
height outside `J`. -/
public theorem relativeRootHeight_reflectionPerm_eq
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {δ : ι} (hδJ : δ ∈ J) (α : ι) :
    RelativeRootHeight coeff base.support J (P.reflectionPerm δ α) =
      RelativeRootHeight coeff base.support J α := by
  classical
  have hδSupport : δ ∈ base.support := hJ hδJ
  have hCoeffUnique (β γ : ι) (hγ : γ ∈ base.support) {f : ι → ℤ}
      (hf : P.root β = ∑ j ∈ base.support, (f j : R) • P.root j) :
      coeff β γ = f γ := by
    have hc := (hCoeff β).1
    rw [base.support.sum_subtype (p := (· ∈ base.support)) (by simp)
      (F := inferInstance)] at hc hf
    have heq : ∑ j : base.support, (coeff β j : R) • P.root j =
        ∑ j : base.support, (f j : R) • P.root j := hc.symm.trans hf
    have heqCoeff : (coeff β γ : R) = (f γ : R) :=
      Fintype.linearIndependent_iffₛ.mp base.linearIndepOn_root
        (fun j : base.support => (coeff β j : R))
        (fun j : base.support => (f j : R)) heq ⟨γ, hγ⟩
    exact_mod_cast heqCoeff
  let f : ι → ℤ := fun γ =>
    coeff α γ - if γ = δ then P.pairingIn ℤ α δ else 0
  have hroot : P.root (P.reflectionPerm δ α) =
      ∑ γ ∈ base.support, (f γ : R) • P.root γ := by
    rw [P.root_reflectionPerm, P.reflection_apply_root, (hCoeff α).1]
    simp only [f, Int.cast_sub, sub_smul, Finset.sum_sub_distrib]
    congr 1
    rw [← P.algebraMap_pairingIn ℤ α δ]
    simp [hδSupport]
  have hcoeffEq (γ : ι) (hγSupport : γ ∈ base.support) (hγJ : γ ∉ J) :
      coeff (P.reflectionPerm δ α) γ = coeff α γ := by
    rw [hCoeffUnique (P.reflectionPerm δ α) γ hγSupport hroot]
    simp only [f]
    have hγδ : γ ≠ δ := fun h => hγJ (h ▸ hδJ)
    simp [hγδ]
  apply Finset.sum_congr rfl
  intro γ hγSupport
  by_cases hγJ : γ ∈ J
  · simp [hγJ]
  · simp [hγJ, hcoeffEq γ hγSupport hγJ]

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A valid Chevalley commutator term has the expected relative root height.
This is the smallest arithmetic bridge from the commutator product expansion to
the relative-root filtration. -/
public theorem relativeRootHeight_of_validChevalleyCommutatorTerm
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {α β : D.Root} (q : ChevalleyCommutatorTerm D.Root)
    (hvalid : IsValidChevalleyCommutatorTerm D P e α β q) :
    RelativeRootHeight coeff base.support J (e q.root) =
      (q.i : ℤ) * RelativeRootHeight coeff base.support J (e α) +
        (q.j : ℤ) * RelativeRootHeight coeff base.support J (e β) := by
  rcases hvalid with ⟨hqi, hqj, hroot⟩
  have hsucc : q.i = Nat.succ (q.i - 1) := (Nat.succ_pred_eq_of_pos hqi).symm
  have hroot' : P.root (e q.root) =
      P.root (e α) + ((List.replicate (q.i - 1) (e α) ++
        List.replicate q.j (e β)).map P.root).sum := by
    rw [hroot, hsucc]
    simp [Nat.cast_smul_eq_nsmul, List.sum_append, List.sum_replicate,
      add_comm, add_left_comm, add_smul]
  rw [relativeRootHeight_eq_add_list_of_root_eq_add_sum P base J coeff hCoeff _ hroot']
  simp [List.sum_append, List.sum_replicate]
  have hq : (q.i : ℤ) = ((q.i - 1 : ℕ) : ℤ) + 1 := by
    omega
  rw [hq]
  ring

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

end

section

/-- A root of positive relative height is positive with respect to the full
base. -/
public theorem base_isPos_of_relativeRootHeight_pos
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {α : ι} (hheight : 0 < RelativeRootHeight coeff base.support J α) :
    base.IsPos α := by
  classical
  have hCoeffUnique (β γ : ι) (hγ : γ ∈ base.support) {f : ι → ℤ}
      (hf : P.root β = ∑ j ∈ base.support, (f j : R) • P.root j) :
      coeff β γ = f γ := by
    have hc := (hCoeff β).1
    rw [base.support.sum_subtype (p := (· ∈ base.support)) (by simp)
      (F := inferInstance)] at hc hf
    have heq : ∑ j : base.support, (coeff β j : R) • P.root j =
        ∑ j : base.support, (f j : R) • P.root j := hc.symm.trans hf
    have heqCoeff : (coeff β γ : R) = (f γ : R) :=
      Fintype.linearIndependent_iffₛ.mp base.linearIndepOn_root
        (fun j : base.support => (coeff β j : R))
        (fun j : base.support => (f j : R)) heq ⟨γ, hγ⟩
    exact_mod_cast heqCoeff
  obtain ⟨f, hfSupport, hfSign, hfRoot⟩ := base.exists_root_eq_sum_int α
  have hcf : ∀ γ ∈ base.support, coeff α γ = f γ := by
    intro γ hγ
    apply hCoeffUnique α γ hγ
    simpa only [Int.cast_smul_eq_zsmul] using hfRoot
  have hcoeffNonneg : ∀ γ ∈ base.support, 0 ≤ coeff α γ := by
    rcases hfSign with hpos | hneg
    · intro γ hγ
      rw [hcf γ hγ]
      exact (Pi.lt_def.mp hpos).1 γ
    · exfalso
      have hnonpos : RelativeRootHeight coeff base.support J α ≤ 0 := by
        simp only [RelativeRootHeight]
        apply Finset.sum_nonpos
        intro γ hγ
        by_cases hγJ : γ ∈ J
        · simp [hγJ]
        · simp only [if_pos hγJ]
          rw [hcf γ hγ]
          exact (Pi.lt_def.mp hneg).1 γ
      omega
  rw [base.isPos_iff]
  have hrootZ : P.root α = ∑ γ ∈ base.support, coeff α γ • P.root γ := by
    simpa only [Int.cast_smul_eq_zsmul] using (hCoeff α).1
  rw [base.height_eq_sum hrootZ]
  refine lt_of_lt_of_le hheight ?_
  apply Finset.sum_le_sum
  intro γ hγ
  by_cases hγJ : γ ∈ J
  · simp [hγJ, hcoeffNonneg γ hγ]
  · simp [hγJ]

end

section

/-- A positive root strictly below another root in relative height admits a
height-one root extension when their difference is a sum of simple roots. -/
public theorem positiveRootDifference_exists_relativeHeight_one_add
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible]
    (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (α γ : ι) (l : List ι)
    (hαheight : 0 < RelativeRootHeight coeff base.support J α)
    (hl : ∀ δ ∈ l, δ ∈ base.support)
    (hγ : P.root γ = P.root α + (l.map P.root).sum)
    (hheightlt : RelativeRootHeight coeff base.support J α <
      RelativeRootHeight coeff base.support J γ) :
    ∃ β η, P.root η = P.root α + P.root β ∧
      RelativeRootHeight coeff base.support J β = 1 := by
  classical
  induction hlen : l.length using Nat.strong_induction_on generalizing α l with
  | h n ih =>
      have hαpos : base.IsPos α :=
        base_isPos_of_relativeRootHeight_pos P base J coeff hCoeff hαheight
      have hlne : l ≠ [] := by
        intro hnil
        subst l
        simp only [List.map_nil, List.sum_nil, add_zero] at hγ
        have hαγ : α = γ := P.root.injective hγ.symm
        subst γ
        omega
      obtain ⟨δ, hδl, η, hη⟩ :=
        positiveRootDifference_exists_simple_add P base α γ l hαpos hl hlne hγ
      by_cases hδJ : δ ∈ J
      · let l' := l.erase δ
        have hl' : ∀ x ∈ l', x ∈ base.support := by
          intro x hx
          exact hl x (List.mem_of_mem_erase hx)
        have hlen' : l'.length < n := by
          rw [← hlen]
          have hpos : 0 < l.length := Nat.pos_of_ne_zero (by simpa using hlne)
          simpa [l', List.length_erase_of_mem hδl] using hpos
        have herase : (l.map P.root).sum = P.root δ + (l'.map P.root).sum := by
          simpa [l'] using (List.perm_cons_erase hδl |>.map P.root).sum_eq
        have hγη : P.root γ = P.root η + (l'.map P.root).sum := by
          rw [hγ, herase, hη]
          abel
        have hδheight : RelativeRootHeight coeff base.support J δ = 0 :=
          (relativeRootHeight_eq_zero_iff_mem P base J coeff hCoeff (hl δ hδl)).mpr hδJ
        have hηheight : RelativeRootHeight coeff base.support J η =
            RelativeRootHeight coeff base.support J α := by
          rw [relativeRootHeight_eq_add_of_root_eq_add P base J coeff hCoeff hη,
            hδheight, add_zero]
        have hηheightpos : 0 < RelativeRootHeight coeff base.support J η := by
          rw [hηheight]
          exact hαheight
        have hηheightlt : RelativeRootHeight coeff base.support J η <
            RelativeRootHeight coeff base.support J γ := by
          rw [hηheight]
          exact hheightlt
        obtain ⟨β, ζ, hζ, hβheight⟩ :=
          ih l'.length hlen' η l' hηheightpos hl' hγη hηheightlt rfl
        have hβpos : base.IsPos β :=
          base_isPos_of_relativeRootHeight_pos P base J coeff hCoeff (by omega)
        rcases simpleRootExtension_exchange P base α δ β η ζ hαpos hβpos
          (hl δ hδl) hη hζ with hαβ | hδβ
        · obtain ⟨ρ, hρ⟩ := hαβ
          exact ⟨β, ρ, hρ, hβheight⟩
        · obtain ⟨ρ, hρ⟩ := hδβ
          have hρheight : RelativeRootHeight coeff base.support J ρ = 1 := by
            rw [relativeRootHeight_eq_add_of_root_eq_add P base J coeff hCoeff hρ,
              hδheight, hβheight, zero_add]
          refine ⟨ρ, ζ, ?_, hρheight⟩
          rw [hζ, hη, hρ]
          abel
      · exact ⟨δ, η, hη,
          (relativeRootHeight_eq_one_iff_not_mem P base J coeff hCoeff (hl δ hδl)).mpr hδJ⟩

end

end Theory.AlgebraicGroup

