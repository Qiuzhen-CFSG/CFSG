module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Basic
public import Theory.AlgebraicGroup.RootData.RelativeWeyl

universe u

open scoped commutatorElement

/-!
Commutators, normalizers, and normal layers of the relative-root series.

For a set `J` of simple roots, the reverse layer inclusion uses GLS3 Lemma
1.13.6 to split every relative root of height at least two into a height-one
root and a complementary root.  The leading `(1, 1)` Chevalley commutator term
then generates the requested root element modulo the following layer, provided
its expected coefficient is nonzero.  Finite descending induction from a
terminal layer upgrades these inclusions to exact commutator layers.  This is
the root-theoretic core of the lower-central-series argument in GLS3 Theorem
1.13.5(c); coefficient nonvanishing remains an explicit input.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_commutator_le
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i)
    {α β : D.Root}
    (hα : (i : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α))
    (hβ : (1 : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e β)) :
    ⁅(D.rootSubgroup α).toSubgroup, (D.rootSubgroup β).toSubgroup⁆ ≤
      RelativeRootSeries D e base.support coeff J (i + 1) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hrootα : (D.rootSubgroup α : Set (Variety.Point K)) = Set.range (C.x α) := by
    simpa using (hC.1 α).2.symm
  have hrootβ : (D.rootSubgroup β : Set (Variety.Point K)) = Set.range (C.x β) := by
    simpa using (hC.1 β).2.symm
  have hx' : x ∈ (D.rootSubgroup α).toClosedSubgroup.toSubgroup := by
    simpa using hx
  change x ∈ (D.rootSubgroup α : Set (Variety.Point K)) at hx'
  rw [hrootα] at hx'
  rw [Set.mem_range] at hx'
  rcases hx' with ⟨t, rfl⟩
  have hy' : y ∈ (D.rootSubgroup β).toClosedSubgroup.toSubgroup := by
    simpa using hy
  change y ∈ (D.rootSubgroup β : Set (Variety.Point K)) at hy'
  rw [hrootβ] at hy'
  rw [Set.mem_range] at hy'
  rcases hy' with ⟨u, rfl⟩
  by_cases hEq : α = β
  · subst hEq
    have hcomm : Commute (C.x α t) (C.x α u) := by
      show C.x α t * C.x α u = C.x α u * C.x α t
      calc
        C.x α t * C.x α u = C.x α (t + u) := hC.2.2.2.1 α t u
        _ = C.x α (u + t) := by simp [add_comm]
        _ = C.x α u * C.x α t := by rw [hC.2.2.2.1 α u t]
    have hone : ⁅C.x α t, C.x α u⁆ = 1 := hcomm.commutator_eq
    rw [hone]
    simp [RelativeRootSeries, RootSubgroupGenerated]
  · let := P.indexNeg
    have hαPos : base.IsPos (e α) := by
      apply base_isPos_of_relativeRootHeight_pos P base (e '' J) coeff hCoeff
      omega
    have hβPos : base.IsPos (e β) := by
      apply base_isPos_of_relativeRootHeight_pos P base (e '' J) coeff hCoeff
      omega
    have hnotopp : P.root (e α) ≠ - P.root (e β) := by
      intro hneg
      have hidx : e α = P.reflectionPerm (e β) (e β) := P.root_eq_neg_iff.mp hneg
      have hαPos' : base.IsPos (- e β) := by simpa [hidx] using hαPos
      have hβnot : ¬ base.IsPos (e β) := (RootPairing.Base.IsPos.neg_iff_not (P := P) (b := base)
        (i := e β)).mp hαPos'
      exact hβnot hβPos
    have hne : e α ≠ e β := by
      intro heq
      apply hEq
      exact e.injective heq
    have hlin : LinearIndependent R ![P.root (e α), P.root (e β)] :=
      RootPairing.IsReduced.linearIndependent (P := P) hne hnotopp
    rw [LinearIndependent.pair_iff] at hlin
    have hLI : AreLinearlyIndependentRoots D P e α β := by
      simpa [AreLinearlyIndependentRoots] using hlin
    rcases hC.2.2.2.2.1 α β hLI with ⟨order, c, hnodup, hpairwise, hvalid, hcoeff, hformula⟩
    have hterm (s v : k) (q : ChevalleyCommutatorTerm D.Root) (hq : q ∈ order) :
        C.x q.root (c q * s ^ q.i * v ^ q.j) ∈
          RelativeRootSeries D e base.support coeff J (i + 1) := by
      have hqvalid : IsValidChevalleyCommutatorTerm D P e α β q := (hvalid q).mp hq
      have hqheight : (i + 1 : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e q.root) := by
        rw [relativeRootHeight_of_validChevalleyCommutatorTerm D P e base (e '' J) coeff hCoeff q hqvalid]
        have hqi : (1 : ℤ) ≤ q.i := by exact_mod_cast (Nat.succ_le_of_lt hqvalid.1)
        have hqj : (1 : ℤ) ≤ q.j := by exact_mod_cast (Nat.succ_le_of_lt hqvalid.2.1)
        nlinarith
      have hrootq : (D.rootSubgroup q.root : Set (Variety.Point K)) = Set.range (C.x q.root) := by
        simpa using (hC.1 q.root).2.symm
      have hqin : C.x q.root (c q * s ^ q.i * v ^ q.j) ∈ Set.range (C.x q.root) := by
        exact ⟨c q * s ^ q.i * v ^ q.j, rfl⟩
      have hqin' : C.x q.root (c q * s ^ q.i * v ^ q.j) ∈ (D.rootSubgroup q.root : Set (Variety.Point K)) := by
        rw [hrootq]
        exact hqin
      rw [RelativeRootSeries, RootSubgroupGenerated]
      apply Subgroup.subset_closure
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨q.root, hqheight, hqin'⟩
    have hprod : (order.map fun q => C.x q.root (c q * (-t) ^ q.i * (-u) ^ q.j)).prod ∈
        RelativeRootSeries D e base.support coeff J (i + 1) := by
      apply Subgroup.list_prod_mem
      intro z hz
      rw [List.mem_map] at hz
      rcases hz with ⟨q, hq, rfl⟩
      exact hterm (-t) (-u) q hq
    have hcommRaw : (C.x α (-t))⁻¹ * (C.x β (-u))⁻¹ * C.x α (-t) * C.x β (-u) ∈
        RelativeRootSeries D e base.support coeff J (i + 1) := by
      rw [hformula (-t) (-u)]
      exact hprod
    have hzeroα : C.x α 0 = 1 := by
      simpa using (hC.2.2.2.1 α 0 0)
    have hzeroβ : C.x β 0 = 1 := by
      simpa using (hC.2.2.2.1 β 0 0)
    have hxinv : C.x α (-t) = (C.x α t)⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [hC.2.2.2.1 α (-t) t]
      have hnegα : (-t : k) + t = 0 := by abel
      simpa [hnegα] using hzeroα
    have hyinv : C.x β (-u) = (C.x β u)⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [hC.2.2.2.1 β (-u) u]
      have hnegβ : (-u : k) + u = 0 := by abel
      simpa [hnegβ] using hzeroβ
    simpa [hxinv, hyinv, commutatorElement_def, mul_assoc] using hcommRaw

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_commutator_series_le
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i) :
    ⁅RelativeRootSeries D e base.support coeff J i,
      RelativeRootSeries D e base.support coeff J 1⁆ ≤
        RelativeRootSeries D e base.support coeff J (i + 1) := by
  classical
  let Snext : Subgroup (Variety.Point K) := RelativeRootSeries D e base.support coeff J (i + 1)

  have hrootConj :
      ∀ {β : D.Root} (u : K.Point),
        (1 : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e β) →
        u ∈ D.rootSubgroup β →
        ∀ z ∈ RelativeRootSeries D e base.support coeff J (i + 1),
          u * z * u⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
    intro β u hβ hu z hz
    rw [RelativeRootSeries, RootSubgroupGenerated] at hz
    refine Subgroup.closure_induction
      (p := fun z _ => u * z * u⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1))
      (k := ⋃ α ∈ {α | (i + 1 : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α)},
        ↑(D.rootSubgroup α : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hz
    · intro z hz
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hz
      rcases hz with ⟨α : D.Root, hα, hzα⟩
      have hα' : (i : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α) := by
        have hle : (i : ℤ) ≤ (i + 1 : ℤ) := by exact_mod_cast Nat.le_succ i
        exact hle.trans hα
      have hsub :=
        relativeRootSeries_commutator_le (D := D) (C := C) (P := P) (e := e)
          (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC) (J := J)
          (i := i) hi (α := α) (β := β) hα' hβ
      have hcommzu : ⁅z, u⁆ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := hsub
        (Subgroup.commutator_mem_commutator hzα hu)
      have hcommuz : ⁅u, z⁆ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
        simpa [commutatorElement_inv] using
          (RelativeRootSeries D e base.support coeff J (i + 1)).inv_mem hcommzu
      have hzS : z ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
        rw [RelativeRootSeries, RootSubgroupGenerated]
        apply Subgroup.subset_closure
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨α, hα, hzα⟩
      have hmul' : ⁅u, z⁆ * z ∈ RelativeRootSeries D e base.support coeff J (i + 1) :=
        (RelativeRootSeries D e base.support coeff J (i + 1)).mul_mem hcommuz hzS
      have hmul : u * z * u⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
        change (MulAut.conj u) z ∈ RelativeRootSeries D e base.support coeff J (i + 1)
        rw [conj_eq_commutatorElement_mul]
        exact hmul'
      simpa [MulAut.conj_apply] using hmul
    · simp
    · intro z₁ z₂ hz₁ hz₂ ih₁ ih₂
      simpa [mul_assoc] using
        (RelativeRootSeries D e base.support coeff J (i + 1)).mul_mem ih₁ ih₂
    · intro z hz ih
      simpa [mul_assoc] using
        (RelativeRootSeries D e base.support coeff J (i + 1)).inv_mem ih

  have hA_norm :
      ∀ x ∈ RelativeRootSeries D e base.support coeff J i,
        x ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)) := by
    intro x hx
    rw [RelativeRootSeries, RootSubgroupGenerated] at hx
    refine Subgroup.closure_induction
      (p := fun x _ => x ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)))
      (k := ⋃ α ∈ {α | (i : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α)},
        ↑(D.rootSubgroup α : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hx
    · intro x hx
      have hx' : ∃ α : D.Root, ∃ _ : (i : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α),
          x ∈ (D.rootSubgroup α : Set (Variety.Point K)) := by
        simpa only [Set.mem_iUnion, Set.mem_ofPred_eq] using hx
      rcases hx' with ⟨α, hα, hxα⟩
      have h1 : (1 : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α) := by
        have h1' : (1 : ℤ) ≤ (i : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt hi)
        exact h1'.trans hα
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · exact hrootConj x h1 hxα z
      · intro hz
        have hxInvα : x⁻¹ ∈ D.rootSubgroup α := (D.rootSubgroup α).inv_mem hxα
        simpa [mul_assoc] using hrootConj x⁻¹ h1 hxInvα (x * z * x⁻¹) hz
    · exact (Subgroup.normalizer (Snext : Set (Variety.Point K))).one_mem
    · intro x₁ x₂ hx₁ hx₂ ih₁ ih₂
      exact (Subgroup.normalizer (Snext : Set (Variety.Point K))).mul_mem ih₁ ih₂
    · intro x hx ih
      exact (Subgroup.normalizer (Snext : Set (Variety.Point K))).inv_mem ih

  have hB_norm :
      ∀ y ∈ RelativeRootSeries D e base.support coeff J 1,
        y ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)) := by
    intro y hy
    rw [RelativeRootSeries, RootSubgroupGenerated] at hy
    refine Subgroup.closure_induction
      (p := fun y _ => y ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)))
      (k := ⋃ α ∈ {α | (1 : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α)},
        ↑(D.rootSubgroup α : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hy
    · intro y hy
      have hy' : ∃ β : D.Root, ∃ _ : (1 : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e β),
          y ∈ (D.rootSubgroup β : Set (Variety.Point K)) := by
        simpa only [Set.mem_iUnion, Set.mem_ofPred_eq] using hy
      rcases hy' with ⟨β, hβ, hyβ⟩
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · exact hrootConj y hβ hyβ z
      · intro hz
        have hyInvβ : y⁻¹ ∈ D.rootSubgroup β := (D.rootSubgroup β).inv_mem hyβ
        simpa [mul_assoc] using hrootConj y⁻¹ hβ hyInvβ (y * z * y⁻¹) hz
    · exact (Subgroup.normalizer (Snext : Set (Variety.Point K))).one_mem
    · intro y₁ y₂ hy₁ hy₂ ih₁ ih₂
      exact (Subgroup.normalizer (Snext : Set (Variety.Point K))).mul_mem ih₁ ih₂
    · intro y hy ih
      exact (Subgroup.normalizer (Snext : Set (Variety.Point K))).inv_mem ih

  rw [Subgroup.commutator_le]
  intro x hx
  rw [RelativeRootSeries, RootSubgroupGenerated] at hx
  refine Subgroup.closure_induction
    (p := fun x _ => ∀ y ∈ RelativeRootSeries D e base.support coeff J 1,
      ⁅x, y⁆ ∈ RelativeRootSeries D e base.support coeff J (i + 1))
    (k := ⋃ α ∈ {α | (i : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α)},
      ↑(D.rootSubgroup α : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hx
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨α, hα, hxα⟩
    intro y hy
    rw [RelativeRootSeries, RootSubgroupGenerated] at hy
    refine Subgroup.closure_induction
      (p := fun y _ => ⁅x, y⁆ ∈ RelativeRootSeries D e base.support coeff J (i + 1))
      (k := ⋃ α ∈ {α | (1 : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α)},
        ↑(D.rootSubgroup α : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hy
    · intro y hy
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hy
      rcases hy with ⟨β, hβ, hyβ⟩
      exact (relativeRootSeries_commutator_le (D := D) (C := C) (P := P) (e := e)
        (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC) (J := J)
        (i := i) hi (α := α) (β := β) hα hβ)
        (Subgroup.commutator_mem_commutator hxα hyβ)
    · simp
    · intro y₁ y₂ hy₁ hy₂ ih₁ ih₂
      have hy1norm : y₁ ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)) := hB_norm y₁ hy₁
      have hy1conj : y₁ * ⁅x, y₂⁆ * y₁⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
        exact (Subgroup.mem_normalizer_iff.mp hy1norm (⁅x, y₂⁆)).mp ih₂
      have hxy1 : ⁅x, y₁⁆ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := ih₁
      rw [commutatorElement_mul_right_eq_mul_conj]
      simpa [mul_assoc] using
        (RelativeRootSeries D e base.support coeff J (i + 1)).mul_mem hxy1 hy1conj
    · intro y hy ih
      have hyN : y ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)) := hB_norm y hy
      have hyInvN : y⁻¹ ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)) :=
        (Subgroup.normalizer (Snext : Set (Variety.Point K))).inv_mem hyN
      have hyx : ⁅y, x⁆ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
        simpa [commutatorElement_inv] using
          (RelativeRootSeries D e base.support coeff J (i + 1)).inv_mem ih
      have hyinvconj : y⁻¹ * ⁅y, x⁆ * y⁻¹⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
        exact (Subgroup.mem_normalizer_iff.mp hyInvN (⁅y, x⁆)).mp hyx
      have hyinvEq : y⁻¹ * ⁅y, x⁆ * y = ⁅x, y⁻¹⁆ := by
        simp [commutatorElement_def, mul_assoc]
      simpa [hyinvEq] using hyinvconj
  · intro x hx
    simp
  · intro x₁ x₂ hx₁ hx₂ ih₁ ih₂ y hy
    have hx1norm : x₁ ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)) := hA_norm x₁ hx₁
    have hx1conj : x₁ * ⁅x₂, y⁆ * x₁⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
      exact (Subgroup.mem_normalizer_iff.mp hx1norm (⁅x₂, y⁆)).mp (ih₂ y hy)
    have hxy1 : ⁅x₁, y⁆ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := ih₁ y hy
    rw [commutatorElement_mul_left_eq_conj_mul]
    simpa [mul_assoc] using
      (RelativeRootSeries D e base.support coeff J (i + 1)).mul_mem hx1conj hxy1
  · intro x hx ih y hy
    have hxN : x ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)) := hA_norm x hx
    have hxInvN : x⁻¹ ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)) :=
      (Subgroup.normalizer (Snext : Set (Variety.Point K))).inv_mem hxN
    have hyx : ⁅y, x⁆ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
      simpa [commutatorElement_inv] using
        (RelativeRootSeries D e base.support coeff J (i + 1)).inv_mem (ih y hy)
    have hxinvy : x⁻¹ * ⁅y, x⁆ * x⁻¹⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
      exact (Subgroup.mem_normalizer_iff.mp hxInvN (⁅y, x⁆)).mp hyx
    have hxinvyEq : x⁻¹ * ⁅y, x⁆ * x = ⁅x⁻¹, y⁆ := by
      simp [commutatorElement_inv_left]
    simpa [hxinvyEq] using hxinvy

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_next_le_sup_commutator_of_one_one_nonzero_of_subset
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (hJ : e '' J ⊆ base.support)
    (hCoeff11 : ∀ {α β : D.Root} {q : ChevalleyCommutatorTerm D.Root},
      AreLinearlyIndependentRoots D P e α β →
      IsValidChevalleyCommutatorTerm D P e α β q →
      q.i = 1 → q.j = 1 →
      ∀ c : k, HasExpectedChevalleyCoefficient D P e α β q c → c ≠ 0)
    (i : ℕ) (hi : 0 < i) :
    RelativeRootSeries D e base.support coeff J (i + 1) ≤
      ⁅RelativeRootSeries D e base.support coeff J i,
        RelativeRootSeries D e base.support coeff J 1⁆ ⊔
      RelativeRootSeries D e base.support coeff J (i + 2) := by
  let Si : Subgroup (Variety.Point K) :=
    RelativeRootSeries D e base.support coeff J i
  let S1 : Subgroup (Variety.Point K) :=
    RelativeRootSeries D e base.support coeff J 1
  let Snext : Subgroup (Variety.Point K) :=
    RelativeRootSeries D e base.support coeff J (i + 1)
  let Snextnext : Subgroup (Variety.Point K) :=
    RelativeRootSeries D e base.support coeff J (i + 2)
  change Snext ≤ ⁅Si, S1⁆ ⊔ Snextnext
  dsimp [Snext, RelativeRootSeries]
  rw [RootSubgroupGenerated]
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
  rcases hx with ⟨α, hα, hxα⟩
  have hαtwo : (2 : ℤ) ≤
      RelativeRootHeight coeff base.support (e '' J) (e α) := by
    omega
  obtain ⟨βι, γι, hdecomp, hβheight⟩ :=
    relativeRootHeight_split_of_ge_two P base (e '' J) hJ coeff hCoeff
      (e α) hαtwo
  let β : D.Root := e.symm βι
  let γ : D.Root := e.symm γι
  have hdecomp' : P.root (e α) = P.root (e β) + P.root (e γ) := by
    simpa [β, γ] using hdecomp
  have hβheight' : RelativeRootHeight coeff base.support
      (e '' J) (e β) = 1 := by
    simpa [β] using hβheight
  have hγheight0 : (i : ℤ) ≤
      RelativeRootHeight coeff base.support (e '' J) γι := by
    have hadd := relativeRootHeight_eq_add_of_root_eq_add
      P base (e '' J) coeff hCoeff hdecomp
    have hα' : RelativeRootHeight coeff base.support (e '' J) (e α) =
        RelativeRootHeight coeff base.support (e '' J) βι +
          RelativeRootHeight coeff base.support (e '' J) γι := hadd
    rw [hβheight] at hα'
    omega
  have hγheight : (i : ℤ) ≤
      RelativeRootHeight coeff base.support (e '' J) (e γ) := by
    simpa [γ] using hγheight0
  have hLI : AreLinearlyIndependentRoots D P e β γ := by
    have hrootmem : P.root (e α) ∈ Set.range P.root := ⟨e α, rfl⟩
    have hlin : LinearIndependent R ![P.root (e β), P.root (e γ)] := by
      apply P.linearIndependent_of_add_mem_range_root
      rw [← hdecomp']
      exact hrootmem
    simpa [AreLinearlyIndependentRoots] using (LinearIndependent.pair_iff.mp hlin)
  let q : ChevalleyCommutatorTerm D.Root := ⟨1, 1, α⟩
  have hqsum : q.i + q.j = 2 := by simp [q]
  have hqi : q.i = 1 := by simp [q]
  have hqj : q.j = 1 := by simp [q]
  have hqvalid : IsValidChevalleyCommutatorTerm D P e β γ q := by
    refine ⟨by simp [q], by simp [q], ?_⟩
    simpa [q] using hdecomp'
  rcases hC.2.2.2.2.1 β γ hLI with
    ⟨order, cfun, hnodup, hpairwise, hvalid, hexpected, hformula⟩
  have hqorder : q ∈ order := (hvalid q).mpr hqvalid
  have horder_head : ∃ tail, order = q :: tail := by
    induction order with
    | nil => simp at hqorder
    | cons p l ih =>
      by_cases hpq : p = q
      · exact ⟨l, by simp [hpq]⟩
      · have hqtail : q ∈ l :=
          (List.mem_cons.mp hqorder).resolve_left (Ne.symm hpq)
        have hpcases := List.pairwise_cons.mp hpairwise
        have hpvalid := (hvalid p).mp (by simp)
        have hpdeg : 2 ≤ p.i + p.j := by
          have hpi := hpvalid.1
          have hpj := hpvalid.2.1
          omega
        have hpqdeg : p.i + p.j ≤ q.i + q.j := hpcases.1 q hqtail
        have hpdegEq : p.i + p.j = q.i + q.j := by omega
        have hp_i : p.i = 1 := by
          have := hpvalid.1
          have := hpvalid.2.1
          have hsum : p.i + p.j = 2 := by
            rw [hpdegEq, hqsum]
          omega
        have hp_j : p.j = 1 := by
          have hsum : p.i + p.j = 2 := by
            rw [hpdegEq, hqsum]
          omega
        have hproot : p.root = α := by
          apply e.injective
          apply P.root.injective
          rw [hpvalid.2.2, hqvalid.2.2]
          simp [hp_i, hp_j, q]
        have hpqeq : p = q := by
          cases p
          simp_all [q]
        exact (hpq hpqeq).elim
  obtain ⟨tail, rfl⟩ := horder_head
  have htailStrict : ∀ r ∈ tail, q.i + q.j < r.i + r.j := by
    intro r hr
    have hqr := (List.pairwise_cons.mp hpairwise).1 r hr
    by_contra hnot
    have hqrdeg : q.i + q.j ≤ r.i + r.j := hqr
    have hrdEq : r.i + r.j = q.i + q.j :=
      Nat.le_antisymm (Nat.le_of_not_gt hnot) hqrdeg
    have hrvalid := (hvalid r).mp (by simp [hr])
    have hri : r.i = 1 := by
      have hsum : r.i + r.j = 2 := by
        simpa [hqi, hqj] using hrdEq
      have hri_pos := hrvalid.1
      have hrj_pos := hrvalid.2.1
      omega
    have hrj : r.j = 1 := by
      have hsum : r.i + r.j = 2 := by
        simpa [hqi, hqj] using hrdEq
      have hri_pos := hrvalid.1
      have hrj_pos := hrvalid.2.1
      omega
    have hrroot : r.root = α := by
      apply e.injective
      apply P.root.injective
      rw [hrvalid.2.2, hqvalid.2.2]
      simp [hri, hrj, q]
    have hreq : r = q := by
      cases r
      simp_all [q]
    have hqnotmem : q ∉ tail := (List.nodup_cons.mp hnodup).1
    exact hqnotmem (by simpa [hreq] using hr)
  have htail_mem : ∀ r ∈ tail, ∀ s : k,
      C.x r.root s ∈ Snextnext := by
    intro r hr s
    have hrvalid := (hvalid r).mp (by simp [hr])
    have hrheight := relativeRootHeight_of_validChevalleyCommutatorTerm
      D P e base (e '' J) coeff hCoeff r hrvalid
    have hrh : (i + 2 : ℤ) ≤
        RelativeRootHeight coeff base.support (e '' J) (e r.root) := by
      have hri : (1 : ℤ) ≤ r.i := by exact_mod_cast (Nat.succ_le_of_lt hrvalid.1)
      have hrj : (1 : ℤ) ≤ r.j := by exact_mod_cast (Nat.succ_le_of_lt hrvalid.2.1)
      have hdeg : 3 ≤ r.i + r.j := by
        have := htailStrict r hr
        omega
      rw [hrheight]
      have hβh : RelativeRootHeight coeff base.support (e '' J) (e β) = 1 := hβheight'
      have hγh : (i : ℤ) ≤
          RelativeRootHeight coeff base.support (e '' J) (e γ) := hγheight
      nlinarith
    dsimp [Snextnext, RelativeRootSeries]
    rw [RootSubgroupGenerated]
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨r.root, hrh, by
      rw [← (hC.1 r.root).2]
      exact Set.mem_range_self _⟩
  have hparam_ne : cfun q ≠ 0 :=
    hCoeff11 hLI hqvalid (by simp [q]) (by simp [q]) (cfun q) (hexpected q hqorder)
  have hβheight_ge : (1 : ℤ) ≤
      RelativeRootHeight coeff base.support (e '' J) (e β) := by
    omega
  have hrootRange : (D.rootSubgroup α : Set (Variety.Point K)) = Set.range (C.x α) := by
    simpa using (hC.1 α).2.symm
  rw [hrootRange] at hxα
  rcases hxα with ⟨t, rfl⟩
  let u : k := (cfun q)⁻¹ * t
  have htail_prod :
      ChevalleyCommutatorTermWordProduct C
        (tail.map fun r => (r, cfun r * 1 ^ r.i * u ^ r.j)) ∈ Snextnext := by
    apply Subgroup.list_prod_mem
    intro z hz
    rw [List.mem_map] at hz
    rcases hz with ⟨z, hz, rfl⟩
    rw [List.mem_map] at hz
    rcases hz with ⟨r, hr, rfl⟩
    exact htail_mem r hr _
  have hcomm : ⁅C.x β 1, C.x γ u⁆ ∈ ⁅Si, S1⁆ := by
    have hraw : ⁅C.x β 1, C.x γ u⁆ ∈ ⁅S1, Si⁆ := by
      apply Subgroup.commutator_mem_commutator
      · apply Subgroup.subset_closure
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨β, hβheight_ge, by
          rw [← (hC.1 β).2]
          exact Set.mem_range_self _⟩
      · apply Subgroup.subset_closure
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨γ, hγheight, by
          rw [← (hC.1 γ).2]
          exact Set.mem_range_self _⟩
    simpa only [Subgroup.commutator_comm Si S1] using hraw
  have hcommRaw :
      (C.x β 1)⁻¹ * (C.x γ u)⁻¹ * C.x β 1 * C.x γ u ∈ ⁅Si, S1⁆ := by
    have hraw : ⁅(C.x β 1)⁻¹, (C.x γ u)⁻¹⁆ ∈ ⁅S1, Si⁆ := by
      apply Subgroup.commutator_mem_commutator
      · exact (S1.inv_mem (by
          apply Subgroup.subset_closure
          simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
          exact ⟨β, hβheight_ge, by
            rw [← (hC.1 β).2]
            exact Set.mem_range_self _⟩))
      · exact (Si.inv_mem (by
          apply Subgroup.subset_closure
          simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
          exact ⟨γ, hγheight, by
            rw [← (hC.1 γ).2]
            exact Set.mem_range_self _⟩))
    have hraw' : ⁅(C.x β 1)⁻¹, (C.x γ u)⁻¹⁆ ∈ ⁅Si, S1⁆ := by
      simpa only [Subgroup.commutator_comm Si S1] using hraw
    simpa [commutatorElement_def] using hraw'
  have hformula' := hformula 1 u
  simp only [List.map_cons, List.prod_cons] at hformula'
  have hhead : cfun q * (1 : k) ^ q.i * u ^ q.j = t := by
    simp [q, u, hparam_ne]
  rw [hhead] at hformula'
  have hformula'' :
      (C.x β 1)⁻¹ * (C.x γ u)⁻¹ * C.x β 1 * C.x γ u =
        C.x α t * ChevalleyCommutatorTermWordProduct C
          (tail.map fun r => (r, cfun r * 1 ^ r.i * u ^ r.j)) := by
    simpa [q, ChevalleyCommutatorTermWordProduct, List.map_map, Function.comp_def] using hformula'
  have hsup : C.x α t ∈ ⁅Si, S1⁆ ⊔ Snextnext := by
    have hprod_mem : C.x α t *
        ChevalleyCommutatorTermWordProduct C
          (tail.map fun r => (r, cfun r * 1 ^ r.i * u ^ r.j)) ∈
        ⁅Si, S1⁆ ⊔ Snextnext := by
      rw [← hformula'']
      exact (le_sup_left : ⁅Si, S1⁆ ≤ ⁅Si, S1⁆ ⊔ Snextnext) hcommRaw
    have htail_sup : ChevalleyCommutatorTermWordProduct C
        (tail.map fun r => (r, cfun r * 1 ^ r.i * u ^ r.j)) ∈ ⁅Si, S1⁆ ⊔ Snextnext :=
      (show Snextnext ≤ ⁅Si, S1⁆ ⊔ Snextnext from le_sup_right) htail_prod
    have hprod_inv := (⁅Si, S1⁆ ⊔ Snextnext).inv_mem htail_sup
    simpa [mul_assoc] using (⁅Si, S1⁆ ⊔ Snextnext).mul_mem hprod_mem hprod_inv
  exact hsup

omit [IsAlgClosed k] in
/-- The ordinary-height specialization of
`relativeRootSeries_next_le_sup_commutator_of_one_one_nonzero_of_subset`. -/
public theorem relativeRootSeries_next_le_sup_commutator_of_one_one_nonzero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (hCoeff11 : ∀ {α β : D.Root} {q : ChevalleyCommutatorTerm D.Root},
      AreLinearlyIndependentRoots D P e α β →
      IsValidChevalleyCommutatorTerm D P e α β q →
      q.i = 1 → q.j = 1 →
      ∀ c : k, HasExpectedChevalleyCoefficient D P e α β q c → c ≠ 0)
    (i : ℕ) (hi : 0 < i) :
    RelativeRootSeries D e base.support coeff (∅ : Set D.Root) (i + 1) ≤
      ⁅RelativeRootSeries D e base.support coeff (∅ : Set D.Root) i,
        RelativeRootSeries D e base.support coeff (∅ : Set D.Root) 1⁆ ⊔
      RelativeRootSeries D e base.support coeff (∅ : Set D.Root) (i + 2) := by
  exact relativeRootSeries_next_le_sup_commutator_of_one_one_nonzero_of_subset
    D C P e base coeff hCoeff hC (∅ : Set D.Root) (by simp) hCoeff11 i hi

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_commutator_same_layer_le_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i) :
    ⁅RelativeRootSeries D e base.support coeff J i,
      RelativeRootSeries D e base.support coeff J i⁆ ≤
        RelativeRootSeries D e base.support coeff J (i + 1) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : (1 : ℕ) ≤ i := Nat.succ_le_of_lt hi
  have hy1 : y ∈ RelativeRootSeries D e base.support coeff J 1 := by
    exact (relativeRootSeries_antitone D e base.support coeff J h1) hy
  exact (Subgroup.commutator_le.mp
      (relativeRootSeries_commutator_series_le (D := D) (C := C) (P := P)
        (e := e) (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC)
        (J := J) (i := i) hi)) x hx y hy1

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_commutator_with_subgroup_eq_one_le_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i)
    (U : Subgroup (Variety.Point K))
    (hU : U = RelativeRootSeries D e base.support coeff J 1) :
    ⁅RelativeRootSeries D e base.support coeff J i, U⁆ ≤
      RelativeRootSeries D e base.support coeff J (i + 1) := by
  rw [hU]
  exact relativeRootSeries_commutator_series_le (D := D) (C := C) (P := P)
    (e := e) (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC)
    (J := J) (i := i) hi

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_le_normalizer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i) :
    RelativeRootSeries D e base.support coeff J i ≤
      Subgroup.normalizer (RelativeRootSeries D e base.support coeff J (i + 1) :
        Set (Variety.Point K)) := by
  classical
  let Snext : Subgroup (Variety.Point K) := RelativeRootSeries D e base.support coeff J (i + 1)
  intro x hx
  rw [RelativeRootSeries, RootSubgroupGenerated] at hx
  refine Subgroup.closure_induction
    (p := fun x _ => x ∈ Subgroup.normalizer (Snext : Set (Variety.Point K)))
    (k := ⋃ α ∈ {α | (i : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α)},
      ↑(D.rootSubgroup α : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hx
  · intro x hx
    have hx' : ∃ α : D.Root, ∃ _ : (i : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α),
        x ∈ (D.rootSubgroup α : Set (Variety.Point K)) := by
      simpa only [Set.mem_iUnion, Set.mem_ofPred_eq] using hx
    rcases hx' with ⟨α, hα, hxα⟩
    have h1 : (1 : ℕ) ≤ i + 1 := by omega
    have hSnext_le : Snext ≤ RelativeRootSeries D e base.support coeff J 1 := by
      exact relativeRootSeries_antitone D e base.support coeff J h1
    have hrootConj :
        ∀ u ∈ (D.rootSubgroup α : Set (Variety.Point K)),
          ∀ z ∈ Snext, u * z * u⁻¹ ∈ Snext := by
      intro u hu z hz
      have hz1 : z ∈ RelativeRootSeries D e base.support coeff J 1 := hSnext_le hz
      have huSeries : u ∈ RelativeRootSeries D e base.support coeff J i := by
        rw [RelativeRootSeries, RootSubgroupGenerated]
        apply Subgroup.subset_closure
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨α, hα, hu⟩
      have hcomm : ⁅u, z⁆ ∈ Snext := by
        exact (relativeRootSeries_commutator_series_le (D := D) (C := C) (P := P)
          (e := e) (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC)
          (J := J) (i := i) hi) (Subgroup.commutator_mem_commutator huSeries hz1)
      have hmul : (MulAut.conj u) z ∈ Snext := by
        rw [conj_eq_commutatorElement_mul]
        exact Snext.mul_mem hcomm hz
      simpa [MulAut.conj_apply] using hmul
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hrootConj x hxα z hz
    · intro hz
      have hxInvα : x⁻¹ ∈ (D.rootSubgroup α : Set (Variety.Point K)) := (D.rootSubgroup α).inv_mem hxα
      have hzinv : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ ∈ Snext :=
        hrootConj x⁻¹ hxInvα (x * z * x⁻¹) hz
      simpa [mul_assoc, inv_inv] using hzinv
  · exact (Subgroup.normalizer (Snext : Set (Variety.Point K))).one_mem
  · intro x₁ x₂ hx₁ hx₂ ih₁ ih₂
    exact (Subgroup.normalizer (Snext : Set (Variety.Point K))).mul_mem ih₁ ih₂
  · intro x hx ih
    exact (Subgroup.normalizer (Snext : Set (Variety.Point K))).inv_mem ih

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Finite descending induction upgrades the one-step reverse inclusion to exact
commutator layers.  The coefficient nonvanishing premise is kept explicit so
this core theorem does not encode a conclusion in a structure or definition. -/
public theorem relativeRootSeries_eq_commutator_of_one_one_nonzero_of_subset
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (hJ : e '' J ⊆ base.support)
    (hCoeff11 : ∀ {α β : D.Root} {q : ChevalleyCommutatorTerm D.Root},
      AreLinearlyIndependentRoots D P e α β →
      IsValidChevalleyCommutatorTerm D P e α β q →
      q.i = 1 → q.j = 1 →
      ∀ c : k, HasExpectedChevalleyCoefficient D P e α β q c → c ≠ 0)
    (c : ℕ)
    (hTerminal :
      RelativeRootSeries D e base.support coeff J (c + 1) = ⊥) :
    ∀ i, 0 < i → i ≤ c →
      ⁅RelativeRootSeries D e base.support coeff J i,
        RelativeRootSeries D e base.support coeff J 1⁆ =
      RelativeRootSeries D e base.support coeff J (i + 1) := by
  let S : ℕ → Subgroup (Variety.Point K) := fun i =>
    RelativeRootSeries D e base.support coeff J i
  have hAnti : ∀ i, 0 < i → S (i + 1) ≤ S i := by
    intro i hi
    simpa [S] using
      (relativeRootSeries_antitone D e base.support coeff J
        (Nat.le_succ i))
  have hCommLe : ∀ i, 0 < i → ⁅S i, S 1⁆ ≤ S (i + 1) := by
    intro i hi
    simpa [S] using
      (relativeRootSeries_commutator_series_le D C P e base coeff hCoeff hC
        J i hi)
  have hMod : ∀ i, 0 < i → i ≤ c → S (i + 1) ≤ ⁅S i, S 1⁆ ⊔ S (i + 2) := by
    intro i hi hile
    simpa [S] using
      (relativeRootSeries_next_le_sup_commutator_of_one_one_nonzero_of_subset
        D C P e base coeff hCoeff hC J hJ hCoeff11 i hi)
  have hTerminal' : S (c + 1) = ⊥ := by
    simpa [S] using hTerminal
  simpa [S] using
    (subgroupSeries_commutator_eq_of_mod_next (S 1) S c hAnti hCommLe hMod hTerminal')

omit [IsAlgClosed k] in
/-- The ordinary-height specialization of
`relativeRootSeries_eq_commutator_of_one_one_nonzero_of_subset`. -/
public theorem relativeRootSeries_eq_commutator_of_one_one_nonzero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (hCoeff11 : ∀ {α β : D.Root} {q : ChevalleyCommutatorTerm D.Root},
      AreLinearlyIndependentRoots D P e α β →
      IsValidChevalleyCommutatorTerm D P e α β q →
      q.i = 1 → q.j = 1 →
      ∀ c : k, HasExpectedChevalleyCoefficient D P e α β q c → c ≠ 0)
    (c : ℕ)
    (hTerminal :
      RelativeRootSeries D e base.support coeff (∅ : Set D.Root) (c + 1) = ⊥) :
    ∀ i, 0 < i → i ≤ c →
      ⁅RelativeRootSeries D e base.support coeff (∅ : Set D.Root) i,
        RelativeRootSeries D e base.support coeff (∅ : Set D.Root) 1⁆ =
      RelativeRootSeries D e base.support coeff (∅ : Set D.Root) (i + 1) := by
  exact relativeRootSeries_eq_commutator_of_one_one_nonzero_of_subset
    D C P e base coeff hCoeff hC (∅ : Set D.Root) (by simp) hCoeff11 c hTerminal

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_conj_mem_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i) :
    ∀ x ∈ RelativeRootSeries D e base.support coeff J i,
      ∀ z ∈ RelativeRootSeries D e base.support coeff J (i + 1),
        x * z * x⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
  intro x hx z hz
  exact (Subgroup.mem_normalizer_iff.mp
    (relativeRootSeries_le_normalizer (D := D) (C := C) (P := P) (e := e)
      (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC) (J := J)
      (i := i) hi hx) z).1 hz

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_next_layer_normal
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i) :
    ((RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
      (RelativeRootSeries D e base.support coeff J i)).Normal := by
  exact Subgroup.normal_subgroupOf_of_le_normalizer
    (relativeRootSeries_le_normalizer (D := D) (C := C) (P := P)
      (e := e) (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC)
      (J := J) (i := i) hi)

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_conj_pow_mem_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i) :
    ∀ x ∈ RelativeRootSeries D e base.support coeff J i,
      ∀ z ∈ RelativeRootSeries D e base.support coeff J (i + 1),
        ∀ n : ℕ, x ^ n * z * (x ^ n)⁻¹ ∈
          RelativeRootSeries D e base.support coeff J (i + 1) := by
  intro x hx z hz n
  induction n with
  | zero =>
      simpa
  | succ n ih =>
      have hconj :
          x * (x ^ n * z * (x ^ n)⁻¹) * x⁻¹ ∈
            RelativeRootSeries D e base.support coeff J (i + 1) :=
        relativeRootSeries_conj_mem_next_layer (D := D) (C := C) (P := P)
          (e := e) (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC)
          (J := J) (i := i) hi x hx (x ^ n * z * (x ^ n)⁻¹) ih
      have hpow :
          x ^ (n + 1) * z * (x ^ (n + 1))⁻¹ =
            x * (x ^ n * z * (x ^ n)⁻¹) * x⁻¹ := by
        rw [pow_succ]
        group
      simpa [hpow] using hconj

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_mul_conj_mem_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i)
    {x y z : Variety.Point K}
    (hx : x ∈ RelativeRootSeries D e base.support coeff J i)
    (hy : y ∈ RelativeRootSeries D e base.support coeff J i)
    (hz : z ∈ RelativeRootSeries D e base.support coeff J (i + 1)) :
    (x * y) * z * (x * y)⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
  have hnormx := relativeRootSeries_le_normalizer D C P e base coeff hCoeff hC J i hi hx
  have hnormy := relativeRootSeries_le_normalizer D C P e base coeff hCoeff hC J i hi hy
  have hnormxy := (Subgroup.normalizer
      (RelativeRootSeries D e base.support coeff J (i + 1) : Set (Variety.Point K))).mul_mem hnormx hnormy
  exact (Subgroup.mem_normalizer_iff.mp hnormxy z).1 hz

end
end Theory.AlgebraicGroup
