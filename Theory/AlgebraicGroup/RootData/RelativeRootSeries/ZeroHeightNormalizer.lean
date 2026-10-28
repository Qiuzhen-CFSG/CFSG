module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Basic
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.RelativeRootNeg

universe u

set_option linter.style.haveILetI false

open scoped commutatorElement

/-!
Normalization of positive relative-root layers by zero-height root subgroups.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private lemma rootSubgroup_commutator_le_relativeRootSeries_of_height_zero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i) {α β : D.Root}
    (hα : RelativeRootHeight coeff base.support (e '' J) (e α) = 0)
    (hβ : (i : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e β)) :
    ⁅(D.rootSubgroup α).toSubgroup, (D.rootSubgroup β).toSubgroup⁆ ≤
      RelativeRootSeries D e base.support coeff J i := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hrootα : (D.rootSubgroup α : Set (Variety.Point K)) =
      Set.range (C.x α) := by
    simpa using (hC.1 α).2.symm
  have hrootβ : (D.rootSubgroup β : Set (Variety.Point K)) =
      Set.range (C.x β) := by
    simpa using (hC.1 β).2.symm
  have hx' : x ∈ (D.rootSubgroup α).toClosedSubgroup.toSubgroup := by
    simpa using hx
  change x ∈ (D.rootSubgroup α : Set (Variety.Point K)) at hx'
  rw [hrootα] at hx'
  obtain ⟨t, rfl⟩ := hx'
  have hy' : y ∈ (D.rootSubgroup β).toClosedSubgroup.toSubgroup := by
    simpa using hy
  change y ∈ (D.rootSubgroup β : Set (Variety.Point K)) at hy'
  rw [hrootβ] at hy'
  obtain ⟨s, rfl⟩ := hy'
  have hαβ : α ≠ β := by
    intro hEq
    subst β
    omega
  letI := P.indexNeg
  have hnotopp : P.root (e α) ≠ -P.root (e β) := by
    intro hneg
    have hidx : e α = P.reflectionPerm (e β) (e β) :=
      P.root_eq_neg_iff.mp hneg
    have hnegHeight :
        RelativeRootHeight coeff base.support (e '' J) (e α) =
          -RelativeRootHeight coeff base.support (e '' J) (e β) := by
      rw [hidx]
      exact relativeRootHeight_reflectionPerm_self P base (e '' J) coeff
        hCoeff (e β)
    rw [hα] at hnegHeight
    omega
  have hne : e α ≠ e β := fun h => hαβ (e.injective h)
  have hlin : LinearIndependent R ![P.root (e α), P.root (e β)] :=
    RootPairing.IsReduced.linearIndependent (P := P) hne hnotopp
  have hLI : AreLinearlyIndependentRoots D P e α β := by
    simpa [AreLinearlyIndependentRoots] using
      (LinearIndependent.pair_iff.mp hlin)
  rcases hC.2.2.2.2.1 α β hLI with
    ⟨order, c, -, -, hvalid, -, hformula⟩
  have hterm (a b : k) (q : ChevalleyCommutatorTerm D.Root)
      (hq : q ∈ order) :
      C.x q.root (c q * a ^ q.i * b ^ q.j) ∈
        RelativeRootSeries D e base.support coeff J i := by
    have hqvalid : IsValidChevalleyCommutatorTerm D P e α β q :=
      (hvalid q).mp hq
    have hqheight : (i : ℤ) ≤
        RelativeRootHeight coeff base.support (e '' J) (e q.root) := by
      rw [relativeRootHeight_of_validChevalleyCommutatorTerm D P e base
        (e '' J) coeff hCoeff q hqvalid, hα]
      have hqj : (1 : ℤ) ≤ q.j := by
        exact_mod_cast Nat.succ_le_of_lt hqvalid.2.1
      nlinarith
    have hrootq : (D.rootSubgroup q.root : Set (Variety.Point K)) =
        Set.range (C.x q.root) := by
      simpa using (hC.1 q.root).2.symm
    rw [RelativeRootSeries, RootSubgroupGenerated]
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨q.root, hqheight, hrootq ▸ Set.mem_range_self _⟩
  have hprod :
      (order.map fun q => C.x q.root
        (c q * (-t) ^ q.i * (-s) ^ q.j)).prod ∈
        RelativeRootSeries D e base.support coeff J i := by
    apply Subgroup.list_prod_mem
    intro z hz
    rw [List.mem_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    exact hterm (-t) (-s) q hq
  have hcommRaw :
      (C.x α (-t))⁻¹ * (C.x β (-s))⁻¹ * C.x α (-t) * C.x β (-s) ∈
        RelativeRootSeries D e base.support coeff J i := by
    rw [hformula (-t) (-s)]
    exact hprod
  have hzeroα : C.x α 0 = 1 := by
    simpa using (hC.2.2.2.1 α 0 0)
  have hzeroβ : C.x β 0 = 1 := by
    simpa using (hC.2.2.2.1 β 0 0)
  have hxinv : C.x α (-t) = (C.x α t)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [hC.2.2.2.1 α (-t) t]
    simpa using hzeroα
  have hyinv : C.x β (-s) = (C.x β s)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [hC.2.2.2.1 β (-s) s]
    simpa using hzeroβ
  simpa [hxinv, hyinv, commutatorElement_def, mul_assoc] using hcommRaw

/-- A root subgroup of relative height zero normalizes every positive
relative-root layer. -/
public lemma rootSubgroup_le_normalizer_relativeRootSeries_of_height_zero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i) (α : D.Root)
    (hα : RelativeRootHeight coeff base.support (e '' J) (e α) = 0) :
    (D.rootSubgroup α).toSubgroup ≤
      Subgroup.normalizer
        (RelativeRootSeries D e base.support coeff J i :
          Set (Variety.Point K)) := by
  classical
  let S : Subgroup (Variety.Point K) :=
    RelativeRootSeries D e base.support coeff J i
  have hrootConj (x : Variety.Point K) (hx : x ∈ D.rootSubgroup α) :
      ∀ z ∈ S, x * z * x⁻¹ ∈ S := by
    intro z hz
    change z ∈ RelativeRootSeries D e base.support coeff J i at hz
    rw [RelativeRootSeries, RootSubgroupGenerated] at hz
    refine Subgroup.closure_induction
      (p := fun z _ => x * z * x⁻¹ ∈ S)
      (k := ⋃ β ∈ {β | (i : ℤ) ≤
        RelativeRootHeight coeff base.support (e '' J) (e β)},
        ↑(D.rootSubgroup β : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hz
    · intro y hy
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hy
      rcases hy with ⟨β, hβ, hyβ⟩
      have hcomm : ⁅x, y⁆ ∈ S :=
        (rootSubgroup_commutator_le_relativeRootSeries_of_height_zero
          D C P e base coeff hCoeff hC J i hi hα hβ)
          (Subgroup.commutator_mem_commutator hx hyβ)
      have hyS : y ∈ S := by
        change y ∈ RelativeRootSeries D e base.support coeff J i
        rw [RelativeRootSeries, RootSubgroupGenerated]
        apply Subgroup.subset_closure
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨β, hβ, hyβ⟩
      change (MulAut.conj x) y ∈ S
      rw [conj_eq_commutatorElement_mul]
      exact S.mul_mem hcomm hyS
    · simp [S]
    · intro y z hy hz ihy ihz
      simpa [mul_assoc] using S.mul_mem ihy ihz
    · intro y hy ihy
      simpa [mul_assoc] using S.inv_mem ihy
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hrootConj x hx z
  · intro hz
    have hxinv : x⁻¹ ∈ D.rootSubgroup α := (D.rootSubgroup α).inv_mem hx
    have hback := hrootConj x⁻¹ hxinv (x * z * x⁻¹) hz
    simpa [mul_assoc] using hback

end Theory.AlgebraicGroup
