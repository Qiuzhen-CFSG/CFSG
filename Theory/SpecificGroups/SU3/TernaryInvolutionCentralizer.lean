module

public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Theory.SpecificGroups.SU3.UnitaryTwoResidual
public import ABG.ChapterII.Section2.SpecialUnitaryEquivSL2
public import Theory.SpecificGroups.SL2.BinaryTetrahedral

/-!
# Solvability of involution centralizers in PSU₃(3)

The full special-unitary centralizer is GU₂(3). Its determinant kernel is
SU₂(3), identified with the solvable binary tetrahedral group SL₂(3).
The central scalar kernel of exponent three allows every projective
centralizer element to lift. The resulting surjection proves solvability
in the actual projective image. Form and field transport retain an arbitrary
nondegenerate Hermitian form and its specified Frobenius conjugation.

Source: Aschbacher--Smith, A.3.21(a), printed p.55; the solvable parameter
in the inner-centralizer argument for E.1.14(7), printed p.214.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open Matrix.SU3.InnerThreeRank
namespace Matrix.SU3.TernaryCentralizer

private theorem sl23_solvable :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  let hQ : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by norm_num [QuaternionGroup.card])
  let : Group.IsNilpotent (QuaternionGroup 2) := hQ.isNilpotent
  let : Group.IsSolvable
      (QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
        Multiplicative (ZMod 3)) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl
      SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge
  exact Group.isSolvable_of_surjective
    (f := GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.toMonoidHom)
    GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.surjective

/-- The full centralizer in the standard projective matrix image is solvable. -/
theorem standard_involution_centralizer_solvable
    (k : ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 3 1 one_ne_zero))
    (hk : orderOf k = 2) :
    Group.IsSolvable (centralizer ({k} : Set
      (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 3 1 one_ne_zero)))) := by
  let J3 := ABG.unitaryForm 3 3 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 3 1 one_ne_zero
  let q := J3.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J3.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨z, hz, rfl⟩ := exists_involution_lift_of_cube_kernel q
    J3.specialToProjective_surjective hcube k hk
  let C := centralizer ({z} : Set J3.specialSubgroup)
  have hmap : C.map q = centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J3)) :=
    map_centralizer_of_central_cube_kernel q J3.specialToProjective_surjective
      J3.specialToProjective_ker_le_center hcube z (by simpa only [hz] using pow_orderOf_eq_one z)
  let ep := MulEquiv.subgroupCongr hmap
  let f := ep.toMonoidHom.comp (q.subgroupMap C)
  have hf : Function.Surjective f := ep.surjective.comp (q.subgroupMap_surjective C)
  let : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := sl23_solvable
  let e := J2.unitaryDetKernelEquiv.trans
    ((ABG.specialUnitaryTwo_equiv_sl2 3 1 (by decide) one_ne_zero).trans
      (GorensteinWalter.sl2RingEquiv (GaloisField.equivZmodP 3).toRingEquiv))
  let : Group.IsSolvable J2.unitaryDet.ker :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsSolvable J2.unitarySubgroup :=
    Group.isSolvable_of_ker_le_range J2.unitaryDet.ker.subtype J2.unitaryDet
      (by rw [J2.unitaryDet.ker.range_subtype])
  let ec : C ≃* J2.unitarySubgroup := (Matrix.SU3.involutionCentralizerEquiv (by decide : 3 ≠ 2)
    (GaloisField.card 3 (2 * 1) (by decide)) J3 J2 rfl rfl
    (by intro x; simp only [J3, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one])
    (by intro x; simp only [J2, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]) z hz).symm
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (f := ec.toMonoidHom) ec.injective
  exact Group.isSolvable_of_surjective hf

/-- The calculation holds for every allowed Hermitian form over a field of order nine. -/
theorem involution_centralizer_solvable
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = 3 ^ 2) (hc : ∀ x, J.conj x = x ^ 3)
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : orderOf z = 2) :
    Group.IsSolvable (centralizer ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨e⟩ := exists_projective_equiv_standard 3 F J hcard hc
  let : Group.IsSolvable (centralizer ({e z} : Set _)) :=
    standard_involution_centralizer_solvable (e z) ((e.orderOf_eq z).trans hz)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (centralizerEquiv e z).toMonoidHom) (centralizerEquiv e z).injective

end Matrix.SU3.TernaryCentralizer
