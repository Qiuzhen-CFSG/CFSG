module
public import Theory.SpecificGroups.SL2.BinaryTetrahedral
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The binary tetrahedral central quotient

The explicit Q8 semidirect C3 model has center of order two and central
quotient of order twelve. Transporting its center by the matrix-model
equivalence identifies this quotient with PSL2(ZMod3). Generator relations
and a three-generator extensionality theorem support construction of maps
from central extensions, using finite quaternion normal forms.

This supplies the finite-model calculations for the q=3 Schur-cover step
of ABG II.3 Proposition 2, using the extracted GLS3 5.2.4 matrix model.
-/

public section
namespace GLS3.Chapter5.SchurPresentation

abbrev BinaryTetrahedral :=
  QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)

abbrev binaryI : BinaryTetrahedral := SemidirectProduct.inl (QuaternionGroup.a 1)
abbrev binaryJ : BinaryTetrahedral := SemidirectProduct.inl (QuaternionGroup.xa 0)
abbrev binaryT : BinaryTetrahedral := SemidirectProduct.inr (Multiplicative.ofAdd 1)
abbrev BinaryTetrahedralCentralQuotient :=
  BinaryTetrahedral ⧸ Subgroup.center BinaryTetrahedral

private instance binaryFintype : Fintype BinaryTetrahedral :=
  Fintype.ofEquiv (QuaternionGroup 2 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

theorem binaryTetrahedral_card : Nat.card BinaryTetrahedral = 24 := by
  rw [SemidirectProduct.card]
  norm_num [QuaternionGroup.card]

theorem binaryTetrahedral_center_card :
    Nat.card (Subgroup.center BinaryTetrahedral) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem binaryTetrahedral_quotient_card :
    Nat.card BinaryTetrahedralCentralQuotient = 12 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center BinaryTetrahedral)
  rw [binaryTetrahedral_card, binaryTetrahedral_center_card] at h
  change 24 = Nat.card BinaryTetrahedralCentralQuotient * 2 at h
  omega

theorem binaryT_cube : binaryT ^ 3 = 1 := by decide

theorem binaryI_square_central : binaryI ^ 2 ∈ Subgroup.center BinaryTetrahedral := by
  decide

theorem binary_commutator_square_central :
    (binaryI⁻¹ * binaryT * binaryI * binaryT⁻¹) ^ 2 ∈
      Subgroup.center BinaryTetrahedral := by decide

theorem binary_commutator_eq_conjugate :
    binaryI⁻¹ * binaryT * binaryI * binaryT⁻¹ =
      binaryT ^ 2 * binaryI * (binaryT ^ 2)⁻¹ := by decide

theorem binary_commutator_pair_eq_conjugate :
    binaryT * (binaryI⁻¹ * binaryT * binaryI * binaryT⁻¹) * binaryT⁻¹ *
        (binaryI⁻¹ * binaryT * binaryI * binaryT⁻¹)⁻¹ =
      binaryT ^ 2 * binaryJ * (binaryT ^ 2)⁻¹ := by decide

theorem binary_hom_ext {E : Type*} [Group E] (f g : BinaryTetrahedral →* E)
    (hI : f binaryI = g binaryI) (hJ : f binaryJ = g binaryJ)
    (hT : f binaryT = g binaryT) : f = g := by
  have hl (x : QuaternionGroup 2) : f (SemidirectProduct.inl x) =
      g (SemidirectProduct.inl x) := by
    rcases x with i | i
    · rw [← ZMod.natCast_zmod_val i, ← QuaternionGroup.a_one_pow]
      simp only [map_pow, hI]
    · have hx : QuaternionGroup.xa i = QuaternionGroup.xa 0 * QuaternionGroup.a i := by
        simp [QuaternionGroup.xa_mul_a]
      rw [hx, map_mul, map_mul, map_mul, hJ]
      rw [← ZMod.natCast_zmod_val i, ← QuaternionGroup.a_one_pow]
      simp only [map_pow, hI]
  have hr (k : Multiplicative (ZMod 3)) : f (SemidirectProduct.inr k) =
      g (SemidirectProduct.inr k) := by
    change ZMod 3 at k
    fin_cases k
    · change f (SemidirectProduct.inr 1) = g (SemidirectProduct.inr 1)
      simp
    · exact hT
    · change f (binaryT ^ 2) = g (binaryT ^ 2)
      simp only [map_pow, hT]
  ext x
  rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul, map_mul, hl, hr]

noncomputable def binaryTetrahedralCentralQuotientEquivPSL :
    BinaryTetrahedralCentralQuotient ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3) := by
  apply QuotientGroup.congr _ _ binaryTetrahedralEquivSL
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Subgroup.centerCongr binaryTetrahedralEquivSL ⟨x, hx⟩).property
  · intro hy
    exact ⟨binaryTetrahedralEquivSL.symm y,
      (Subgroup.centerCongr binaryTetrahedralEquivSL.symm ⟨y, hy⟩).property,
      binaryTetrahedralEquivSL.apply_symm_apply y⟩

end GLS3.Chapter5.SchurPresentation
