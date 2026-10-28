module

public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.FactorSign
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.OrthogonalWreath
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# An S₃ square in a wreath subgroup containing the residual and a four-group

Every involution in S₃ wr C₂ lies in either the factor-swap kernel or the
factor-sign kernel. A subgroup contained in the union of two subgroups is
contained in one of them, so an elementary two-subgroup lies in one of these
explicit copies of S₃ × S₃.

Both kernels contain the two-residual, of order nine. If a subgroup J also
contains an elementary four-group E, choose the kernel containing E. Its
intersection with J has order divisible by both nine and four, hence fills
the kernel. This supplies an actual square subgroup of relative index at
most two. The isomorphisms use the factor coordinates and balanced rotations;
no enumeration of subgroups or order-only recognition is involved.

Source application: Aschbacher--Smith, 14.3.20, printed pp.997--998, the
square quotient of a subgroup of the marked quotient centralizer.
-/

public section
open Subgroup
namespace BinaryFourPlus

/-- The balanced rotations and flips identify the factor-sign kernel with a square. -/
noncomputable def factorSignEquiv : factorSign.ker ≃*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  (MulEquiv.subgroupCongr balancedProduct_range.symm).trans
    (MonoidHom.ofInjective balancedProduct_injective).symm

/-- Every elementary two-subgroup lies wholly in one of the two square kernels. -/
theorem elementary_le_square_kernel (E : Subgroup Wreath) [IsElementaryAbelian 2 E] :
    E ≤ (RegularWreathProduct.rightHom : Wreath →* C2).ker ∨ E ≤ factorSign.ker := by
  apply SubgroupClass.subset_union.mp
  intro w hw
  by_cases hs : factorSign w = 1
  · exact Or.inr hs
  · apply Or.inl
    exact factorSign_odd_involution_preserves_factors w hs
      (congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) ⟨w,hw⟩))

/-- The two-residual is the cubic base, of order nine. -/
theorem wreath_residual_card : Nat.card (pResidual 2 Wreath) = 9 := by
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e := RegularWreathProduct.congr eSL (MulEquiv.refl C2)
  rw [←map_pResidual 2 e,card_map_of_injective e.injective]
  obtain ⟨r⟩ := Theory.GroupTheory.WreathTwoResidual.residual_equiv_elementaryNine
  rw [Nat.card_congr r.toEquiv]
  norm_num [Nat.card_eq_fintype_card]

private theorem square_card (K : Subgroup Wreath)
    (e : K ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : Nat.card K = 36 := by
  rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_perm]
  norm_num

private theorem wreath_card : Nat.card Wreath = 72 := by
  rw [RegularWreathProduct.card,Nat.card_perm]
  norm_num [Nat.card_eq_fintype_card]

private theorem square_index (K : Subgroup Wreath)
    (e : K ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : K.index = 2 := by
  have h := K.card_mul_index
  rw [square_card K e,wreath_card] at h
  omega

private theorem square_le_of_residual_four (J E K : Subgroup Wreath) [K.Normal]
    (hR : pResidual 2 Wreath ≤ J) (hEJ : E ≤ J) (hEK : E ≤ K)
    (hE : Nat.card E = 4)
    (e : K ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : K ≤ J := by
  have hRK : pResidual 2 Wreath ≤ K := by
    apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    simpa only [pow_one,←index_eq_card] using square_index K e
  have h9 : 9 ∣ Nat.card (K ⊓ J : Subgroup Wreath) := by
    rw [←wreath_residual_card]
    exact card_dvd_of_le (le_inf hRK hR)
  have h4 : 4 ∣ Nat.card (K ⊓ J : Subgroup Wreath) := by
    rw [←hE]
    exact card_dvd_of_le (le_inf hEK hEJ)
  have h36 : 36 ∣ Nat.card (K ⊓ J : Subgroup Wreath) :=
    (by decide : Nat.Coprime 9 4).mul_dvd_of_dvd_of_dvd h9 h4
  have heq : K ⊓ J = K := eq_of_le_of_card_ge inf_le_left (by
    rw [square_card K e]
    exact Nat.le_of_dvd Nat.card_pos h36)
  exact heq ▸ inf_le_right

/-- A residual-containing wreath subgroup with an elementary four-group contains
an actual S₃ × S₃ subgroup of relative index at most two. -/
theorem exists_square_of_residual_four (J E : Subgroup Wreath)
    (hR : pResidual 2 Wreath ≤ J) (hEJ : E ≤ J)
    (hEA : IsElementaryAbelian 2 E) (hE : Nat.card E = 4) :
    ∃ S : Subgroup Wreath, S ≤ J ∧ S.relIndex J ≤ 2 ∧
      Nonempty (S ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let := hEA
  have finish (K : Subgroup Wreath) [K.Normal] (hEK : E ≤ K)
      (e : K ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
      K ≤ J ∧ K.relIndex J ≤ 2 ∧
        Nonempty (K ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
    have hKJ := square_le_of_residual_four J E K hR hEJ hEK hE e
    refine ⟨hKJ,?_,⟨e⟩⟩
    have hd := relIndex_dvd_index_of_le hKJ
    rw [square_index K e] at hd
    exact Nat.le_of_dvd (by decide) hd
  rcases elementary_le_square_kernel E with hbase | hsign
  · exact ⟨_,finish _ hbase baseEquiv⟩
  · exact ⟨_,finish _ hsign factorSignEquiv⟩
end BinaryFourPlus
