module
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The common prime-field cubic in binary PSL2

The matrix [[0,1],[1,1]] has exact order three in characteristic two.
The canonical projective quotient and faithful inner action preserve its
order. Every field automorphism fixes this literal matrix, so a pair of
field automorphisms centralizes the elementary-nine subgroup generated
by one inner cubic in each factor. All statements include the field F2.

Source application: Aschbacher--Smith 1.2.2(a), printed p.504, the
centralizing cubic obstruction in the two-component case.
-/

@[expose] public section
open Subgroup Matrix
open scoped IsMulCommutative
namespace Theory.PSL2.PairedOuterThree
variable (F : Type*) [Field F] [CharP F 2]

def primeCubic : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0,1;1,1], by simp [CharTwo.neg_eq]⟩

theorem primeCubic_pow : primeCubic F ^ 3 = 1 := by
  apply Subtype.ext
  change (!![0,1;1,1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem primeCubic_order : orderOf (primeCubic F) = 3 := by
  apply orderOf_eq_prime (primeCubic_pow F)
  intro he
  have hh := congrArg (fun m : SpecialLinearGroup (Fin 2) F => m.val 0 1) he
  simp [primeCubic] at hh

noncomputable def innerCubic : MulAut (Group F) :=
  MulAut.conj (quotientMap F (primeCubic F))

theorem innerCubic_order : orderOf (innerCubic F) = 3 := by
  have hi : Function.Injective (MulAut.conj : Group F →* MulAut (Group F)) := by
    rw [←MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro x hx
    exact psl2_conj_eq_one_implies x hx
  rw [innerCubic,orderOf_injective _ hi,
    orderOf_injective _ (quotientMap_injective F),primeCubic_order]

theorem innerCubic_mem : innerCubic F ∈ inner F := ⟨_,rfl⟩

theorem primeCubic_fixed (σ : F ≃+* F) :
    fieldAut σ (quotientMap F (primeCubic F)) = quotientMap F (primeCubic F) := by
  rw [fieldAut_apply_quotientMap]
  congr 1
  ext i j
  change σ ((primeCubic F).val i j) = (primeCubic F).val i j
  fin_cases i <;> fin_cases j <;> simp [primeCubic]

theorem field_commutes_innerCubic (σ : F ≃+* F) :
    Commute (fieldAut σ) (innerCubic F) := by
  apply MulEquiv.ext
  intro x
  change fieldAut σ ((quotientMap F (primeCubic F))*x*(quotientMap F (primeCubic F))⁻¹) =
    quotientMap F (primeCubic F)*fieldAut σ x*(quotientMap F (primeCubic F))⁻¹
  rw [map_mul,map_mul,map_inv,primeCubic_fixed]

noncomputable def cubicPlane : Subgroup (MulAut (Group F) × MulAut (Group F)) :=
  (zpowers (innerCubic F)).prod (zpowers (innerCubic F))

theorem cubicPlane_le_inner : cubicPlane F ≤ (inner F).prod (inner F) := by
  rintro x ⟨h₁,h₂⟩
  exact ⟨zpowers_le.mpr (innerCubic_mem F) h₁,zpowers_le.mpr (innerCubic_mem F) h₂⟩

theorem cubicPlane_elementary : IsElementaryAbelian 3 (cubicPlane F) := by
  have hp : innerCubic F ^ 3 = 1 := by rw [←innerCubic_order F,pow_orderOf_eq_one]
  let : IsElementaryAbelian 3 (zpowers (innerCubic F)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hp
  refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (Prod.ext ?_ ?_)⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · exact congrArg Subtype.val (mul_comm (⟨a.val.1,a.property.1⟩ : zpowers (innerCubic F)) ⟨b.val.1,b.property.1⟩)
  · exact congrArg Subtype.val (mul_comm (⟨a.val.2,a.property.2⟩ : zpowers (innerCubic F)) ⟨b.val.2,b.property.2⟩)
  · intro a
    exact Subtype.ext (Prod.ext
      (elemPow_eq_one_of_isElementaryAbelian a.val.1 a.property.1)
      (elemPow_eq_one_of_isElementaryAbelian a.val.2 a.property.2))

theorem cubicPlane_card : Nat.card (cubicPlane F) = 3^2 := by
  let e : cubicPlane F ≃ (zpowers (innerCubic F) × zpowers (innerCubic F)) :=
    { toFun x := (⟨x.val.1,x.property.1⟩,⟨x.val.2,x.property.2⟩)
      invFun x := ⟨(x.1,x.2),x.1.property,x.2.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e,Nat.card_prod,Nat.card_zpowers,innerCubic_order]
  rfl

theorem fieldPair_centralizes_plane (σ : (F ≃+* F) × (F ≃+* F)) :
    (fieldAut σ.1,fieldAut σ.2) ∈ centralizer (cubicPlane F : Set _) := by
  rintro x ⟨h₁,h₂⟩
  apply Prod.ext
  · exact mem_centralizer_singleton_iff.mp
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (field_commutes_innerCubic F σ.1).eq.symm) h₁)
  · exact mem_centralizer_singleton_iff.mp
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (field_commutes_innerCubic F σ.2).eq.symm) h₂)
end Theory.PSL2.PairedOuterThree
