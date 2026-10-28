module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.ExtensionAction
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.LocalCharactersModel
public import Theory.Character.Transport

/-!
# Actual quadratic characters of the original involution centralizer

The full quaternion quotient is the equal-sign subgroup of S₃ × S₃.
Its four permutation constructions inflate to four distinct irreducibles
of the original H. Their differences vanish at every three-regular element.
No character or character-table premise is needed.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
namespace LocalCharacters
open LocalCharactersModel

private theorem sign_eq_of_product (a b : S3)
    (h : Equiv.Perm.sign a * Equiv.Perm.sign b = 1) :
    Equiv.Perm.sign a = Equiv.Perm.sign b := by
  revert a b
  decide +kernel

private theorem sign_product_of_eq (a b : S3)
    (h : Equiv.Perm.sign a = Equiv.Perm.sign b) :
    Equiv.Perm.sign a * Equiv.Perm.sign b = 1 := by
  revert a b
  decide +kernel

def pairMap : diagonalSign →* D where
  toFun w := ⟨(w.val.left 1, w.val.left BinaryFourPlus.swapIndex),
    by exact sign_eq_of_product _ _ w.property.2⟩
  map_one' := rfl
  map_mul' a b := by
    apply Subtype.ext
    have ha : a.val.right = 1 := a.property.1
    simp only [Subgroup.coe_mul, RegularWreathProduct.mul_left, ha,
      inv_one, one_mul]
    rfl

theorem pairMap_surjective : Function.Surjective pairMap := by
  intro d
  let w : BinaryFourPlus.Wreath :=
    ⟨fun i => if i = 1 then d.val.1 else d.val.2, 1⟩
  have hw : w ∈ diagonalSign := by
    refine ⟨rfl, ?_⟩
    change Equiv.Perm.sign (if (1 : BinaryFourPlus.C2) = 1 then d.val.1 else d.val.2) *
      Equiv.Perm.sign (if BinaryFourPlus.swapIndex = 1 then d.val.1 else d.val.2) = 1
    simpa only [ite_true, BinaryFourPlus.swapIndex_ne_one, ite_false] using
      sign_product_of_eq d.val.1 d.val.2 d.property
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  simp [pairMap, w]

variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] Fintype.ofFinite

/-- The original full quaternion quotient, in the literal permutation coordinates. -/
def quotientMap : c.H →* D := pairMap.comp
  ((coreQuotientEquiv c).toMonoidHom.comp (QuotientGroup.mk' (quaternionCore c)))

theorem quotientMap_surjective : Function.Surjective (quotientMap c) :=
  pairMap_surjective.comp ((coreQuotientEquiv c).surjective.comp
    (QuotientGroup.mk'_surjective (quaternionCore c)))

/-- Four explicit rows on the original H. -/
def localRow (i : Fin 4) : ClassFunction c.H := fun h => row i (quotientMap c h)

theorem localRow_one (i : Fin 4) : localRow c i 1 = 2 := by
  simp only [localRow, map_one, row_one]

theorem localRow_irreducible (i : Fin 4) : IsIrreducibleCharacter (localRow c i) := by
  apply (isGeneralizedCharacter_comp_hom (quotientMap c) (row_generalized i)).irreducible_of_norm_one
  · exact (scalarProduct_comp_surjective (quotientMap c) (quotientMap_surjective c)
      (row i) (row i)).trans (row_norm i)
  · rw [map_one, row_one]
    norm_num

theorem localRow_injective : Function.Injective (localRow c) := by
  intro i j hij
  apply row_injective
  ext d
  obtain ⟨h, rfl⟩ := quotientMap_surjective c d
  exact congrFun hij h

theorem localRow_difference_supported (i j : Fin 4) :
    supportedOn (localRow c i - localRow c j) {a : c.H | 3 ∣ orderOf a} := by
  intro a ha
  apply sub_eq_zero.mpr
  apply row_equal_of_three_regular
  intro hd
  exact ha (hd.trans (orderOf_map_dvd (quotientMap c) a))

/-- The actual linear sign character of the quaternion quotient. -/
def localSign : c.H →* ℂ := signRow.comp (quotientMap c)

theorem localSign_linear : IsLinearCharacter (localSign c : c.H → ℂ) :=
  (localSign c).isLinearCharacter

/-- The four virtual rows used by special-support induction. -/
def localAlpha (i : Fin 4) : ClassFunction c.H := fun h => alpha i (quotientMap c h)

theorem localAlpha_eq (i : Fin 4) :
    localAlpha c i = 1 + (localSign c : c.H → ℂ) - localRow c i := by
  ext h
  exact congrFun (alpha_eq i) (quotientMap c h)

theorem localAlpha_generalized (i : Fin 4) : IsGeneralizedCharacter (localAlpha c i) :=
  isGeneralizedCharacter_comp_hom (quotientMap c) (alpha_generalized i)

theorem localAlpha_supported (i : Fin 4) :
    supportedOn (localAlpha c i) {a : c.H | 3 ∣ orderOf a} := by
  intro a ha
  exact alpha_three_regular i (quotientMap c a)
    (fun hd => ha (hd.trans (orderOf_map_dvd (quotientMap c) a)))

theorem localAlpha_one (i : Fin 4) : localAlpha c i 1 = 0 := by
  simp only [localAlpha, map_one, alpha_one]

theorem localAlpha_inner (i j : Fin 4) :
    scalarProduct c.H (localAlpha c i) (localAlpha c j) = 2 + if i = j then 1 else 0 :=
  (scalarProduct_comp_surjective (quotientMap c) (quotientMap_surjective c)
    (alpha i) (alpha j)).trans (alpha_inner i j)

theorem localAlpha_principal (i : Fin 4) :
    scalarProduct c.H (localAlpha c i) 1 = 1 :=
  (scalarProduct_comp_surjective (quotientMap c) (quotientMap_surjective c)
    (alpha i) 1).trans (alpha_principal i)

end LocalCharacters
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
