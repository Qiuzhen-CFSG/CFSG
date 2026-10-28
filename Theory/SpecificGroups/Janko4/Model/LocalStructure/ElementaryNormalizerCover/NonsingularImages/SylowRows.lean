module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.Certificate

/-!
# Exhaustive elementary containers in the marked nonsingular Sylow

Six literal elementary subgroups contain every elementary subgroup of the
certified 128-element Sylow. Outside two chosen containers, the commuting
involutions of each exceptional involution lie in the union of two others.
A subgroup contained in a union of two subgroups lies in one of them. This
proves whole-subgroup coverage without assuming maximality or normality.

Binary products of five commuting involutions certify the containers using
short generator identities, avoiding a quadratic multiplication certificate.
`FourRows` relates these containers to the selected source images, and
`SourceRows` lifts the choices through the original ambient quotient.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Lemma 2.3.1,
printed p.492. The native permutation coordinates and ATLAS attribution are
inherited from `NonsingularImages.Certificate`.
-/

set_option Elab.async false
@[expose] public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
open Subgroup Theory.GroupTheory Cardinality.QuotientCount.Image
open scoped IsMulCommutative

def rowIndex : Fin 6 → Fin 32 → Fin 128 :=
  ![![0, 1, 2, 3, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31, 96, 97, 98, 99, 108, 109, 110, 111, 120, 121, 122, 123, 124, 125, 126, 127], ![0, 3, 28, 31, 32, 35, 60, 63, 64, 67, 92, 95, 96, 99, 124, 127, 0, 3, 28, 31, 32, 35, 60, 63, 64, 67, 92, 95, 96, 99, 124, 127], ![0, 4, 9, 13, 18, 26, 31, 23, 96, 100, 105, 109, 114, 122, 127, 119, 0, 4, 9, 13, 18, 26, 31, 23, 96, 100, 105, 109, 114, 122, 127, 119], ![0, 4, 23, 31, 32, 36, 55, 63, 64, 68, 87, 95, 96, 100, 119, 127, 0, 4, 23, 31, 32, 36, 55, 63, 64, 68, 87, 95, 96, 100, 119, 127], ![0, 9, 18, 31, 35, 42, 49, 60, 67, 74, 81, 92, 96, 105, 114, 127, 0, 9, 18, 31, 35, 42, 49, 60, 67, 74, 81, 92, 96, 105, 114, 127], ![0, 14, 25, 31, 36, 49, 42, 55, 68, 81, 74, 87, 96, 110, 121, 127, 0, 14, 25, 31, 36, 49, 42, 55, 68, 81, 74, 87, 96, 110, 121, 127]]

open Cardinality.KernelCount

def rowGenerator (k : Fin 6) (j : Fin 5) : StarGroup :=
  element (rowIndex k ⟨2 ^ j.val, by have := j.isLt; interval_cases j.val <;> decide⟩)

private def generatorPoint : Fin 6 → Fin 5 → Fin 24 → Fin 24 :=
![![![0, 1, 2, 3, 4, 7, 9, 5, 8, 6, 18, 19, 20, 21, 15, 14, 16, 17, 10, 11, 12, 13, 23, 22], ![0, 1, 2, 3, 4, 14, 22, 15, 8, 23, 21, 12, 11, 18, 5, 7, 16, 17, 13, 20, 19, 10, 6, 9], ![0, 1, 2, 3, 8, 5, 9, 7, 4, 6, 13, 12, 11, 10, 14, 15, 17, 16, 21, 20, 19, 18, 23, 22], ![0, 1, 2, 3, 16, 5, 22, 7, 17, 23, 18, 20, 19, 21, 14, 15, 4, 8, 10, 12, 11, 13, 6, 9], ![1, 0, 3, 2, 4, 5, 23, 7, 8, 22, 18, 12, 11, 21, 14, 15, 16, 17, 10, 20, 19, 13, 9, 6]], ![![0, 1, 2, 3, 4, 15, 23, 14, 8, 22, 13, 20, 19, 10, 7, 5, 16, 17, 21, 12, 11, 18, 9, 6], ![0, 1, 2, 3, 17, 5, 23, 7, 16, 22, 21, 19, 20, 18, 14, 15, 8, 4, 13, 11, 12, 10, 9, 6], ![0, 1, 3, 2, 4, 5, 6, 14, 16, 22, 19, 21, 13, 12, 7, 15, 8, 17, 20, 10, 18, 11, 9, 23], ![1, 0, 2, 3, 4, 5, 23, 14, 16, 9, 20, 13, 21, 11, 7, 15, 8, 17, 19, 18, 10, 12, 22, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]], ![![0, 1, 2, 3, 5, 4, 6, 8, 7, 9, 20, 21, 13, 12, 16, 17, 14, 15, 19, 18, 10, 11, 22, 23], ![0, 1, 2, 3, 7, 8, 6, 4, 5, 9, 11, 10, 18, 19, 17, 16, 15, 14, 12, 13, 21, 20, 22, 23], ![0, 1, 2, 3, 14, 16, 6, 17, 15, 9, 12, 18, 10, 20, 4, 8, 5, 7, 11, 21, 13, 19, 22, 23], ![1, 0, 3, 2, 4, 5, 23, 7, 8, 22, 18, 12, 11, 21, 14, 15, 16, 17, 10, 20, 19, 13, 9, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]], ![![0, 1, 2, 3, 5, 4, 6, 8, 7, 9, 20, 21, 13, 12, 16, 17, 14, 15, 19, 18, 10, 11, 22, 23], ![0, 1, 2, 3, 15, 17, 6, 16, 14, 9, 19, 13, 21, 11, 8, 4, 7, 5, 20, 10, 18, 12, 22, 23], ![0, 1, 3, 2, 4, 5, 6, 14, 16, 22, 19, 21, 13, 12, 7, 15, 8, 17, 20, 10, 18, 11, 9, 23], ![1, 0, 2, 3, 4, 5, 23, 14, 16, 9, 20, 13, 21, 11, 7, 15, 8, 17, 19, 18, 10, 12, 22, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]], ![![0, 1, 2, 3, 7, 8, 6, 4, 5, 9, 11, 10, 18, 19, 17, 16, 15, 14, 12, 13, 21, 20, 22, 23], ![0, 1, 2, 3, 14, 16, 6, 17, 15, 9, 12, 18, 10, 20, 4, 8, 5, 7, 11, 21, 13, 19, 22, 23], ![0, 1, 3, 2, 4, 15, 23, 7, 16, 9, 12, 18, 10, 19, 14, 5, 8, 17, 11, 13, 21, 20, 22, 6], ![1, 0, 2, 3, 4, 15, 6, 7, 16, 22, 11, 10, 18, 20, 14, 5, 8, 17, 12, 21, 13, 19, 9, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]], ![![0, 1, 2, 3, 8, 14, 23, 15, 4, 22, 18, 11, 12, 21, 5, 7, 17, 16, 10, 19, 20, 13, 9, 6], ![0, 1, 2, 3, 16, 7, 23, 5, 17, 22, 10, 12, 11, 13, 15, 14, 4, 8, 18, 20, 19, 21, 9, 6], ![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![1, 0, 2, 3, 5, 4, 23, 16, 14, 9, 10, 12, 11, 21, 8, 17, 7, 15, 18, 19, 20, 13, 22, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]]
private def generatorPermutation (k : Fin 6) (j : Fin 5) : Equiv.Perm (Fin 24) where
  toFun := generatorPoint k j
  invFun := generatorPoint k j
  left_inv := by revert k j; decide +kernel
  right_inv := by revert k j; decide +kernel

private theorem rowGenerator_val (k : Fin 6) (j : Fin 5) :
    (rowGenerator k j).val = generatorPermutation k j := by
  apply Equiv.ext
  intro x
  rw [rowGenerator,element_apply]
  revert k j x
  decide +kernel

private theorem generator_square (k : Fin 6) (j : Fin 5) :
    rowGenerator k j * rowGenerator k j = 1 := by
  apply Subtype.ext
  change (rowGenerator k j).val * (rowGenerator k j).val = 1
  rw [rowGenerator_val]
  revert k j
  decide +kernel

private theorem generator_commute (k : Fin 6) (i j : Fin 5) :
    Commute (rowGenerator k i) (rowGenerator k j) := by
  apply Subtype.ext
  change (rowGenerator k i).val * (rowGenerator k j).val =
    (rowGenerator k j).val * (rowGenerator k i).val
  rw [rowGenerator_val,rowGenerator_val]
  revert k i j
  decide +kernel

private theorem product_point : ∀ (k : Fin 6) (i : Fin 32) (x : Fin 24),
    (binaryProduct (generatorPermutation k) (fun j => i.val.testBit j.val)) x =
      point (rowIndex k i) x := by
  decide +kernel

private theorem row_product (k : Fin 6) (i : Fin 32) :
    binaryProduct (rowGenerator k) (fun j => i.val.testBit j.val) = element (rowIndex k i) := by
  apply Subtype.ext
  change StarGroup.subtype (binaryProduct (rowGenerator k) (fun j => i.val.testBit j.val)) =
    (element (rowIndex k i)).val.val
  rw [map_binaryProduct]
  simp only [subtype_apply,rowGenerator_val]
  apply Equiv.ext
  intro x
  rw [element_apply]
  exact product_point k i x

private theorem bits_surjective (v : Fin 5 → Bool) :
    ∃ i : Fin 32, (fun j : Fin 5 => i.val.testBit j.val) = v := by
  revert v
  decide +kernel

def rowGroup (k : Fin 6) : Subgroup StarGroup := closure (Set.range (rowGenerator k))

theorem mem_rowGroup_iff (k : Fin 6) (x : StarGroup) :
    x ∈ rowGroup k ↔ ∃ i : Fin 32, (element (rowIndex k i) : StarGroup) = x := by
  rw [rowGroup,mem_closure_iff_binaryProduct _ (generator_square k) (generator_commute k)]
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨i,rfl⟩ := bits_surjective v
    exact ⟨i,(row_product k i).symm.trans hv⟩
  · rintro ⟨i,rfl⟩
    exact ⟨_,row_product k i⟩

instance rowGroup_elementary (k : Fin 6) : IsElementaryAbelian 2 (rowGroup k) := by
  let : IsMulCommutative (closure (Set.range (rowGenerator k))) :=
    isMulCommutative_closure (by
      rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
      exact generator_commute k i j)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨i,rfl⟩
  simpa only [pow_two] using generator_square k i


private def exceptionalIndex : Fin 12 → Fin 128 := ![9, 18, 35, 42, 49, 60, 67, 74, 81, 92, 105, 114]
private def pairChoice : Fin 12 → Fin 2 → Fin 6 := ![![2, 4], ![2, 4], ![1, 4], ![4, 5], ![4, 5], ![1, 4], ![1, 4], ![4, 5], ![4, 5], ![1, 4], ![2, 4], ![2, 4]]
private def squareWitness : Fin 128 → Fin 24 := ![0, 0, 0, 0, 0, 4, 4, 4, 4, 0, 4, 4, 0, 0, 0, 0, 4, 4, 0, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 0, 5, 5, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 0, 4, 4, 0, 0, 0, 0, 4, 4, 0, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def commuteWitness : Fin 12 → Fin 128 → Fin 24 := ![![0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0], ![0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0], ![0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0], ![0, 4, 4, 4, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 4, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 0, 4, 4, 4, 4, 4, 4, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0], ![0, 4, 4, 4, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 4, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 0, 4, 4, 4, 4, 4, 4, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0], ![0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0], ![0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0], ![0, 4, 4, 4, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 4, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 0, 4, 4, 4, 4, 4, 4, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0], ![0, 4, 4, 4, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 4, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 0, 4, 4, 4, 4, 4, 4, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 0, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0], ![0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0, 0, 5, 5, 0, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 5, 0, 0, 5, 4, 4, 4, 4, 4, 4, 4, 4, 0, 5, 5, 0], ![0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0], ![0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 4, 4, 0, 4, 4, 0, 4, 4, 4, 4, 0]]

private theorem square_cases : ∀ i : Fin 128,
    point i (point i (squareWitness i)) = squareWitness i →
    (∃ j : Fin 32, i = rowIndex 0 j) ∨ (∃ j : Fin 32, i = rowIndex 3 j) ∨
      ∃ k : Fin 12, i = exceptionalIndex k := by decide +kernel

private theorem exceptional_cover : ∀ (k : Fin 12) (i : Fin 128),
    point i (point i (squareWitness i)) = squareWitness i →
    point (exceptionalIndex k) (point i (commuteWitness k i)) =
      point i (point (exceptionalIndex k) (commuteWitness k i)) →
    ∃ (b : Fin 2) (j : Fin 32), i = rowIndex (pairChoice k b) j := by decide +kernel

theorem rowGroup_le_candidate (k : Fin 6) : rowGroup k ≤ candidate := by
  intro x hx
  obtain ⟨i,rfl⟩ := (mem_rowGroup_iff k x).mp hx
  exact (element _).property

/-- Every elementary subgroup of the literal 128-element Sylow lies in one of
six explicit elementary containers. The assertion concerns the whole subgroup,
not merely its individual involutions or its maximal subgroups. -/
theorem elementary_sylow_rows (A : Subgroup StarGroup) [IsElementaryAbelian 2 A]
    (hA : A ≤ candidate) : ∃ k : Fin 6, A ≤ rowGroup k := by
  classical
  have square (i : Fin 128) (hi : (element i : StarGroup) ∈ A) (x : Fin 24) :
      point i (point i x) = x := by
    have h := congrArg (fun g : StarGroup => g.val x)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (element i : StarGroup) hi)
    simpa only [pow_two, coe_mul, Equiv.Perm.coe_mul, Function.comp_apply,
      element_apply, coe_one, Equiv.Perm.one_apply] using h
  have repr (x : StarGroup) (hx : x ∈ A) : ∃ i, (element i : StarGroup) = x := by
    obtain ⟨i,hi⟩ := element_surjective ⟨x,hA hx⟩
    exact ⟨i,congrArg Subtype.val hi⟩
  by_cases hex : ∃ k : Fin 12, (element (exceptionalIndex k) : StarGroup) ∈ A
  · obtain ⟨k,hk⟩ := hex
    have hu : (A : Set StarGroup) ⊆ (rowGroup (pairChoice k 0) : Set StarGroup) ∪
        rowGroup (pairChoice k 1) := by
      intro x hx
      obtain ⟨i,rfl⟩ := repr x hx
      have hc (z : Fin 24) :
          point (exceptionalIndex k) (point i z) = point i (point (exceptionalIndex k) z) := by
        have h := congrArg (fun a : A => a.val.val z)
          (mul_comm (⟨element (exceptionalIndex k),hk⟩ : A) ⟨element i,hx⟩)
        simpa only [coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, element_apply] using h
      obtain ⟨b,j,hj⟩ := exceptional_cover k i (square i hx _) (hc _)
      fin_cases b
      · exact Or.inl ((mem_rowGroup_iff _ _).mpr ⟨j,congrArg (fun i => (element i : StarGroup)) hj.symm⟩)
      · exact Or.inr ((mem_rowGroup_iff _ _).mpr ⟨j,congrArg (fun i => (element i : StarGroup)) hj.symm⟩)
    rcases SubgroupClass.subset_union.mp hu with h | h
    · exact ⟨pairChoice k 0,h⟩
    · exact ⟨pairChoice k 1,h⟩
  · have hu : (A : Set StarGroup) ⊆ (rowGroup 0 : Set StarGroup) ∪ rowGroup 3 := by
      intro x hx
      obtain ⟨i,rfl⟩ := repr x hx
      rcases square_cases i (square i hx _) with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨k,rfl⟩
      · exact Or.inl ((mem_rowGroup_iff _ _).mpr ⟨j,congrArg (fun i => (element i : StarGroup)) hj.symm⟩)
      · exact Or.inr ((mem_rowGroup_iff _ _).mpr ⟨j,congrArg (fun i => (element i : StarGroup)) hj.symm⟩)
      · exact (hex ⟨k,hx⟩).elim
    rcases SubgroupClass.subset_union.mp hu with h | h
    · exact ⟨0,h⟩
    · exact ⟨3,h⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
