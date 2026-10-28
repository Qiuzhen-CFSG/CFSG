module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.Seeds
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.Coordinates
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarData

/-!
# Evaluating masks in the concrete local kernel

The binary coordinates from the local-order certificate are reindexed by
integers below 2048. XOR evaluates to multiplication and the two mask maps
evaluate to right conjugation. Masks 1 and 3 give the two checked fusion seeds.
The fold argument follows `QuotientCount.Image.Comparison`; the source words
and conjugation tables are documented in `KernelCount.Tables`.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
@[expose] public section
namespace Janko4.Simplicity.Max1Fusion.KernelOrbits
open Cardinality Cardinality.KernelCount Cardinality.QuotientCount.Image
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

def maskValue (m : ℕ) : localKernel hA hB :=
  coordinates hA hB (fun i => m.testBit i.val)

lemma maskValue_zero : maskValue hA hB 0 = 1 := by
  apply Subtype.ext
  simp [maskValue, coordinates_val, binaryProduct_zero]

lemma maskValue_xor (m n : ℕ) :
    maskValue hA hB (Nat.xor m n) = maskValue hA hB m * maskValue hA hB n := by
  change maskValue hA hB (m ^^^ n) = _
  simp only [maskValue, coordinates_mul, Nat.testBit_xor]

lemma maskValue_fold (l : List ℕ) :
    maskValue hA hB (l.foldr Nat.xor 0) = (l.map (maskValue hA hB)).prod := by
  induction l with
  | nil => exact maskValue_zero hA hB
  | cons a l ih => simpa only [List.foldr_cons, List.map_cons, List.prod_cons,
      maskValue_xor] using congrArg (maskValue hA hB a * ·) ih

lemma maskValue_maskImage (masks : Fin 11 → ℕ) (m : ℕ) :
    (maskValue hA hB (maskImage masks m) : max1Subgroup hA hB) =
      binaryProduct (fun i => binaryProduct (basis hA hB)
        (fun j => (masks i).testBit j.val)) (fun i => m.testBit i.val) := by
  rw [maskImage, maskValue_fold]
  simp only [List.map_ofFn, SubmonoidClass.coe_list_prod]
  rw [binaryProduct]
  congr 1
  congr 1
  funext i
  dsimp only [Function.comp_apply]
  split_ifs
  · rfl
  · change (maskValue hA hB 0 : max1Subgroup hA hB) = 1
    rw [maskValue_zero]
    rfl

lemma right_conj_mask_x (m : ℕ) :
    (localX hA hB)⁻¹ * (maskValue hA hB m : max1Subgroup hA hB) * localX hA hB =
      maskValue hA hB (maskImage xMasks m) := by
  rw [maskValue_maskImage]
  exact right_conj_coordinates_x hA hB _

lemma right_conj_mask_y (m : ℕ) :
    (localY hA hB)⁻¹ * (maskValue hA hB m : max1Subgroup hA hB) * localY hA hB =
      maskValue hA hB (maskImage yMasks m) := by
  rw [maskValue_maskImage]
  exact right_conj_coordinates_y hA hB _

lemma maskValue_basis (i : Fin 11) :
    (maskValue hA hB (2 ^ i.val) : max1Subgroup hA hB) = basis hA hB i := by
  simp only [maskValue, coordinates_val, Nat.testBit_two_pow]
  convert binaryProduct_single (basis hA hB) i using 2
  funext j
  simp only [Fin.ext_iff, eq_comm]

lemma maskValue_one : (maskValue hA hB 1 : max1Subgroup hA hB) = localKernelSeed hA hB := by
  simpa only [Fin.val_zero, pow_zero, basis, conjugates, Matrix.cons_val_zero] using maskValue_basis hA hB 0

lemma maskValue_three : (maskValue hA hB 3 : max1Subgroup hA hB) = kernelPair hA hB := by
  have he : 3 = Nat.xor 1 2 := rfl
  rw [he, maskValue_xor]
  change (maskValue hA hB 1 : max1Subgroup hA hB) * maskValue hA hB 2 = _
  rw [maskValue_one, show (maskValue hA hB 2 : max1Subgroup hA hB) = basis hA hB 1 from
    maskValue_basis hA hB 1]
  simp only [kernelPair, basis, conjugates, Matrix.cons_val_one, Matrix.cons_val_zero]

lemma bits_surjective : Function.Surjective (fun m : Fin 2048 =>
    fun i : Fin 11 => m.val.testBit i.val) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by decide⟩).2
  intro m n h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 11
  · exact congrFun h ⟨j, hj⟩
  · have hp : 2^11 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le m.isLt hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le n.isLt hp)]

lemma maskValue_surjective : Function.Surjective (fun m : Fin 2048 => maskValue hA hB m.val) := by
  intro z
  obtain ⟨v, rfl⟩ := coordinates_surjective hA hB z
  obtain ⟨m, hm⟩ := bits_surjective v
  exact ⟨m, congrArg (coordinates hA hB) hm⟩

end Janko4.Simplicity.Max1Fusion.KernelOrbits
