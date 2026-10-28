module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Words
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftRelations

/-!
# The literal quotient marking of the fusion conjugator

The max1 word projects to this explicit permutation of the native 24 stars.
The left kernel correction does not change the quotient. This is the quotient
marking used in the native fusion equations, with the same left-conjugation
convention as the original projection.
Source: Kleidman--Wilson (1988), Corollary 2.3.6.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Theory.GroupTheory Subgroup Cardinality KernelCount QuotientCount.Image
open SylowCore SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four

def fusionPermutation : Equiv.Perm (Fin 24) where
  toFun := ![0,1,14,8,2,22,6,10,18,7,12,15,17,5,19,3,20,9,11,21,13,4,16,23]
  invFun := ![0,1,4,15,21,13,6,9,3,17,7,18,10,20,2,11,22,12,8,14,16,19,5,23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem alphabet_projection (i : Fin 4) :
    (π (nativeAlphabet i)).val = alphabet i := by
  fin_cases i
  · exact congrArg Subtype.val (starProjection_x _ _)
  · exact congrArg Subtype.val (starProjection_y _ _)
  · change (π (localX matrixA_mul_self matrixB_pow_four)⁻¹).val = starX⁻¹
    rw [map_inv, starProjection_x]
    rfl
  · change (π (localY matrixA_mul_self matrixB_pow_four)⁻¹).val = starY⁻¹
    rw [map_inv, starProjection_y]
    rfl

private theorem word_projection (w : List (Fin 4)) :
    (π (evalWord nativeAlphabet w)).val = evalWord alphabet w := by
  induction w with
  | nil => simp only [evalWord, map_one, coe_one]
  | cons i w ih => simp only [evalWord, map_mul, coe_mul, alphabet_projection, ih]

private theorem literalWord_projection :
    evalWord alphabet FusionWords.literalWord = fusionPermutation := by decide +kernel

theorem localFusion_projection : (π localFusion).val = fusionPermutation := by
  rw [localFusion, map_mul, nativeMask_projection, one_mul, word_projection]
  exact literalWord_projection

end Janko4.LocalStructure.ElementaryEightGeometry
