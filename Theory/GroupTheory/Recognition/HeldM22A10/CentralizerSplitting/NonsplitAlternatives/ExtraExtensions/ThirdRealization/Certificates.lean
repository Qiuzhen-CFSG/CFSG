module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.ThirdRealization.Tables
public import Theory.GroupTheory.WordSubgroup
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Checked finite facts for the third extension

Words prove row membership; generator transitions prove exhaustive coverage.
The remaining checks identify the kernel, quotient labels, binary group law,
and conjugation on the two generators. Finally two disjoint transpositions
have no commuting involutory lifts, obstructing any homomorphic section.
All finite identities are reduced by the Lean kernel.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.ThirdRealization
open LocalModelDichotomy NonsplitModels
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem row_word : ∀ i x, row i x = evalWord ![thirdA, thirdB] (word i) x := by
  decide +kernel

public theorem row_one : ∀ x, row 0 x = x := by decide +kernel

public theorem row_next : ∀ i j x,
    row (next i j) x = row i (![thirdA, thirdB, thirdA⁻¹, thirdB⁻¹] j x) := by
  decide +kernel

public theorem row_blocks : ∀ i x,
    block (row i x) = block (row i (blockRep (block x))) := by decide +kernel

public theorem block_rep : ∀ j, block (blockRep j) = j := by decide +kernel

public theorem quotient_witness : ∀ s j,
    block (row (quotientWitness s) (blockRep j)) = s j := by decide +kernel

public theorem binary_code_vector : ∀ i, binaryCode (binaryVector i) = i := by
  decide +kernel

public theorem kernel_one : ∀ x, kernelRow 1 x = x := by decide +kernel

public theorem kernel_mul : ∀ v w x, kernelRow (v * w) x = kernelRow v (kernelRow w x) := by
  decide +kernel

public theorem kernel_injective_key : Function.Injective
    (fun v => (kernelRow v 0, kernelRow v 2, kernelRow v 4)) := by decide +kernel

public theorem kernel_blocks : ∀ v j, block (kernelRow v (blockRep j)) = j := by
  decide +kernel

public theorem row_kernel : ∀ i,
    (∀ j, block (row i (blockRep j)) = j) →
      ∀ x, row i x = kernelRow (binaryVector (kernelCoordinate i)) x := by
  decide +kernel

/-- The explicit quotient images of the published generators. -/
@[expose] public def quotientA : SymmetricFour where
  toFun := ![0, 3, 1, 2]
  invFun := ![0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[expose] public def quotientB : SymmetricFour where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

public theorem quotient_generators : ∀ j : Fin 2, ∀ x,
    block (![thirdA, thirdB] j (blockRep x)) = ![quotientA, quotientB] j x := by
  decide +kernel

public theorem conjugation_generators : ∀ j : Fin 2, ∀ v x,
    kernelRow (sixOrbitAction (![quotientA, quotientB] j) v) x =
      ![thirdA, thirdB] j (kernelRow v ((![thirdA, thirdB] j)⁻¹ x)) := by
  decide +kernel

/-- Exhaust the four involutory lifts of each of the disjoint transpositions. -/
public theorem involution_lifts_left : ∀ i,
    (∀ x, row i (row i x) = x) →
    ((∀ j, block (row i (blockRep j)) = Equiv.swap (0 : Fin 4) 1 j) →
      i = 270 ∨ i = 287 ∨ i = 302 ∨ i = 309) := by
  decide +kernel

public theorem involution_lifts_right : ∀ i,
    (∀ x, row i (row i x) = x) →
    ((∀ j, block (row i (blockRep j)) = Equiv.swap (2 : Fin 4) 3 j) →
      i = 265 ∨ i = 278 ∨ i = 307 ∨ i = 379) := by
  decide +kernel

public theorem lifts_do_not_commute : ∀ i j : Fin 4,
    row (![270, 287, 302, 309] i) (row (![265, 278, 307, 379] j) 0) ≠
      row (![265, 278, 307, 379] j) (row (![270, 287, 302, 309] i) 0) := by
  decide +kernel

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.ThirdRealization
