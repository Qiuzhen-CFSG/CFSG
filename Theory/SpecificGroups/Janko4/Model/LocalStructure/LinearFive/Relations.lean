module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Evaluation
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Action
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.LiftRelations

/-!
# Native generator relations for the elementary linear-five subgroup

The outside squares and outside pair commutators are checked as packed matrix
identities. Commutation with the kernel is transported along the literal word
DAG through the existing eleven-bit right-conjugation action.
-/

public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Janko4.GeneratorCertificates Cardinality KernelCount KernelCount.Relations
open Simplicity.Max1Fusion.KernelOrbits QuotientCount.Image
open NativeRows NativeWords
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis
local notation "ρ" => representation matrixA_mul_self matrixB_pow_four
local notation "x" => localX matrixA_mul_self matrixB_pow_four
local notation "y" => localY matrixA_mul_self matrixB_pow_four
theorem lift_square (i : Fin 4) : lift i * lift i = 1 := by
  apply representation_injective matrixA_mul_self matrixB_pow_four
  rw [map_mul, map_one, representation_lift]
  fin_cases i
  · exact (decoded_product square_rows_0).trans decode_packedOne
  · exact (decoded_product square_rows_1).trans decode_packedOne
  · exact (decoded_product square_rows_2).trans decode_packedOne
  · exact (decoded_product square_rows_3).trans decode_packedOne
private theorem decoded_commute (a b : Vector ℕ 112)
    (h : packedMul a b = packedMul b a) : decodeRows a * decodeRows b = decodeRows b * decodeRows a :=
  (decode_packedMul a b).symm.trans ((congrArg decodeRows h).trans (decode_packedMul b a))

theorem lift_commute (i j : Fin 4) : Commute (lift i) (lift j) := by
  apply representation_injective matrixA_mul_self matrixB_pow_four
  simp only [map_mul, representation_lift]
  fin_cases i <;> fin_cases j
  · rfl
  · exact decoded_commute f0Rows f1Rows commute_rows_0_1
  · exact decoded_commute f0Rows f2Rows commute_rows_0_2
  · exact decoded_commute f0Rows f3Rows commute_rows_0_3
  · exact (decoded_commute f0Rows f1Rows commute_rows_0_1).symm
  · rfl
  · exact decoded_commute f1Rows f2Rows commute_rows_1_2
  · exact decoded_commute f1Rows f3Rows commute_rows_1_3
  · exact (decoded_commute f0Rows f2Rows commute_rows_0_2).symm
  · exact (decoded_commute f1Rows f2Rows commute_rows_1_2).symm
  · rfl
  · exact decoded_commute f2Rows f3Rows commute_rows_2_3
  · exact (decoded_commute f0Rows f3Rows commute_rows_0_3).symm
  · exact (decoded_commute f1Rows f3Rows commute_rows_1_3).symm
  · exact (decoded_commute f2Rows f3Rows commute_rows_2_3).symm
  · rfl
end Janko4.LocalStructure.LinearFive
