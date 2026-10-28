module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 0-31

Each remaining batch is checked pointwise on the 4060 permutation points by
Lean's kernel.  Cancellation-only batches are discharged by the shared reduction.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block0
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch6 : stepBatch 2 6 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch8 : stepBatch 2 8 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch10 : stepBatch 2 10 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch13 : stepBatch 2 13 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch15 : stepBatch 2 15 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch16 : stepBatch 2 16 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch18 : stepBatch 2 18 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch19 : stepBatch 2 19 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch21 : stepBatch 2 21 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch22 : stepBatch 2 22 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch24 : stepBatch 2 24 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch25 : stepBatch 2 25 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch28 : stepBatch 2 28 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch30 : stepBatch 2 30 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch31 : stepBatch 2 31 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The thirty-two batches from 0 through 31. -/
public theorem batches (b : Fin 32) : stepBatch 2 ⟨0 + b.val, by omega⟩ := by
  fin_cases b
  · exact algebraic_batches 0 (by decide +kernel)
  · exact algebraic_batches 1 (by decide +kernel)
  · exact algebraic_batches 2 (by decide +kernel)
  · exact algebraic_batches 3 (by decide +kernel)
  · exact algebraic_batches 4 (by decide +kernel)
  · exact algebraic_batches 5 (by decide +kernel)
  · exact batch6
  · exact algebraic_batches 7 (by decide +kernel)
  · exact batch8
  · exact algebraic_batches 9 (by decide +kernel)
  · exact batch10
  · exact algebraic_batches 11 (by decide +kernel)
  · exact algebraic_batches 12 (by decide +kernel)
  · exact batch13
  · exact algebraic_batches 14 (by decide +kernel)
  · exact batch15
  · exact batch16
  · exact algebraic_batches 17 (by decide +kernel)
  · exact batch18
  · exact batch19
  · exact algebraic_batches 20 (by decide +kernel)
  · exact batch21
  · exact batch22
  · exact algebraic_batches 23 (by decide +kernel)
  · exact batch24
  · exact batch25
  · exact algebraic_batches 26 (by decide +kernel)
  · exact algebraic_batches 27 (by decide +kernel)
  · exact batch28
  · exact algebraic_batches 29 (by decide +kernel)
  · exact batch30
  · exact batch31

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block0
