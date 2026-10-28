module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 32-63

Each remaining batch is checked pointwise on the 4060 permutation points by
Lean's kernel.  Cancellation-only batches are discharged by the shared reduction.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block1
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch33 : stepBatch 2 33 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch34 : stepBatch 2 34 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch35 : stepBatch 2 35 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch36 : stepBatch 2 36 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch37 : stepBatch 2 37 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch38 : stepBatch 2 38 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch40 : stepBatch 2 40 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch41 : stepBatch 2 41 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch42 : stepBatch 2 42 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch44 : stepBatch 2 44 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch45 : stepBatch 2 45 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch46 : stepBatch 2 46 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch47 : stepBatch 2 47 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch48 : stepBatch 2 48 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch49 : stepBatch 2 49 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch50 : stepBatch 2 50 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch52 : stepBatch 2 52 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch53 : stepBatch 2 53 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch54 : stepBatch 2 54 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch55 : stepBatch 2 55 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch56 : stepBatch 2 56 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch57 : stepBatch 2 57 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch58 : stepBatch 2 58 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch59 : stepBatch 2 59 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch60 : stepBatch 2 60 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch61 : stepBatch 2 61 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch63 : stepBatch 2 63 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The thirty-two batches from 32 through 63. -/
public theorem batches (b : Fin 32) : stepBatch 2 ⟨32 + b.val, by omega⟩ := by
  fin_cases b
  · exact algebraic_batches 32 (by decide +kernel)
  · exact batch33
  · exact batch34
  · exact batch35
  · exact batch36
  · exact batch37
  · exact batch38
  · exact algebraic_batches 39 (by decide +kernel)
  · exact batch40
  · exact batch41
  · exact batch42
  · exact algebraic_batches 43 (by decide +kernel)
  · exact batch44
  · exact batch45
  · exact batch46
  · exact batch47
  · exact batch48
  · exact batch49
  · exact batch50
  · exact algebraic_batches 51 (by decide +kernel)
  · exact batch52
  · exact batch53
  · exact batch54
  · exact batch55
  · exact batch56
  · exact batch57
  · exact batch58
  · exact batch59
  · exact batch60
  · exact batch61
  · exact algebraic_batches 62 (by decide +kernel)
  · exact batch63

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block1
