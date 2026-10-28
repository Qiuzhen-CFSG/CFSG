module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 64-95

Each remaining batch is checked pointwise on the 4060 permutation points by
Lean's kernel.  Cancellation-only batches are discharged by the shared reduction.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block2
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch64 : stepBatch 2 64 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch65 : stepBatch 2 65 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch67 : stepBatch 2 67 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch68 : stepBatch 2 68 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch69 : stepBatch 2 69 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch70 : stepBatch 2 70 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch71 : stepBatch 2 71 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch72 : stepBatch 2 72 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch73 : stepBatch 2 73 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch74 : stepBatch 2 74 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch75 : stepBatch 2 75 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch77 : stepBatch 2 77 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch78 : stepBatch 2 78 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch79 : stepBatch 2 79 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch80 : stepBatch 2 80 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch81 : stepBatch 2 81 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch82 : stepBatch 2 82 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch83 : stepBatch 2 83 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch84 : stepBatch 2 84 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch85 : stepBatch 2 85 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch86 : stepBatch 2 86 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch87 : stepBatch 2 87 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch88 : stepBatch 2 88 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch89 : stepBatch 2 89 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch90 : stepBatch 2 90 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch91 : stepBatch 2 91 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch92 : stepBatch 2 92 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch94 : stepBatch 2 94 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch95 : stepBatch 2 95 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The thirty-two batches from 64 through 95. -/
public theorem batches (b : Fin 32) : stepBatch 2 ⟨64 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch64
  · exact batch65
  · exact algebraic_batches 66 (by decide +kernel)
  · exact batch67
  · exact batch68
  · exact batch69
  · exact batch70
  · exact batch71
  · exact batch72
  · exact batch73
  · exact batch74
  · exact batch75
  · exact algebraic_batches 76 (by decide +kernel)
  · exact batch77
  · exact batch78
  · exact batch79
  · exact batch80
  · exact batch81
  · exact batch82
  · exact batch83
  · exact batch84
  · exact batch85
  · exact batch86
  · exact batch87
  · exact batch88
  · exact batch89
  · exact batch90
  · exact batch91
  · exact batch92
  · exact algebraic_batches 93 (by decide +kernel)
  · exact batch94
  · exact batch95

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block2
