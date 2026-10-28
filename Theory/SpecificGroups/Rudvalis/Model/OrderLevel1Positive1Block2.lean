module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Third block of the second positive Rudvalis level-1 transition

This certifies batches 78 through 116, covering orbit representatives 390 through
584. Three batches follow from the existing free-cancellation certificate. For
each remaining batch, the bounded checker verifies the five transitions on all
4060 points in Lean's kernel, using free cancellation where possible.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch78 : stepBatch 1 78 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch79 : stepBatch 1 79 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch80 : stepBatch 1 80 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch81 : stepBatch 1 81 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch82 : stepBatch 1 82 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch83 : stepBatch 1 83 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch84 : stepBatch 1 84 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch85 : stepBatch 1 85 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch86 : stepBatch 1 86 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch87 : stepBatch 1 87 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch88 : stepBatch 1 88 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch90 : stepBatch 1 90 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch91 : stepBatch 1 91 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch92 : stepBatch 1 92 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch93 : stepBatch 1 93 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch94 : stepBatch 1 94 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch95 : stepBatch 1 95 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch96 : stepBatch 1 96 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch97 : stepBatch 1 97 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch98 : stepBatch 1 98 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch100 : stepBatch 1 100 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch101 : stepBatch 1 101 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch102 : stepBatch 1 102 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch103 : stepBatch 1 103 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch104 : stepBatch 1 104 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch105 : stepBatch 1 105 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch107 : stepBatch 1 107 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch108 : stepBatch 1 108 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch109 : stepBatch 1 109 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch110 : stepBatch 1 110 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch111 : stepBatch 1 111 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch112 : stepBatch 1 112 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch113 : stepBatch 1 113 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch114 : stepBatch 1 114 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch115 : stepBatch 1 115 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch116 : stepBatch 1 116 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- Representatives 390 through 584 satisfy the second positive transition. -/
public theorem block2 : block 2 := by
  intro b
  fin_cases b
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
  · exact algebraic_batches 89 (by decide +kernel)
  · exact batch90
  · exact batch91
  · exact batch92
  · exact batch93
  · exact batch94
  · exact batch95
  · exact batch96
  · exact batch97
  · exact batch98
  · exact algebraic_batches 99 (by decide +kernel)
  · exact batch100
  · exact batch101
  · exact batch102
  · exact batch103
  · exact batch104
  · exact batch105
  · exact algebraic_batches 106 (by decide +kernel)
  · exact batch107
  · exact batch108
  · exact batch109
  · exact batch110
  · exact batch111
  · exact batch112
  · exact batch113
  · exact batch114
  · exact batch115
  · exact batch116

end Rudvalis.OrderCertificate.OrderLevel1Positive1
