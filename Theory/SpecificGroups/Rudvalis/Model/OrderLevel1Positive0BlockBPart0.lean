module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive-generator-0 transitions: batches 100–113

Each batch certifies five level-1 orbit representatives by free cancellation or
pointwise equality on all 4060 points, checked in Lean's kernel. These bounded
compilation units checkpoint the certificate assembled in
`OrderLevel1Positive0BlockB`.

Source: the ATLAS-derived witnesses documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockB
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch100 : stepBatch 0 100 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch101 : stepBatch 0 101 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch102 : stepBatch 0 102 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch103 : stepBatch 0 103 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch104 : stepBatch 0 104 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch105 : stepBatch 0 105 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch106 : stepBatch 0 106 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch107 : stepBatch 0 107 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch108 : stepBatch 0 108 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch109 : stepBatch 0 109 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch110 : stepBatch 0 110 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch111 : stepBatch 0 111 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch112 : stepBatch 0 112 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch113 : stepBatch 0 113 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The fourteen batches starting at 100 satisfy the transition identity. -/
public theorem part0 (b : Fin 14) : stepBatch 0 ⟨100 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch100
  · exact batch101
  · exact batch102
  · exact batch103
  · exact batch104
  · exact batch105
  · exact batch106
  · exact batch107
  · exact batch108
  · exact batch109
  · exact batch110
  · exact batch111
  · exact batch112
  · exact batch113

end Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockB
