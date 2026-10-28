module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 0: representatives 448–511

The sixteen batches below certify the forward transition on this range.
Free cancellation is attempted first; all remaining permutation equalities
are checked on all 4060 points by the Lean kernel.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive0
open Level2Reduction
set_option Elab.async false

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

set_option maxRecDepth 30000 in
private theorem batch114 : stepBatch 0 114 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch115 : stepBatch 0 115 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch116 : stepBatch 0 116 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch117 : stepBatch 0 117 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch118 : stepBatch 0 118 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch119 : stepBatch 0 119 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch120 : stepBatch 0 120 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch121 : stepBatch 0 121 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch122 : stepBatch 0 122 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch123 : stepBatch 0 123 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch124 : stepBatch 0 124 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch125 : stepBatch 0 125 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch126 : stepBatch 0 126 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch127 : stepBatch 0 127 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- Generator 0 transitions for representatives 448 through 511. -/
public theorem block7 : ∀ s : Fin 16,
    stepBatch 0 ⟨16 * 7 + s.val, by omega⟩ := by
  intro s
  fin_cases s
  · exact batch112
  · exact batch113
  · exact batch114
  · exact batch115
  · exact batch116
  · exact batch117
  · exact batch118
  · exact batch119
  · exact batch120
  · exact batch121
  · exact batch122
  · exact batch123
  · exact batch124
  · exact batch125
  · exact batch126
  · exact batch127

end Rudvalis.OrderCertificate.OrderLevel2Positive0
