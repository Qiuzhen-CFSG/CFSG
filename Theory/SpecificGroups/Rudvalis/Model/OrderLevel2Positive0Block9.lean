module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 0: representatives 576–639

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
private theorem batch144 : stepBatch 0 144 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch145 : stepBatch 0 145 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch146 : stepBatch 0 146 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch147 : stepBatch 0 147 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch148 : stepBatch 0 148 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch149 : stepBatch 0 149 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch150 : stepBatch 0 150 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch151 : stepBatch 0 151 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch152 : stepBatch 0 152 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch153 : stepBatch 0 153 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch154 : stepBatch 0 154 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch155 : stepBatch 0 155 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch156 : stepBatch 0 156 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch157 : stepBatch 0 157 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch158 : stepBatch 0 158 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch159 : stepBatch 0 159 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- Generator 0 transitions for representatives 576 through 639. -/
public theorem block9 : ∀ s : Fin 16,
    stepBatch 0 ⟨16 * 9 + s.val, by omega⟩ := by
  intro s
  fin_cases s
  · exact batch144
  · exact batch145
  · exact batch146
  · exact batch147
  · exact batch148
  · exact batch149
  · exact batch150
  · exact batch151
  · exact batch152
  · exact batch153
  · exact batch154
  · exact batch155
  · exact batch156
  · exact batch157
  · exact batch158
  · exact batch159

end Rudvalis.OrderCertificate.OrderLevel2Positive0
