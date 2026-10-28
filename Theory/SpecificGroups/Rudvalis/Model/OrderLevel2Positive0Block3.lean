module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 0: representatives 192–255

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
private theorem batch48 : stepBatch 0 48 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch49 : stepBatch 0 49 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch50 : stepBatch 0 50 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch51 : stepBatch 0 51 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch52 : stepBatch 0 52 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch53 : stepBatch 0 53 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch54 : stepBatch 0 54 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch55 : stepBatch 0 55 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch56 : stepBatch 0 56 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch57 : stepBatch 0 57 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch58 : stepBatch 0 58 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch59 : stepBatch 0 59 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch60 : stepBatch 0 60 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch61 : stepBatch 0 61 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch62 : stepBatch 0 62 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch63 : stepBatch 0 63 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- Generator 0 transitions for representatives 192 through 255. -/
public theorem block3 : ∀ s : Fin 16,
    stepBatch 0 ⟨16 * 3 + s.val, by omega⟩ := by
  intro s
  fin_cases s
  · exact batch48
  · exact batch49
  · exact batch50
  · exact batch51
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
  · exact batch62
  · exact batch63

end Rudvalis.OrderCertificate.OrderLevel2Positive0
