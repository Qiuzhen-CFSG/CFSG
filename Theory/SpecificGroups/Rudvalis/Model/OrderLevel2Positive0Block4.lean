module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 0: representatives 256–319

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
private theorem batch64 : stepBatch 0 64 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch65 : stepBatch 0 65 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch66 : stepBatch 0 66 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch67 : stepBatch 0 67 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch68 : stepBatch 0 68 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch69 : stepBatch 0 69 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch70 : stepBatch 0 70 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch71 : stepBatch 0 71 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch72 : stepBatch 0 72 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch73 : stepBatch 0 73 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch74 : stepBatch 0 74 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch75 : stepBatch 0 75 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch76 : stepBatch 0 76 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch77 : stepBatch 0 77 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch78 : stepBatch 0 78 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch79 : stepBatch 0 79 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- Generator 0 transitions for representatives 256 through 319. -/
public theorem block4 : ∀ s : Fin 16,
    stepBatch 0 ⟨16 * 4 + s.val, by omega⟩ := by
  intro s
  fin_cases s
  · exact batch64
  · exact batch65
  · exact batch66
  · exact batch67
  · exact batch68
  · exact batch69
  · exact batch70
  · exact batch71
  · exact batch72
  · exact batch73
  · exact batch74
  · exact batch75
  · exact batch76
  · exact batch77
  · exact batch78
  · exact batch79

end Rudvalis.OrderCertificate.OrderLevel2Positive0
