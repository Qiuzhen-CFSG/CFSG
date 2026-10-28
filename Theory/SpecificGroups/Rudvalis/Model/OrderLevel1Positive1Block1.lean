module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Second block for the second positive Rudvalis level-1 generator

This certifies batches 39–77, covering representatives 195–389. Eight batches
follow from the existing free-cancellation certificates. The remaining batches
are checked at all 4060 permutation points in Lean's kernel, five representatives
at a time, and then assembled into the block certificate.

Source: the ATLAS-derived witnesses in `OrderLevel1Data` and `OrderChainData`,
as documented by `OrderCertificate/GenerateChain.g` and
`OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch39 : stepBatch 1 39 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch40 : stepBatch 1 40 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch41 : stepBatch 1 41 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch43 : stepBatch 1 43 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch44 : stepBatch 1 44 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch45 : stepBatch 1 45 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch47 : stepBatch 1 47 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch48 : stepBatch 1 48 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch49 : stepBatch 1 49 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch51 : stepBatch 1 51 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch53 : stepBatch 1 53 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch55 : stepBatch 1 55 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch56 : stepBatch 1 56 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch58 : stepBatch 1 58 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch59 : stepBatch 1 59 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch60 : stepBatch 1 60 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch61 : stepBatch 1 61 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch62 : stepBatch 1 62 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch63 : stepBatch 1 63 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch64 : stepBatch 1 64 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch67 : stepBatch 1 67 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch68 : stepBatch 1 68 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch69 : stepBatch 1 69 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch70 : stepBatch 1 70 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch71 : stepBatch 1 71 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch72 : stepBatch 1 72 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch73 : stepBatch 1 73 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch74 : stepBatch 1 74 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch75 : stepBatch 1 75 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch76 : stepBatch 1 76 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch77 : stepBatch 1 77 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- All 195 transitions in the second block satisfy the required identity. -/
public theorem block1 : block 1 := by
  intro b
  fin_cases b
  · exact batch39
  · exact batch40
  · exact batch41
  · exact algebraic_batches 42 (by decide +kernel)
  · exact batch43
  · exact batch44
  · exact batch45
  · exact algebraic_batches 46 (by decide +kernel)
  · exact batch47
  · exact batch48
  · exact batch49
  · exact algebraic_batches 50 (by decide +kernel)
  · exact batch51
  · exact algebraic_batches 52 (by decide +kernel)
  · exact batch53
  · exact algebraic_batches 54 (by decide +kernel)
  · exact batch55
  · exact batch56
  · exact algebraic_batches 57 (by decide +kernel)
  · exact batch58
  · exact batch59
  · exact batch60
  · exact batch61
  · exact batch62
  · exact batch63
  · exact batch64
  · exact algebraic_batches 65 (by decide +kernel)
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
  · exact batch76
  · exact batch77

end Rudvalis.OrderCertificate.OrderLevel1Positive1
