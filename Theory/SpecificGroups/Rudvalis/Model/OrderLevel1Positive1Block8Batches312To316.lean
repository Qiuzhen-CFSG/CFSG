module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 312–316

This certifies representatives 1560–1584. Each batch first uses proved free
cancellation when available and otherwise checks equality on all 4060 points
in Lean's kernel. The five batch proofs elaborate sequentially and assemble
into a certificate for this bounded range.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch312 : stepBatch 1 312 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch313 : stepBatch 1 313 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch314 : stepBatch 1 314 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch315 : stepBatch 1 315 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch316 : stepBatch 1 316 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 312 through 316. -/
public theorem segment312 (b : Fin 5) :
    stepBatch 1 ⟨312 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch312
  · exact batch313
  · exact batch314
  · exact batch315
  · exact batch316

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
