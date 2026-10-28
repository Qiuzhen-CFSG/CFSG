module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 337–341

This certifies representatives 1685–1709. Each batch first uses proved free
cancellation when available and otherwise checks equality on all 4060 points
in Lean's kernel. The 5 batch proofs elaborate sequentially and assemble
into a certificate for this bounded range.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
The checker and its soundness proof are in `OrderLevel1Reduction`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch337 : stepBatch 1 337 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch338 : stepBatch 1 338 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch339 : stepBatch 1 339 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch340 : stepBatch 1 340 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch341 : stepBatch 1 341 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 337 through 341. -/
public theorem segment337 (b : Fin 5) :
    stepBatch 1 ⟨337 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch337
  · exact batch338
  · exact batch339
  · exact batch340
  · exact batch341

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
