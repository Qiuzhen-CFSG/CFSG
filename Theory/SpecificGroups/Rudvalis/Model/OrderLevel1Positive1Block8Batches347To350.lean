module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block8Batches342To346
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 347–350

This certifies representatives 1735–1754. Each batch first uses proved free
cancellation when available and otherwise checks equality on all 4060 points
in Lean's kernel. The 4 batch proofs elaborate sequentially and assemble
into a certificate for this bounded range.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
The checker and its soundness proof are in `OrderLevel1Reduction`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch347 : stepBatch 1 347 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch348 : stepBatch 1 348 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch349 : stepBatch 1 349 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch350 : stepBatch 1 350 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 347 through 350. -/
public theorem segment347 (b : Fin 4) :
    stepBatch 1 ⟨347 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch347
  · exact batch348
  · exact batch349
  · exact batch350

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
