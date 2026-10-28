module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block8Batches337To341
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 342–346

This certifies representatives 1710–1734. Each batch first uses proved free
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
private theorem batch342 : stepBatch 1 342 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch343 : stepBatch 1 343 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch344 : stepBatch 1 344 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch345 : stepBatch 1 345 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch346 : stepBatch 1 346 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 342 through 346. -/
public theorem segment342 (b : Fin 5) :
    stepBatch 1 ⟨342 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch342
  · exact batch343
  · exact batch344
  · exact batch345
  · exact batch346

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
