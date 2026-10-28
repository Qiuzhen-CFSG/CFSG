module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 327–331

This certifies representatives 1635–1659. Each batch first uses proved free
cancellation when available and otherwise checks equality on all 4060 points
in Lean's kernel. The five batch proofs elaborate sequentially and assemble
into a certificate for this bounded range.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`;
checker correctness is proved in `OrderLevel1Reduction`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch327 : stepBatch 1 327 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch328 : stepBatch 1 328 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch329 : stepBatch 1 329 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch330 : stepBatch 1 330 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch331 : stepBatch 1 331 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 327 through 331. -/
public theorem segment327 (b : Fin 5) :
    stepBatch 1 ⟨327 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch327
  · exact batch328
  · exact batch329
  · exact batch330
  · exact batch331

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
