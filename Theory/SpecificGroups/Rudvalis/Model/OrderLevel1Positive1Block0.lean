module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis positive generator 1: batches 0–38

This certifies the transitions for representatives 0–194. Free word cancellation
handles the algebraic batches; each remaining batch is checked separately on the
4060 permutation points by the Lean kernel. The 39 certificates assemble to block 0.

Source: the ATLAS witnesses recorded in `OrderLevel1Data` and `OrderChainData`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch1 : stepBatch 1 1 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch3 : stepBatch 1 3 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch4 : stepBatch 1 4 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch5 : stepBatch 1 5 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch7 : stepBatch 1 7 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch13 : stepBatch 1 13 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch15 : stepBatch 1 15 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch16 : stepBatch 1 16 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch17 : stepBatch 1 17 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch21 : stepBatch 1 21 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch22 : stepBatch 1 22 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch24 : stepBatch 1 24 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch25 : stepBatch 1 25 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch26 : stepBatch 1 26 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch28 : stepBatch 1 28 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch29 : stepBatch 1 29 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch30 : stepBatch 1 30 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch32 : stepBatch 1 32 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch33 : stepBatch 1 33 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch34 : stepBatch 1 34 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch35 : stepBatch 1 35 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch36 : stepBatch 1 36 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch37 : stepBatch 1 37 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The first 195 representatives satisfy the second positive transition. -/
public theorem block0 : block 0 := by
  intro b
  fin_cases b
  · exact algebraic_batches 0 (by decide +kernel)
  · exact batch1
  · exact algebraic_batches 2 (by decide +kernel)
  · exact batch3
  · exact batch4
  · exact batch5
  · exact algebraic_batches 6 (by decide +kernel)
  · exact batch7
  · exact algebraic_batches 8 (by decide +kernel)
  · exact algebraic_batches 9 (by decide +kernel)
  · exact algebraic_batches 10 (by decide +kernel)
  · exact algebraic_batches 11 (by decide +kernel)
  · exact algebraic_batches 12 (by decide +kernel)
  · exact batch13
  · exact algebraic_batches 14 (by decide +kernel)
  · exact batch15
  · exact batch16
  · exact batch17
  · exact algebraic_batches 18 (by decide +kernel)
  · exact algebraic_batches 19 (by decide +kernel)
  · exact algebraic_batches 20 (by decide +kernel)
  · exact batch21
  · exact batch22
  · exact algebraic_batches 23 (by decide +kernel)
  · exact batch24
  · exact batch25
  · exact batch26
  · exact algebraic_batches 27 (by decide +kernel)
  · exact batch28
  · exact batch29
  · exact batch30
  · exact algebraic_batches 31 (by decide +kernel)
  · exact batch32
  · exact batch33
  · exact batch34
  · exact batch35
  · exact batch36
  · exact batch37
  · exact algebraic_batches 38 (by decide +kernel)

end Rudvalis.OrderCertificate.OrderLevel1Positive1
