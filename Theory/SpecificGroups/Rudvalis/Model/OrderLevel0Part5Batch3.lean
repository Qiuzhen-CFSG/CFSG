module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis forward transition certificates, part 5, batch 3

This batch checks both forward generators at twenty representatives. The
source witnesses are documented in `OrderLevel0Data`; each finite proof is
checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point3_0_0 : stepCheck 0 520 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_1 : stepCheck 0 521 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_2 : stepCheck 0 522 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_3 : stepCheck 0 523 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_4 : stepCheck 0 524 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_5 : stepCheck 0 525 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_6 : stepCheck 0 526 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_7 : stepCheck 0 527 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_8 : stepCheck 0 528 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_9 : stepCheck 0 529 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_10 : stepCheck 0 530 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_11 : stepCheck 0 531 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_12 : stepCheck 0 532 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_13 : stepCheck 0 533 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_14 : stepCheck 0 534 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_15 : stepCheck 0 535 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_16 : stepCheck 0 536 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_17 : stepCheck 0 537 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_18 : stepCheck 0 538 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_19 : stepCheck 0 539 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_0 : stepCheck 1 520 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_1 : stepCheck 1 521 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_2 : stepCheck 1 522 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_3 : stepCheck 1 523 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_4 : stepCheck 1 524 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_5 : stepCheck 1 525 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_6 : stepCheck 1 526 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_7 : stepCheck 1 527 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_8 : stepCheck 1 528 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_9 : stepCheck 1 529 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_10 : stepCheck 1 530 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_11 : stepCheck 1 531 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_12 : stepCheck 1 532 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_13 : stepCheck 1 533 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_14 : stepCheck 1 534 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_15 : stepCheck 1 535 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_16 : stepCheck 1 536 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_17 : stepCheck 1 537 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_18 : stepCheck 1 538 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_19 : stepCheck 1 539 := by
  decide +kernel

public theorem part5_checked3 : stepBatch 26 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point3_0_0
  · exact point3_0_1
  · exact point3_0_2
  · exact point3_0_3
  · exact point3_0_4
  · exact point3_0_5
  · exact point3_0_6
  · exact point3_0_7
  · exact point3_0_8
  · exact point3_0_9
  · exact point3_0_10
  · exact point3_0_11
  · exact point3_0_12
  · exact point3_0_13
  · exact point3_0_14
  · exact point3_0_15
  · exact point3_0_16
  · exact point3_0_17
  · exact point3_0_18
  · exact point3_0_19
  · exact point3_1_0
  · exact point3_1_1
  · exact point3_1_2
  · exact point3_1_3
  · exact point3_1_4
  · exact point3_1_5
  · exact point3_1_6
  · exact point3_1_7
  · exact point3_1_8
  · exact point3_1_9
  · exact point3_1_10
  · exact point3_1_11
  · exact point3_1_12
  · exact point3_1_13
  · exact point3_1_14
  · exact point3_1_15
  · exact point3_1_16
  · exact point3_1_17
  · exact point3_1_18
  · exact point3_1_19

end Rudvalis.OrderCertificate.ForwardReduction
