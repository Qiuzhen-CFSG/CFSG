module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis forward transition certificates, part 5, batch 4

This batch checks both forward generators at twenty representatives. The
source witnesses are documented in `OrderLevel0Data`; each finite proof is
checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point4_0_0 : stepCheck 0 660 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_1 : stepCheck 0 661 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_2 : stepCheck 0 662 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_3 : stepCheck 0 663 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_4 : stepCheck 0 664 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_5 : stepCheck 0 665 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_6 : stepCheck 0 666 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_7 : stepCheck 0 667 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_8 : stepCheck 0 668 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_9 : stepCheck 0 669 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_10 : stepCheck 0 670 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_11 : stepCheck 0 671 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_12 : stepCheck 0 672 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_13 : stepCheck 0 673 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_14 : stepCheck 0 674 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_15 : stepCheck 0 675 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_16 : stepCheck 0 676 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_17 : stepCheck 0 677 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_18 : stepCheck 0 678 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_19 : stepCheck 0 679 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_0 : stepCheck 1 660 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_1 : stepCheck 1 661 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_2 : stepCheck 1 662 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_3 : stepCheck 1 663 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_4 : stepCheck 1 664 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_5 : stepCheck 1 665 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_6 : stepCheck 1 666 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_7 : stepCheck 1 667 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_8 : stepCheck 1 668 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_9 : stepCheck 1 669 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_10 : stepCheck 1 670 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_11 : stepCheck 1 671 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_12 : stepCheck 1 672 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_13 : stepCheck 1 673 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_14 : stepCheck 1 674 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_15 : stepCheck 1 675 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_16 : stepCheck 1 676 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_17 : stepCheck 1 677 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_18 : stepCheck 1 678 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_19 : stepCheck 1 679 := by
  decide +kernel

public theorem part5_checked4 : stepBatch 33 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point4_0_0
  · exact point4_0_1
  · exact point4_0_2
  · exact point4_0_3
  · exact point4_0_4
  · exact point4_0_5
  · exact point4_0_6
  · exact point4_0_7
  · exact point4_0_8
  · exact point4_0_9
  · exact point4_0_10
  · exact point4_0_11
  · exact point4_0_12
  · exact point4_0_13
  · exact point4_0_14
  · exact point4_0_15
  · exact point4_0_16
  · exact point4_0_17
  · exact point4_0_18
  · exact point4_0_19
  · exact point4_1_0
  · exact point4_1_1
  · exact point4_1_2
  · exact point4_1_3
  · exact point4_1_4
  · exact point4_1_5
  · exact point4_1_6
  · exact point4_1_7
  · exact point4_1_8
  · exact point4_1_9
  · exact point4_1_10
  · exact point4_1_11
  · exact point4_1_12
  · exact point4_1_13
  · exact point4_1_14
  · exact point4_1_15
  · exact point4_1_16
  · exact point4_1_17
  · exact point4_1_18
  · exact point4_1_19

end Rudvalis.OrderCertificate.ForwardReduction
