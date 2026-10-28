module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis forward transition certificates, part 5, batch 5

This batch checks both forward generators at twenty representatives. The
source witnesses are documented in `OrderLevel0Data`; each finite proof is
checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point5_0_0 : stepCheck 0 800 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_1 : stepCheck 0 801 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_2 : stepCheck 0 802 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_3 : stepCheck 0 803 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_4 : stepCheck 0 804 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_5 : stepCheck 0 805 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_6 : stepCheck 0 806 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_7 : stepCheck 0 807 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_8 : stepCheck 0 808 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_9 : stepCheck 0 809 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_10 : stepCheck 0 810 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_11 : stepCheck 0 811 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_12 : stepCheck 0 812 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_13 : stepCheck 0 813 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_14 : stepCheck 0 814 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_15 : stepCheck 0 815 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_16 : stepCheck 0 816 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_17 : stepCheck 0 817 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_18 : stepCheck 0 818 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_19 : stepCheck 0 819 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_0 : stepCheck 1 800 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_1 : stepCheck 1 801 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_2 : stepCheck 1 802 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_3 : stepCheck 1 803 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_4 : stepCheck 1 804 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_5 : stepCheck 1 805 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_6 : stepCheck 1 806 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_7 : stepCheck 1 807 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_8 : stepCheck 1 808 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_9 : stepCheck 1 809 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_10 : stepCheck 1 810 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_11 : stepCheck 1 811 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_12 : stepCheck 1 812 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_13 : stepCheck 1 813 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_14 : stepCheck 1 814 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_15 : stepCheck 1 815 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_16 : stepCheck 1 816 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_17 : stepCheck 1 817 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_18 : stepCheck 1 818 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_19 : stepCheck 1 819 := by
  decide +kernel

public theorem part5_checked5 : stepBatch 40 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point5_0_0
  · exact point5_0_1
  · exact point5_0_2
  · exact point5_0_3
  · exact point5_0_4
  · exact point5_0_5
  · exact point5_0_6
  · exact point5_0_7
  · exact point5_0_8
  · exact point5_0_9
  · exact point5_0_10
  · exact point5_0_11
  · exact point5_0_12
  · exact point5_0_13
  · exact point5_0_14
  · exact point5_0_15
  · exact point5_0_16
  · exact point5_0_17
  · exact point5_0_18
  · exact point5_0_19
  · exact point5_1_0
  · exact point5_1_1
  · exact point5_1_2
  · exact point5_1_3
  · exact point5_1_4
  · exact point5_1_5
  · exact point5_1_6
  · exact point5_1_7
  · exact point5_1_8
  · exact point5_1_9
  · exact point5_1_10
  · exact point5_1_11
  · exact point5_1_12
  · exact point5_1_13
  · exact point5_1_14
  · exact point5_1_15
  · exact point5_1_16
  · exact point5_1_17
  · exact point5_1_18
  · exact point5_1_19

end Rudvalis.OrderCertificate.ForwardReduction
