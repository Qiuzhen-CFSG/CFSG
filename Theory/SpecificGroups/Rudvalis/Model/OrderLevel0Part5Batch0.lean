module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis forward transition certificates, part 5, batch 0

This batch checks both forward generators at twenty representatives. The
source witnesses are documented in `OrderLevel0Data`; each finite proof is
checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point0_0_0 : stepCheck 0 100 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_1 : stepCheck 0 101 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_2 : stepCheck 0 102 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_3 : stepCheck 0 103 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_4 : stepCheck 0 104 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_5 : stepCheck 0 105 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_6 : stepCheck 0 106 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_7 : stepCheck 0 107 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_8 : stepCheck 0 108 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_9 : stepCheck 0 109 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_10 : stepCheck 0 110 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_11 : stepCheck 0 111 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_12 : stepCheck 0 112 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_13 : stepCheck 0 113 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_14 : stepCheck 0 114 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_15 : stepCheck 0 115 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_16 : stepCheck 0 116 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_17 : stepCheck 0 117 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_18 : stepCheck 0 118 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_19 : stepCheck 0 119 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_0 : stepCheck 1 100 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_1 : stepCheck 1 101 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_2 : stepCheck 1 102 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_3 : stepCheck 1 103 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_4 : stepCheck 1 104 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_5 : stepCheck 1 105 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_6 : stepCheck 1 106 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_7 : stepCheck 1 107 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_8 : stepCheck 1 108 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_9 : stepCheck 1 109 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_10 : stepCheck 1 110 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_11 : stepCheck 1 111 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_12 : stepCheck 1 112 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_13 : stepCheck 1 113 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_14 : stepCheck 1 114 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_15 : stepCheck 1 115 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_16 : stepCheck 1 116 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_17 : stepCheck 1 117 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_18 : stepCheck 1 118 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_19 : stepCheck 1 119 := by
  decide +kernel

public theorem part5_checked0 : stepBatch 5 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point0_0_0
  · exact point0_0_1
  · exact point0_0_2
  · exact point0_0_3
  · exact point0_0_4
  · exact point0_0_5
  · exact point0_0_6
  · exact point0_0_7
  · exact point0_0_8
  · exact point0_0_9
  · exact point0_0_10
  · exact point0_0_11
  · exact point0_0_12
  · exact point0_0_13
  · exact point0_0_14
  · exact point0_0_15
  · exact point0_0_16
  · exact point0_0_17
  · exact point0_0_18
  · exact point0_0_19
  · exact point0_1_0
  · exact point0_1_1
  · exact point0_1_2
  · exact point0_1_3
  · exact point0_1_4
  · exact point0_1_5
  · exact point0_1_6
  · exact point0_1_7
  · exact point0_1_8
  · exact point0_1_9
  · exact point0_1_10
  · exact point0_1_11
  · exact point0_1_12
  · exact point0_1_13
  · exact point0_1_14
  · exact point0_1_15
  · exact point0_1_16
  · exact point0_1_17
  · exact point0_1_18
  · exact point0_1_19

end Rudvalis.OrderCertificate.ForwardReduction
