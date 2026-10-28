module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Reduction
import Mathlib.Tactic.FinCases
/-!
# The first three part-6 Rudvalis transition batches

These 120 transitions follow from word normalization with the generator
orders 2 and 4. They use the fixed witnesses documented in `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Base
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point0_0_0 : stepCheck 0 120 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_1 : stepCheck 0 121 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_2 : stepCheck 0 122 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_3 : stepCheck 0 123 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_4 : stepCheck 0 124 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_5 : stepCheck 0 125 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_6 : stepCheck 0 126 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_7 : stepCheck 0 127 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_8 : stepCheck 0 128 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_9 : stepCheck 0 129 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_10 : stepCheck 0 130 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_11 : stepCheck 0 131 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_12 : stepCheck 0 132 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_13 : stepCheck 0 133 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_14 : stepCheck 0 134 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_15 : stepCheck 0 135 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_16 : stepCheck 0 136 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_17 : stepCheck 0 137 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_18 : stepCheck 0 138 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_19 : stepCheck 0 139 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_0 : stepCheck 1 120 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_1 : stepCheck 1 121 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_2 : stepCheck 1 122 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_3 : stepCheck 1 123 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_4 : stepCheck 1 124 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_5 : stepCheck 1 125 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_6 : stepCheck 1 126 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_7 : stepCheck 1 127 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_8 : stepCheck 1 128 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_9 : stepCheck 1 129 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_10 : stepCheck 1 130 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_11 : stepCheck 1 131 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_12 : stepCheck 1 132 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_13 : stepCheck 1 133 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_14 : stepCheck 1 134 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_15 : stepCheck 1 135 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_16 : stepCheck 1 136 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_17 : stepCheck 1 137 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_18 : stepCheck 1 138 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_19 : stepCheck 1 139 := by
  decide +kernel

private theorem checked0 : stepBatch 6 := by
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

set_option maxHeartbeats 1600000 in
private theorem point1_0_0 : stepCheck 0 260 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_1 : stepCheck 0 261 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_2 : stepCheck 0 262 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_3 : stepCheck 0 263 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_4 : stepCheck 0 264 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_5 : stepCheck 0 265 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_6 : stepCheck 0 266 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_7 : stepCheck 0 267 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_8 : stepCheck 0 268 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_9 : stepCheck 0 269 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_10 : stepCheck 0 270 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_11 : stepCheck 0 271 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_12 : stepCheck 0 272 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_13 : stepCheck 0 273 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_14 : stepCheck 0 274 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_15 : stepCheck 0 275 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_16 : stepCheck 0 276 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_17 : stepCheck 0 277 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_18 : stepCheck 0 278 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_19 : stepCheck 0 279 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_0 : stepCheck 1 260 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_1 : stepCheck 1 261 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_2 : stepCheck 1 262 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_3 : stepCheck 1 263 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_4 : stepCheck 1 264 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_5 : stepCheck 1 265 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_6 : stepCheck 1 266 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_7 : stepCheck 1 267 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_8 : stepCheck 1 268 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_9 : stepCheck 1 269 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_10 : stepCheck 1 270 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_11 : stepCheck 1 271 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_12 : stepCheck 1 272 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_13 : stepCheck 1 273 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_14 : stepCheck 1 274 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_15 : stepCheck 1 275 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_16 : stepCheck 1 276 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_17 : stepCheck 1 277 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_18 : stepCheck 1 278 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_19 : stepCheck 1 279 := by
  decide +kernel

private theorem checked1 : stepBatch 13 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point1_0_0
  · exact point1_0_1
  · exact point1_0_2
  · exact point1_0_3
  · exact point1_0_4
  · exact point1_0_5
  · exact point1_0_6
  · exact point1_0_7
  · exact point1_0_8
  · exact point1_0_9
  · exact point1_0_10
  · exact point1_0_11
  · exact point1_0_12
  · exact point1_0_13
  · exact point1_0_14
  · exact point1_0_15
  · exact point1_0_16
  · exact point1_0_17
  · exact point1_0_18
  · exact point1_0_19
  · exact point1_1_0
  · exact point1_1_1
  · exact point1_1_2
  · exact point1_1_3
  · exact point1_1_4
  · exact point1_1_5
  · exact point1_1_6
  · exact point1_1_7
  · exact point1_1_8
  · exact point1_1_9
  · exact point1_1_10
  · exact point1_1_11
  · exact point1_1_12
  · exact point1_1_13
  · exact point1_1_14
  · exact point1_1_15
  · exact point1_1_16
  · exact point1_1_17
  · exact point1_1_18
  · exact point1_1_19

set_option maxHeartbeats 1600000 in
private theorem point2_0_0 : stepCheck 0 400 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_1 : stepCheck 0 401 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_2 : stepCheck 0 402 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_3 : stepCheck 0 403 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_4 : stepCheck 0 404 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_5 : stepCheck 0 405 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_6 : stepCheck 0 406 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_7 : stepCheck 0 407 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_8 : stepCheck 0 408 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_9 : stepCheck 0 409 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_10 : stepCheck 0 410 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_11 : stepCheck 0 411 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_12 : stepCheck 0 412 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_13 : stepCheck 0 413 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_14 : stepCheck 0 414 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_15 : stepCheck 0 415 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_16 : stepCheck 0 416 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_17 : stepCheck 0 417 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_18 : stepCheck 0 418 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_19 : stepCheck 0 419 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_0 : stepCheck 1 400 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_1 : stepCheck 1 401 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_2 : stepCheck 1 402 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_3 : stepCheck 1 403 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_4 : stepCheck 1 404 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_5 : stepCheck 1 405 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_6 : stepCheck 1 406 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_7 : stepCheck 1 407 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_8 : stepCheck 1 408 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_9 : stepCheck 1 409 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_10 : stepCheck 1 410 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_11 : stepCheck 1 411 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_12 : stepCheck 1 412 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_13 : stepCheck 1 413 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_14 : stepCheck 1 414 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_15 : stepCheck 1 415 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_16 : stepCheck 1 416 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_17 : stepCheck 1 417 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_18 : stepCheck 1 418 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_19 : stepCheck 1 419 := by
  decide +kernel

private theorem checked2 : stepBatch 20 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point2_0_0
  · exact point2_0_1
  · exact point2_0_2
  · exact point2_0_3
  · exact point2_0_4
  · exact point2_0_5
  · exact point2_0_6
  · exact point2_0_7
  · exact point2_0_8
  · exact point2_0_9
  · exact point2_0_10
  · exact point2_0_11
  · exact point2_0_12
  · exact point2_0_13
  · exact point2_0_14
  · exact point2_0_15
  · exact point2_0_16
  · exact point2_0_17
  · exact point2_0_18
  · exact point2_0_19
  · exact point2_1_0
  · exact point2_1_1
  · exact point2_1_2
  · exact point2_1_3
  · exact point2_1_4
  · exact point2_1_5
  · exact point2_1_6
  · exact point2_1_7
  · exact point2_1_8
  · exact point2_1_9
  · exact point2_1_10
  · exact point2_1_11
  · exact point2_1_12
  · exact point2_1_13
  · exact point2_1_14
  · exact point2_1_15
  · exact point2_1_16
  · exact point2_1_17
  · exact point2_1_18
  · exact point2_1_19

public theorem first (b : Fin 3) : stepBatch ⟨7 * b.val + 6, by omega⟩ := by
  fin_cases b
  · exact checked0
  · exact checked1
  · exact checked2

end Rudvalis.OrderCertificate.ForwardReduction.Part6Base
