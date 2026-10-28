module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Fast
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Algebraic
import Mathlib.Tactic.FinCases
/-!
# Rudvalis part-4 batch 16

Certify the forty forward transitions in batch 16. Algebraic checks use
`OrderLevel0Part4Algebraic`; residual checks expand compressed factors and
verify their action on all 4060 points through certified lookup tables.
Source: the fixed ATLAS witnesses documented in `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
set_option maxRecDepth 30000
set_option Elab.async false

private theorem point16_0_0 : stepCheck 0 2320 := Or.inl algebraic16_0_0

private def point16_0_1Word : List (Fin 71) := [7, 23, 16, 47, 24, 31, 43]
private theorem point16_0_1Expanded :
    point16_0_1Word.flatMap Part4Group1Fast.word = L0Factor 0 2321 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_0_1Check : Part4Group1Fast.check 0 2321 point16_0_1Word = true := by
  decide +kernel
private theorem point16_0_1 : stepCheck 0 2321 :=
  Part4Group1Fast.ofCheck 0 2321 point16_0_1Word point16_0_1Expanded point16_0_1Check

private theorem point16_0_2 : stepCheck 0 2322 := Or.inl algebraic16_0_2

private theorem point16_0_3 : stepCheck 0 2323 := Or.inl algebraic16_0_3

private theorem point16_0_4 : stepCheck 0 2324 := Or.inl algebraic16_0_4

private theorem point16_0_5 : stepCheck 0 2325 := Or.inl algebraic16_0_5

private def point16_0_6Word : List (Fin 71) := [2, 16, 7, 7, 34, 59, 5, 55]
private theorem point16_0_6Expanded :
    point16_0_6Word.flatMap Part4Group1Fast.word = L0Factor 0 2326 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_0_6Check : Part4Group1Fast.check 0 2326 point16_0_6Word = true := by
  decide +kernel
private theorem point16_0_6 : stepCheck 0 2326 :=
  Part4Group1Fast.ofCheck 0 2326 point16_0_6Word point16_0_6Expanded point16_0_6Check

private def point16_0_7Word : List (Fin 71) := [0, 0, 25, 68, 38, 23, 51, 42, 70]
private theorem point16_0_7Expanded :
    point16_0_7Word.flatMap Part4Group1Fast.word = L0Factor 0 2327 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_0_7Check : Part4Group1Fast.check 0 2327 point16_0_7Word = true := by
  decide +kernel
private theorem point16_0_7 : stepCheck 0 2327 :=
  Part4Group1Fast.ofCheck 0 2327 point16_0_7Word point16_0_7Expanded point16_0_7Check

private def point16_0_8Word : List (Fin 71) := [6, 7, 7, 0, 37, 54, 18, 40, 24, 10, 70]
private theorem point16_0_8Expanded :
    point16_0_8Word.flatMap Part4Group1Fast.word = L0Factor 0 2328 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_0_8Check : Part4Group1Fast.check 0 2328 point16_0_8Word = true := by
  decide +kernel
private theorem point16_0_8 : stepCheck 0 2328 :=
  Part4Group1Fast.ofCheck 0 2328 point16_0_8Word point16_0_8Expanded point16_0_8Check

private theorem point16_0_9 : stepCheck 0 2329 := Or.inl algebraic16_0_9

private theorem point16_0_10 : stepCheck 0 2330 := Or.inl algebraic16_0_10

private theorem point16_0_11 : stepCheck 0 2331 := Or.inl algebraic16_0_11

private theorem point16_0_12 : stepCheck 0 2332 := Or.inl algebraic16_0_12

private def point16_0_13Word : List (Fin 71) := [2, 8, 25, 1, 28, 38, 53]
private theorem point16_0_13Expanded :
    point16_0_13Word.flatMap Part4Group1Fast.word = L0Factor 0 2333 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_0_13Check : Part4Group1Fast.check 0 2333 point16_0_13Word = true := by
  decide +kernel
private theorem point16_0_13 : stepCheck 0 2333 :=
  Part4Group1Fast.ofCheck 0 2333 point16_0_13Word point16_0_13Expanded point16_0_13Check

private theorem point16_0_14 : stepCheck 0 2334 := Or.inl algebraic16_0_14

private def point16_0_15Word : List (Fin 71) := [54, 1, 4, 2, 9, 50, 42, 50, 42, 67]
private theorem point16_0_15Expanded :
    point16_0_15Word.flatMap Part4Group1Fast.word = L0Factor 0 2335 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_0_15Check : Part4Group1Fast.check 0 2335 point16_0_15Word = true := by
  decide +kernel
private theorem point16_0_15 : stepCheck 0 2335 :=
  Part4Group1Fast.ofCheck 0 2335 point16_0_15Word point16_0_15Expanded point16_0_15Check

private theorem point16_0_16 : stepCheck 0 2336 := Or.inl algebraic16_0_16

private theorem point16_0_17 : stepCheck 0 2337 := Or.inl algebraic16_0_17

private theorem point16_0_18 : stepCheck 0 2338 := Or.inl algebraic16_0_18

private theorem point16_0_19 : stepCheck 0 2339 := Or.inl algebraic16_0_19

private theorem point16_1_0 : stepCheck 1 2320 := Or.inl algebraic16_1_0

private def point16_1_1Word : List (Fin 71) := [0, 6, 7, 0, 42, 68, 38, 14, 49, 10, 69]
private theorem point16_1_1Expanded :
    point16_1_1Word.flatMap Part4Group1Fast.word = L0Factor 1 2321 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_1_1Check : Part4Group1Fast.check 1 2321 point16_1_1Word = true := by
  decide +kernel
private theorem point16_1_1 : stepCheck 1 2321 :=
  Part4Group1Fast.ofCheck 1 2321 point16_1_1Word point16_1_1Expanded point16_1_1Check

private def point16_1_2Word : List (Fin 71) := [64, 4, 6, 61, 34, 38, 8, 18, 34, 55, 39]
private theorem point16_1_2Expanded :
    point16_1_2Word.flatMap Part4Group1Fast.word = L0Factor 1 2322 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_1_2Check : Part4Group1Fast.check 1 2322 point16_1_2Word = true := by
  decide +kernel
private theorem point16_1_2 : stepCheck 1 2322 :=
  Part4Group1Fast.ofCheck 1 2322 point16_1_2Word point16_1_2Expanded point16_1_2Check

private def point16_1_3Word : List (Fin 71) := [51, 3, 9, 10, 22, 42, 43, 39]
private theorem point16_1_3Expanded :
    point16_1_3Word.flatMap Part4Group1Fast.word = L0Factor 1 2323 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_1_3Check : Part4Group1Fast.check 1 2323 point16_1_3Word = true := by
  decide +kernel
private theorem point16_1_3 : stepCheck 1 2323 :=
  Part4Group1Fast.ofCheck 1 2323 point16_1_3Word point16_1_3Expanded point16_1_3Check

private theorem point16_1_4 : stepCheck 1 2324 := Or.inl algebraic16_1_4

private theorem point16_1_5 : stepCheck 1 2325 := Or.inl algebraic16_1_5

private theorem point16_1_6 : stepCheck 1 2326 := Or.inl algebraic16_1_6

private theorem point16_1_7 : stepCheck 1 2327 := Or.inl algebraic16_1_7

private theorem point16_1_8 : stepCheck 1 2328 := Or.inl algebraic16_1_8

private theorem point16_1_9 : stepCheck 1 2329 := Or.inl algebraic16_1_9

private theorem point16_1_10 : stepCheck 1 2330 := Or.inl algebraic16_1_10

private def point16_1_11Word : List (Fin 71) := [7, 16, 11, 56, 45]
private theorem point16_1_11Expanded :
    point16_1_11Word.flatMap Part4Group1Fast.word = L0Factor 1 2331 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_1_11Check : Part4Group1Fast.check 1 2331 point16_1_11Word = true := by
  decide +kernel
private theorem point16_1_11 : stepCheck 1 2331 :=
  Part4Group1Fast.ofCheck 1 2331 point16_1_11Word point16_1_11Expanded point16_1_11Check

private def point16_1_12Word : List (Fin 71) := [54, 6, 2, 20, 1, 23, 51, 31, 10, 67, 39]
private theorem point16_1_12Expanded :
    point16_1_12Word.flatMap Part4Group1Fast.word = L0Factor 1 2332 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point16_1_12Check : Part4Group1Fast.check 1 2332 point16_1_12Word = true := by
  decide +kernel
private theorem point16_1_12 : stepCheck 1 2332 :=
  Part4Group1Fast.ofCheck 1 2332 point16_1_12Word point16_1_12Expanded point16_1_12Check

private theorem point16_1_13 : stepCheck 1 2333 := Or.inl algebraic16_1_13

private theorem point16_1_14 : stepCheck 1 2334 := Or.inl algebraic16_1_14

private theorem point16_1_15 : stepCheck 1 2335 := Or.inl algebraic16_1_15

private theorem point16_1_16 : stepCheck 1 2336 := Or.inl algebraic16_1_16

private theorem point16_1_17 : stepCheck 1 2337 := Or.inl algebraic16_1_17

private theorem point16_1_18 : stepCheck 1 2338 := Or.inl algebraic16_1_18

private theorem point16_1_19 : stepCheck 1 2339 := Or.inl algebraic16_1_19

public theorem group1Batch16 : stepBatch 116 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point16_0_0
  · exact point16_0_1
  · exact point16_0_2
  · exact point16_0_3
  · exact point16_0_4
  · exact point16_0_5
  · exact point16_0_6
  · exact point16_0_7
  · exact point16_0_8
  · exact point16_0_9
  · exact point16_0_10
  · exact point16_0_11
  · exact point16_0_12
  · exact point16_0_13
  · exact point16_0_14
  · exact point16_0_15
  · exact point16_0_16
  · exact point16_0_17
  · exact point16_0_18
  · exact point16_0_19
  · exact point16_1_0
  · exact point16_1_1
  · exact point16_1_2
  · exact point16_1_3
  · exact point16_1_4
  · exact point16_1_5
  · exact point16_1_6
  · exact point16_1_7
  · exact point16_1_8
  · exact point16_1_9
  · exact point16_1_10
  · exact point16_1_11
  · exact point16_1_12
  · exact point16_1_13
  · exact point16_1_14
  · exact point16_1_15
  · exact point16_1_16
  · exact point16_1_17
  · exact point16_1_18
  · exact point16_1_19


end Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
