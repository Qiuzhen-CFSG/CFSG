module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Fast
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Algebraic
import Mathlib.Tactic.FinCases
/-!
# Rudvalis part-4 batch 17

Certify the forty forward transitions in batch 17. Algebraic checks use
`OrderLevel0Part4Algebraic`; residual checks expand compressed factors and
verify their action on all 4060 points through certified lookup tables.
Source: the fixed ATLAS witnesses documented in `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
set_option maxRecDepth 30000
set_option Elab.async false

private def point17_0_0Word : List (Fin 71) := [2, 4, 11, 58, 50, 38, 49, 10, 69]
private theorem point17_0_0Expanded :
    point17_0_0Word.flatMap Part4Group1Fast.word = L0Factor 0 2460 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_0_0Check : Part4Group1Fast.check 0 2460 point17_0_0Word = true := by
  decide +kernel
private theorem point17_0_0 : stepCheck 0 2460 :=
  Part4Group1Fast.ofCheck 0 2460 point17_0_0Word point17_0_0Expanded point17_0_0Check

private theorem point17_0_1 : stepCheck 0 2461 := Or.inl algebraic17_0_1

private theorem point17_0_2 : stepCheck 0 2462 := Or.inl algebraic17_0_2

private theorem point17_0_3 : stepCheck 0 2463 := Or.inl algebraic17_0_3

private theorem point17_0_4 : stepCheck 0 2464 := Or.inl algebraic17_0_4

private theorem point17_0_5 : stepCheck 0 2465 := Or.inl algebraic17_0_5

private theorem point17_0_6 : stepCheck 0 2466 := Or.inl algebraic17_0_6

private theorem point17_0_7 : stepCheck 0 2467 := Or.inl algebraic17_0_7

private def point17_0_8Word : List (Fin 71) := [51, 5, 6, 54, 32, 58, 43, 60]
private theorem point17_0_8Expanded :
    point17_0_8Word.flatMap Part4Group1Fast.word = L0Factor 0 2468 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_0_8Check : Part4Group1Fast.check 0 2468 point17_0_8Word = true := by
  decide +kernel
private theorem point17_0_8 : stepCheck 0 2468 :=
  Part4Group1Fast.ofCheck 0 2468 point17_0_8Word point17_0_8Expanded point17_0_8Check

private theorem point17_0_9 : stepCheck 0 2469 := Or.inl algebraic17_0_9

private def point17_0_10Word : List (Fin 71) := [2, 16, 4, 11, 12, 40, 37, 54, 5, 41, 3]
private theorem point17_0_10Expanded :
    point17_0_10Word.flatMap Part4Group1Fast.word = L0Factor 0 2470 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_0_10Check : Part4Group1Fast.check 0 2470 point17_0_10Word = true := by
  decide +kernel
private theorem point17_0_10 : stepCheck 0 2470 :=
  Part4Group1Fast.ofCheck 0 2470 point17_0_10Word point17_0_10Expanded point17_0_10Check

private def point17_0_11Word : List (Fin 71) := [64, 5, 6, 2, 4, 18, 34, 66, 35, 69]
private theorem point17_0_11Expanded :
    point17_0_11Word.flatMap Part4Group1Fast.word = L0Factor 0 2471 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_0_11Check : Part4Group1Fast.check 0 2471 point17_0_11Word = true := by
  decide +kernel
private theorem point17_0_11 : stepCheck 0 2471 :=
  Part4Group1Fast.ofCheck 0 2471 point17_0_11Word point17_0_11Expanded point17_0_11Check

private theorem point17_0_12 : stepCheck 0 2472 := Or.inl algebraic17_0_12

private theorem point17_0_13 : stepCheck 0 2473 := Or.inl algebraic17_0_13

private def point17_0_14Word : List (Fin 71) := [51, 8, 42, 10, 66, 55]
private theorem point17_0_14Expanded :
    point17_0_14Word.flatMap Part4Group1Fast.word = L0Factor 0 2474 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_0_14Check : Part4Group1Fast.check 0 2474 point17_0_14Word = true := by
  decide +kernel
private theorem point17_0_14 : stepCheck 0 2474 :=
  Part4Group1Fast.ofCheck 0 2474 point17_0_14Word point17_0_14Expanded point17_0_14Check

private def point17_0_15Word : List (Fin 71) := [2, 16, 25, 3, 9, 26, 51, 31, 67, 60]
private theorem point17_0_15Expanded :
    point17_0_15Word.flatMap Part4Group1Fast.word = L0Factor 0 2475 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_0_15Check : Part4Group1Fast.check 0 2475 point17_0_15Word = true := by
  decide +kernel
private theorem point17_0_15 : stepCheck 0 2475 :=
  Part4Group1Fast.ofCheck 0 2475 point17_0_15Word point17_0_15Expanded point17_0_15Check

private theorem point17_0_16 : stepCheck 0 2476 := Or.inl algebraic17_0_16

private theorem point17_0_17 : stepCheck 0 2477 := Or.inl algebraic17_0_17

private theorem point17_0_18 : stepCheck 0 2478 := Or.inl algebraic17_0_18

private theorem point17_0_19 : stepCheck 0 2479 := Or.inl algebraic17_0_19

private theorem point17_1_0 : stepCheck 1 2460 := Or.inl algebraic17_1_0

private theorem point17_1_1 : stepCheck 1 2461 := Or.inl algebraic17_1_1

private theorem point17_1_2 : stepCheck 1 2462 := Or.inl algebraic17_1_2

private theorem point17_1_3 : stepCheck 1 2463 := Or.inl algebraic17_1_3

private theorem point17_1_4 : stepCheck 1 2464 := Or.inl algebraic17_1_4

private def point17_1_5Word : List (Fin 71) := [1, 44, 25, 65, 38, 45, 17, 55]
private theorem point17_1_5Expanded :
    point17_1_5Word.flatMap Part4Group1Fast.word = L0Factor 1 2465 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_1_5Check : Part4Group1Fast.check 1 2465 point17_1_5Word = true := by
  decide +kernel
private theorem point17_1_5 : stepCheck 1 2465 :=
  Part4Group1Fast.ofCheck 1 2465 point17_1_5Word point17_1_5Expanded point17_1_5Check

private theorem point17_1_6 : stepCheck 1 2466 := Or.inl algebraic17_1_6

private def point17_1_7Word : List (Fin 71) := [51, 25, 1, 37, 31, 43, 60]
private theorem point17_1_7Expanded :
    point17_1_7Word.flatMap Part4Group1Fast.word = L0Factor 1 2467 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_1_7Check : Part4Group1Fast.check 1 2467 point17_1_7Word = true := by
  decide +kernel
private theorem point17_1_7 : stepCheck 1 2467 :=
  Part4Group1Fast.ofCheck 1 2467 point17_1_7Word point17_1_7Expanded point17_1_7Check

private def point17_1_8Word : List (Fin 71) := [2, 6, 25, 14, 47, 24, 57, 60]
private theorem point17_1_8Expanded :
    point17_1_8Word.flatMap Part4Group1Fast.word = L0Factor 1 2468 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_1_8Check : Part4Group1Fast.check 1 2468 point17_1_8Word = true := by
  decide +kernel
private theorem point17_1_8 : stepCheck 1 2468 :=
  Part4Group1Fast.ofCheck 1 2468 point17_1_8Word point17_1_8Expanded point17_1_8Check

private def point17_1_9Word : List (Fin 71) := [2, 9, 16, 34, 10, 41, 22, 30, 10, 3]
private theorem point17_1_9Expanded :
    point17_1_9Word.flatMap Part4Group1Fast.word = L0Factor 1 2469 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_1_9Check : Part4Group1Fast.check 1 2469 point17_1_9Word = true := by
  decide +kernel
private theorem point17_1_9 : stepCheck 1 2469 :=
  Part4Group1Fast.ofCheck 1 2469 point17_1_9Word point17_1_9Expanded point17_1_9Check

private def point17_1_10Word : List (Fin 71) := [10, 56, 65, 41, 57, 60]
private theorem point17_1_10Expanded :
    point17_1_10Word.flatMap Part4Group1Fast.word = L0Factor 1 2470 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_1_10Check : Part4Group1Fast.check 1 2470 point17_1_10Word = true := by
  decide +kernel
private theorem point17_1_10 : stepCheck 1 2470 :=
  Part4Group1Fast.ofCheck 1 2470 point17_1_10Word point17_1_10Expanded point17_1_10Check

private theorem point17_1_11 : stepCheck 1 2471 := Or.inl algebraic17_1_11

private theorem point17_1_12 : stepCheck 1 2472 := Or.inl algebraic17_1_12

private theorem point17_1_13 : stepCheck 1 2473 := Or.inl algebraic17_1_13

private def point17_1_14Word : List (Fin 71) := [13, 9, 54, 5, 38, 58, 70]
private theorem point17_1_14Expanded :
    point17_1_14Word.flatMap Part4Group1Fast.word = L0Factor 1 2474 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_1_14Check : Part4Group1Fast.check 1 2474 point17_1_14Word = true := by
  decide +kernel
private theorem point17_1_14 : stepCheck 1 2474 :=
  Part4Group1Fast.ofCheck 1 2474 point17_1_14Word point17_1_14Expanded point17_1_14Check

private theorem point17_1_15 : stepCheck 1 2475 := Or.inl algebraic17_1_15

private theorem point17_1_16 : stepCheck 1 2476 := Or.inl algebraic17_1_16

private theorem point17_1_17 : stepCheck 1 2477 := Or.inl algebraic17_1_17

private theorem point17_1_18 : stepCheck 1 2478 := Or.inl algebraic17_1_18

private def point17_1_19Word : List (Fin 71) := [51, 1, 4, 58, 2, 4, 18, 40, 24, 55]
private theorem point17_1_19Expanded :
    point17_1_19Word.flatMap Part4Group1Fast.word = L0Factor 1 2479 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point17_1_19Check : Part4Group1Fast.check 1 2479 point17_1_19Word = true := by
  decide +kernel
private theorem point17_1_19 : stepCheck 1 2479 :=
  Part4Group1Fast.ofCheck 1 2479 point17_1_19Word point17_1_19Expanded point17_1_19Check

public theorem group1Batch17 : stepBatch 123 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point17_0_0
  · exact point17_0_1
  · exact point17_0_2
  · exact point17_0_3
  · exact point17_0_4
  · exact point17_0_5
  · exact point17_0_6
  · exact point17_0_7
  · exact point17_0_8
  · exact point17_0_9
  · exact point17_0_10
  · exact point17_0_11
  · exact point17_0_12
  · exact point17_0_13
  · exact point17_0_14
  · exact point17_0_15
  · exact point17_0_16
  · exact point17_0_17
  · exact point17_0_18
  · exact point17_0_19
  · exact point17_1_0
  · exact point17_1_1
  · exact point17_1_2
  · exact point17_1_3
  · exact point17_1_4
  · exact point17_1_5
  · exact point17_1_6
  · exact point17_1_7
  · exact point17_1_8
  · exact point17_1_9
  · exact point17_1_10
  · exact point17_1_11
  · exact point17_1_12
  · exact point17_1_13
  · exact point17_1_14
  · exact point17_1_15
  · exact point17_1_16
  · exact point17_1_17
  · exact point17_1_18
  · exact point17_1_19


end Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
