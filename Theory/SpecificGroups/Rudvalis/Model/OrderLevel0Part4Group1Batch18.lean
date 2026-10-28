module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Fast
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Algebraic
import Mathlib.Tactic.FinCases
/-!
# Rudvalis part-4 batch 18

Certify the forty forward transitions in batch 18. Algebraic checks use
`OrderLevel0Part4Algebraic`; residual checks expand compressed factors and
verify their action on all 4060 points through certified lookup tables.
Source: the fixed ATLAS witnesses documented in `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
set_option maxRecDepth 30000
set_option Elab.async false

private def point18_0_0Word : List (Fin 71) := [63, 5, 61, 65, 68, 57, 60]
private theorem point18_0_0Expanded :
    point18_0_0Word.flatMap Part4Group1Fast.word = L0Factor 0 2600 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_0_0Check : Part4Group1Fast.check 0 2600 point18_0_0Word = true := by
  decide +kernel
private theorem point18_0_0 : stepCheck 0 2600 :=
  Part4Group1Fast.ofCheck 0 2600 point18_0_0Word point18_0_0Expanded point18_0_0Check

private def point18_0_1Word : List (Fin 71) := [2]
private theorem point18_0_1Expanded :
    point18_0_1Word.flatMap Part4Group1Fast.word = L0Factor 0 2601 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_0_1Check : Part4Group1Fast.check 0 2601 point18_0_1Word = true := by
  decide +kernel
private theorem point18_0_1 : stepCheck 0 2601 :=
  Part4Group1Fast.ofCheck 0 2601 point18_0_1Word point18_0_1Expanded point18_0_1Check

private theorem point18_0_2 : stepCheck 0 2602 := Or.inl algebraic18_0_2

private theorem point18_0_3 : stepCheck 0 2603 := Or.inl algebraic18_0_3

private theorem point18_0_4 : stepCheck 0 2604 := Or.inl algebraic18_0_4

private theorem point18_0_5 : stepCheck 0 2605 := Or.inl algebraic18_0_5

private theorem point18_0_6 : stepCheck 0 2606 := Or.inl algebraic18_0_6

private theorem point18_0_7 : stepCheck 0 2607 := Or.inl algebraic18_0_7

private theorem point18_0_8 : stepCheck 0 2608 := Or.inl algebraic18_0_8

private theorem point18_0_9 : stepCheck 0 2609 := Or.inl algebraic18_0_9

private def point18_0_10Word : List (Fin 71) := [0, 63, 4, 2, 8, 50, 38, 58, 67]
private theorem point18_0_10Expanded :
    point18_0_10Word.flatMap Part4Group1Fast.word = L0Factor 0 2610 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_0_10Check : Part4Group1Fast.check 0 2610 point18_0_10Word = true := by
  decide +kernel
private theorem point18_0_10 : stepCheck 0 2610 :=
  Part4Group1Fast.ofCheck 0 2610 point18_0_10Word point18_0_10Expanded point18_0_10Check

private theorem point18_0_11 : stepCheck 0 2611 := Or.inl algebraic18_0_11

private theorem point18_0_12 : stepCheck 0 2612 := Or.inl algebraic18_0_12

private theorem point18_0_13 : stepCheck 0 2613 := Or.inl algebraic18_0_13

private theorem point18_0_14 : stepCheck 0 2614 := Or.inl algebraic18_0_14

private theorem point18_0_15 : stepCheck 0 2615 := Or.inl algebraic18_0_15

private def point18_0_16Word : List (Fin 71) := [2]
private theorem point18_0_16Expanded :
    point18_0_16Word.flatMap Part4Group1Fast.word = L0Factor 0 2616 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_0_16Check : Part4Group1Fast.check 0 2616 point18_0_16Word = true := by
  decide +kernel
private theorem point18_0_16 : stepCheck 0 2616 :=
  Part4Group1Fast.ofCheck 0 2616 point18_0_16Word point18_0_16Expanded point18_0_16Check

private theorem point18_0_17 : stepCheck 0 2617 := Or.inl algebraic18_0_17

private theorem point18_0_18 : stepCheck 0 2618 := Or.inl algebraic18_0_18

private theorem point18_0_19 : stepCheck 0 2619 := Or.inl algebraic18_0_19

private theorem point18_1_0 : stepCheck 1 2600 := Or.inl algebraic18_1_0

private theorem point18_1_1 : stepCheck 1 2601 := Or.inl algebraic18_1_1

private def point18_1_2Word : List (Fin 71) := [7, 25, 0, 1, 47, 1, 14, 46, 3]
private theorem point18_1_2Expanded :
    point18_1_2Word.flatMap Part4Group1Fast.word = L0Factor 1 2602 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_1_2Check : Part4Group1Fast.check 1 2602 point18_1_2Word = true := by
  decide +kernel
private theorem point18_1_2 : stepCheck 1 2602 :=
  Part4Group1Fast.ofCheck 1 2602 point18_1_2Word point18_1_2Expanded point18_1_2Check

private theorem point18_1_3 : stepCheck 1 2603 := Or.inl algebraic18_1_3

private def point18_1_4Word : List (Fin 71) := [0, 6, 11, 5, 41, 42, 43, 53]
private theorem point18_1_4Expanded :
    point18_1_4Word.flatMap Part4Group1Fast.word = L0Factor 1 2604 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_1_4Check : Part4Group1Fast.check 1 2604 point18_1_4Word = true := by
  decide +kernel
private theorem point18_1_4 : stepCheck 1 2604 :=
  Part4Group1Fast.ofCheck 1 2604 point18_1_4Word point18_1_4Expanded point18_1_4Check

private theorem point18_1_5 : stepCheck 1 2605 := Or.inl algebraic18_1_5

private def point18_1_6Word : List (Fin 71) := [2, 23, 6, 1, 1, 23, 51, 10, 66, 42, 70]
private theorem point18_1_6Expanded :
    point18_1_6Word.flatMap Part4Group1Fast.word = L0Factor 1 2606 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_1_6Check : Part4Group1Fast.check 1 2606 point18_1_6Word = true := by
  decide +kernel
private theorem point18_1_6 : stepCheck 1 2606 :=
  Part4Group1Fast.ofCheck 1 2606 point18_1_6Word point18_1_6Expanded point18_1_6Check

private theorem point18_1_7 : stepCheck 1 2607 := Or.inl algebraic18_1_7

private theorem point18_1_8 : stepCheck 1 2608 := Or.inl algebraic18_1_8

private def point18_1_9Word : List (Fin 71) := [6, 25, 63, 5, 17, 38, 14, 14, 8, 64, 36, 39]
private theorem point18_1_9Expanded :
    point18_1_9Word.flatMap Part4Group1Fast.word = L0Factor 1 2609 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_1_9Check : Part4Group1Fast.check 1 2609 point18_1_9Word = true := by
  decide +kernel
private theorem point18_1_9 : stepCheck 1 2609 :=
  Part4Group1Fast.ofCheck 1 2609 point18_1_9Word point18_1_9Expanded point18_1_9Check

private theorem point18_1_10 : stepCheck 1 2610 := Or.inl algebraic18_1_10

private theorem point18_1_11 : stepCheck 1 2611 := Or.inl algebraic18_1_11

private def point18_1_12Word : List (Fin 71) := [63, 1, 61, 8, 7, 18, 56, 14, 47, 24, 36, 39]
private theorem point18_1_12Expanded :
    point18_1_12Word.flatMap Part4Group1Fast.word = L0Factor 1 2612 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_1_12Check : Part4Group1Fast.check 1 2612 point18_1_12Word = true := by
  decide +kernel
private theorem point18_1_12 : stepCheck 1 2612 :=
  Part4Group1Fast.ofCheck 1 2612 point18_1_12Word point18_1_12Expanded point18_1_12Check

private theorem point18_1_13 : stepCheck 1 2613 := Or.inl algebraic18_1_13

private theorem point18_1_14 : stepCheck 1 2614 := Or.inl algebraic18_1_14

private theorem point18_1_15 : stepCheck 1 2615 := Or.inl algebraic18_1_15

private theorem point18_1_16 : stepCheck 1 2616 := Or.inl algebraic18_1_16

private def point18_1_17Word : List (Fin 71) := [0, 0, 16, 16, 34, 10, 38, 45, 17, 35, 69]
private theorem point18_1_17Expanded :
    point18_1_17Word.flatMap Part4Group1Fast.word = L0Factor 1 2617 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_1_17Check : Part4Group1Fast.check 1 2617 point18_1_17Word = true := by
  decide +kernel
private theorem point18_1_17 : stepCheck 1 2617 :=
  Part4Group1Fast.ofCheck 1 2617 point18_1_17Word point18_1_17Expanded point18_1_17Check

private theorem point18_1_18 : stepCheck 1 2618 := Or.inl algebraic18_1_18

private def point18_1_19Word : List (Fin 71) := [61, 61, 34, 10, 41, 10, 42, 70]
private theorem point18_1_19Expanded :
    point18_1_19Word.flatMap Part4Group1Fast.word = L0Factor 1 2619 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point18_1_19Check : Part4Group1Fast.check 1 2619 point18_1_19Word = true := by
  decide +kernel
private theorem point18_1_19 : stepCheck 1 2619 :=
  Part4Group1Fast.ofCheck 1 2619 point18_1_19Word point18_1_19Expanded point18_1_19Check

public theorem group1Batch18 : stepBatch 130 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point18_0_0
  · exact point18_0_1
  · exact point18_0_2
  · exact point18_0_3
  · exact point18_0_4
  · exact point18_0_5
  · exact point18_0_6
  · exact point18_0_7
  · exact point18_0_8
  · exact point18_0_9
  · exact point18_0_10
  · exact point18_0_11
  · exact point18_0_12
  · exact point18_0_13
  · exact point18_0_14
  · exact point18_0_15
  · exact point18_0_16
  · exact point18_0_17
  · exact point18_0_18
  · exact point18_0_19
  · exact point18_1_0
  · exact point18_1_1
  · exact point18_1_2
  · exact point18_1_3
  · exact point18_1_4
  · exact point18_1_5
  · exact point18_1_6
  · exact point18_1_7
  · exact point18_1_8
  · exact point18_1_9
  · exact point18_1_10
  · exact point18_1_11
  · exact point18_1_12
  · exact point18_1_13
  · exact point18_1_14
  · exact point18_1_15
  · exact point18_1_16
  · exact point18_1_17
  · exact point18_1_18
  · exact point18_1_19


end Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
