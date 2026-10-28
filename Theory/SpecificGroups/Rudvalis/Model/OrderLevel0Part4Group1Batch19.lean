module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Fast
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Algebraic
import Mathlib.Tactic.FinCases
/-!
# Rudvalis part-4 batch 19

Certify the forty forward transitions in batch 19. Algebraic checks use
`OrderLevel0Part4Algebraic`; residual checks expand compressed factors and
verify their action on all 4060 points through certified lookup tables.
Source: the fixed ATLAS witnesses documented in `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
set_option maxRecDepth 30000
set_option Elab.async false

private def point19_0_0Word : List (Fin 71) := [8, 6, 50, 10, 42, 3]
private theorem point19_0_0Expanded :
    point19_0_0Word.flatMap Part4Group1Fast.word = L0Factor 0 2740 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point19_0_0Check : Part4Group1Fast.check 0 2740 point19_0_0Word = true := by
  decide +kernel
private theorem point19_0_0 : stepCheck 0 2740 :=
  Part4Group1Fast.ofCheck 0 2740 point19_0_0Word point19_0_0Expanded point19_0_0Check

private theorem point19_0_1 : stepCheck 0 2741 := Or.inl algebraic19_0_1

private theorem point19_0_2 : stepCheck 0 2742 := Or.inl algebraic19_0_2

private theorem point19_0_3 : stepCheck 0 2743 := Or.inl algebraic19_0_3

private theorem point19_0_4 : stepCheck 0 2744 := Or.inl algebraic19_0_4

private theorem point19_0_5 : stepCheck 0 2745 := Or.inl algebraic19_0_5

private theorem point19_0_6 : stepCheck 0 2746 := Or.inl algebraic19_0_6

private theorem point19_0_7 : stepCheck 0 2747 := Or.inl algebraic19_0_7

private theorem point19_0_8 : stepCheck 0 2748 := Or.inl algebraic19_0_8

private theorem point19_0_9 : stepCheck 0 2749 := Or.inl algebraic19_0_9

private theorem point19_0_10 : stepCheck 0 2750 := Or.inl algebraic19_0_10

private theorem point19_0_11 : stepCheck 0 2751 := Or.inl algebraic19_0_11

private theorem point19_0_12 : stepCheck 0 2752 := Or.inl algebraic19_0_12

private theorem point19_0_13 : stepCheck 0 2753 := Or.inl algebraic19_0_13

private theorem point19_0_14 : stepCheck 0 2754 := Or.inl algebraic19_0_14

private theorem point19_0_15 : stepCheck 0 2755 := Or.inl algebraic19_0_15

private theorem point19_0_16 : stepCheck 0 2756 := Or.inl algebraic19_0_16

private def point19_0_17Word : List (Fin 71) := [7, 7, 8, 7, 17, 31, 41, 57]
private theorem point19_0_17Expanded :
    point19_0_17Word.flatMap Part4Group1Fast.word = L0Factor 0 2757 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point19_0_17Check : Part4Group1Fast.check 0 2757 point19_0_17Word = true := by
  decide +kernel
private theorem point19_0_17 : stepCheck 0 2757 :=
  Part4Group1Fast.ofCheck 0 2757 point19_0_17Word point19_0_17Expanded point19_0_17Check

private theorem point19_0_18 : stepCheck 0 2758 := Or.inl algebraic19_0_18

private theorem point19_0_19 : stepCheck 0 2759 := Or.inl algebraic19_0_19

private theorem point19_1_0 : stepCheck 1 2740 := Or.inl algebraic19_1_0

private theorem point19_1_1 : stepCheck 1 2741 := Or.inl algebraic19_1_1

private theorem point19_1_2 : stepCheck 1 2742 := Or.inl algebraic19_1_2

private def point19_1_3Word : List (Fin 71) := [50, 46, 31, 66, 36, 39]
private theorem point19_1_3Expanded :
    point19_1_3Word.flatMap Part4Group1Fast.word = L0Factor 1 2743 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point19_1_3Check : Part4Group1Fast.check 1 2743 point19_1_3Word = true := by
  decide +kernel
private theorem point19_1_3 : stepCheck 1 2743 :=
  Part4Group1Fast.ofCheck 1 2743 point19_1_3Word point19_1_3Expanded point19_1_3Check

private theorem point19_1_4 : stepCheck 1 2744 := Or.inl algebraic19_1_4

private theorem point19_1_5 : stepCheck 1 2745 := Or.inl algebraic19_1_5

private theorem point19_1_6 : stepCheck 1 2746 := Or.inl algebraic19_1_6

private def point19_1_7Word : List (Fin 71) := []
private theorem point19_1_7Expanded :
    point19_1_7Word.flatMap Part4Group1Fast.word = L0Factor 1 2747 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point19_1_7Check : Part4Group1Fast.check 1 2747 point19_1_7Word = true := by
  decide +kernel
private theorem point19_1_7 : stepCheck 1 2747 :=
  Part4Group1Fast.ofCheck 1 2747 point19_1_7Word point19_1_7Expanded point19_1_7Check

private def point19_1_8Word : List (Fin 71) := [1, 8, 4, 20, 1, 58, 50, 30, 10, 3]
private theorem point19_1_8Expanded :
    point19_1_8Word.flatMap Part4Group1Fast.word = L0Factor 1 2748 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point19_1_8Check : Part4Group1Fast.check 1 2748 point19_1_8Word = true := by
  decide +kernel
private theorem point19_1_8 : stepCheck 1 2748 :=
  Part4Group1Fast.ofCheck 1 2748 point19_1_8Word point19_1_8Expanded point19_1_8Check

private def point19_1_9Word : List (Fin 71) := [50, 1, 37, 42, 50, 52]
private theorem point19_1_9Expanded :
    point19_1_9Word.flatMap Part4Group1Fast.word = L0Factor 1 2749 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point19_1_9Check : Part4Group1Fast.check 1 2749 point19_1_9Word = true := by
  decide +kernel
private theorem point19_1_9 : stepCheck 1 2749 :=
  Part4Group1Fast.ofCheck 1 2749 point19_1_9Word point19_1_9Expanded point19_1_9Check

private def point19_1_10Word : List (Fin 71) := []
private theorem point19_1_10Expanded :
    point19_1_10Word.flatMap Part4Group1Fast.word = L0Factor 1 2750 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point19_1_10Check : Part4Group1Fast.check 1 2750 point19_1_10Word = true := by
  decide +kernel
private theorem point19_1_10 : stepCheck 1 2750 :=
  Part4Group1Fast.ofCheck 1 2750 point19_1_10Word point19_1_10Expanded point19_1_10Check

private theorem point19_1_11 : stepCheck 1 2751 := Or.inl algebraic19_1_11

private theorem point19_1_12 : stepCheck 1 2752 := Or.inl algebraic19_1_12

private theorem point19_1_13 : stepCheck 1 2753 := Or.inl algebraic19_1_13

private def point19_1_14Word : List (Fin 71) := []
private theorem point19_1_14Expanded :
    point19_1_14Word.flatMap Part4Group1Fast.word = L0Factor 1 2754 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point19_1_14Check : Part4Group1Fast.check 1 2754 point19_1_14Word = true := by
  decide +kernel
private theorem point19_1_14 : stepCheck 1 2754 :=
  Part4Group1Fast.ofCheck 1 2754 point19_1_14Word point19_1_14Expanded point19_1_14Check

private theorem point19_1_15 : stepCheck 1 2755 := Or.inl algebraic19_1_15

private def point19_1_16Word : List (Fin 71) := [0, 0, 16, 8, 44, 38, 14, 34, 31, 59, 2, 62]
private theorem point19_1_16Expanded :
    point19_1_16Word.flatMap Part4Group1Fast.word = L0Factor 1 2756 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point19_1_16Check : Part4Group1Fast.check 1 2756 point19_1_16Word = true := by
  decide +kernel
private theorem point19_1_16 : stepCheck 1 2756 :=
  Part4Group1Fast.ofCheck 1 2756 point19_1_16Word point19_1_16Expanded point19_1_16Check

private def point19_1_17Word : List (Fin 71) := [6, 5, 1, 37, 54, 5, 10, 41, 42, 67]
private theorem point19_1_17Expanded :
    point19_1_17Word.flatMap Part4Group1Fast.word = L0Factor 1 2757 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point19_1_17Check : Part4Group1Fast.check 1 2757 point19_1_17Word = true := by
  decide +kernel
private theorem point19_1_17 : stepCheck 1 2757 :=
  Part4Group1Fast.ofCheck 1 2757 point19_1_17Word point19_1_17Expanded point19_1_17Check

private theorem point19_1_18 : stepCheck 1 2758 := Or.inl algebraic19_1_18

private theorem point19_1_19 : stepCheck 1 2759 := Or.inl algebraic19_1_19

public theorem group1Batch19 : stepBatch 137 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point19_0_0
  · exact point19_0_1
  · exact point19_0_2
  · exact point19_0_3
  · exact point19_0_4
  · exact point19_0_5
  · exact point19_0_6
  · exact point19_0_7
  · exact point19_0_8
  · exact point19_0_9
  · exact point19_0_10
  · exact point19_0_11
  · exact point19_0_12
  · exact point19_0_13
  · exact point19_0_14
  · exact point19_0_15
  · exact point19_0_16
  · exact point19_0_17
  · exact point19_0_18
  · exact point19_0_19
  · exact point19_1_0
  · exact point19_1_1
  · exact point19_1_2
  · exact point19_1_3
  · exact point19_1_4
  · exact point19_1_5
  · exact point19_1_6
  · exact point19_1_7
  · exact point19_1_8
  · exact point19_1_9
  · exact point19_1_10
  · exact point19_1_11
  · exact point19_1_12
  · exact point19_1_13
  · exact point19_1_14
  · exact point19_1_15
  · exact point19_1_16
  · exact point19_1_17
  · exact point19_1_18
  · exact point19_1_19


end Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
