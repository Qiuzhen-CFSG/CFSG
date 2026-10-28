module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Fast
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Algebraic
import Mathlib.Tactic.FinCases
/-!
# Rudvalis part-4 batch 20

Certify the forty forward transitions in batch 20. Algebraic checks use
`OrderLevel0Part4Algebraic`; residual checks expand compressed factors and
verify their action on all 4060 points through certified lookup tables.
Source: the fixed ATLAS witnesses documented in `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
set_option maxRecDepth 30000
set_option Elab.async false

private theorem point20_0_0 : stepCheck 0 2880 := Or.inl algebraic20_0_0

private def point20_0_1Word : List (Fin 71) := [54, 1, 44, 38, 47, 1, 34, 57, 60]
private theorem point20_0_1Expanded :
    point20_0_1Word.flatMap Part4Group1Fast.word = L0Factor 0 2881 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point20_0_1Check : Part4Group1Fast.check 0 2881 point20_0_1Word = true := by
  decide +kernel
private theorem point20_0_1 : stepCheck 0 2881 :=
  Part4Group1Fast.ofCheck 0 2881 point20_0_1Word point20_0_1Expanded point20_0_1Check

private theorem point20_0_2 : stepCheck 0 2882 := Or.inl algebraic20_0_2

private theorem point20_0_3 : stepCheck 0 2883 := Or.inl algebraic20_0_3

private def point20_0_4Word : List (Fin 71) := [0, 11, 6, 14, 23, 32, 56]
private theorem point20_0_4Expanded :
    point20_0_4Word.flatMap Part4Group1Fast.word = L0Factor 0 2884 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point20_0_4Check : Part4Group1Fast.check 0 2884 point20_0_4Word = true := by
  decide +kernel
private theorem point20_0_4 : stepCheck 0 2884 :=
  Part4Group1Fast.ofCheck 0 2884 point20_0_4Word point20_0_4Expanded point20_0_4Check

private theorem point20_0_5 : stepCheck 0 2885 := Or.inl algebraic20_0_5

private theorem point20_0_6 : stepCheck 0 2886 := Or.inl algebraic20_0_6

private theorem point20_0_7 : stepCheck 0 2887 := Or.inl algebraic20_0_7

private theorem point20_0_8 : stepCheck 0 2888 := Or.inl algebraic20_0_8

private theorem point20_0_9 : stepCheck 0 2889 := Or.inl algebraic20_0_9

private theorem point20_0_10 : stepCheck 0 2890 := Or.inl algebraic20_0_10

private theorem point20_0_11 : stepCheck 0 2891 := Or.inl algebraic20_0_11

private def point20_0_12Word : List (Fin 71) := []
private theorem point20_0_12Expanded :
    point20_0_12Word.flatMap Part4Group1Fast.word = L0Factor 0 2892 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point20_0_12Check : Part4Group1Fast.check 0 2892 point20_0_12Word = true := by
  decide +kernel
private theorem point20_0_12 : stepCheck 0 2892 :=
  Part4Group1Fast.ofCheck 0 2892 point20_0_12Word point20_0_12Expanded point20_0_12Check

private theorem point20_0_13 : stepCheck 0 2893 := Or.inl algebraic20_0_13

private theorem point20_0_14 : stepCheck 0 2894 := Or.inl algebraic20_0_14

private theorem point20_0_15 : stepCheck 0 2895 := Or.inl algebraic20_0_15

private theorem point20_0_16 : stepCheck 0 2896 := Or.inl algebraic20_0_16

private theorem point20_0_17 : stepCheck 0 2897 := Or.inl algebraic20_0_17

private theorem point20_0_18 : stepCheck 0 2898 := Or.inl algebraic20_0_18

private theorem point20_0_19 : stepCheck 0 2899 := Or.inl algebraic20_0_19

private def point20_1_0Word : List (Fin 71) := [1, 4, 25, 65, 42, 10, 33]
private theorem point20_1_0Expanded :
    point20_1_0Word.flatMap Part4Group1Fast.word = L0Factor 1 2880 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point20_1_0Check : Part4Group1Fast.check 1 2880 point20_1_0Word = true := by
  decide +kernel
private theorem point20_1_0 : stepCheck 1 2880 :=
  Part4Group1Fast.ofCheck 1 2880 point20_1_0Word point20_1_0Expanded point20_1_0Check

private theorem point20_1_1 : stepCheck 1 2881 := Or.inl algebraic20_1_1

private def point20_1_2Word : List (Fin 71) := [0, 63, 9, 50, 43]
private theorem point20_1_2Expanded :
    point20_1_2Word.flatMap Part4Group1Fast.word = L0Factor 1 2882 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point20_1_2Check : Part4Group1Fast.check 1 2882 point20_1_2Word = true := by
  decide +kernel
private theorem point20_1_2 : stepCheck 1 2882 :=
  Part4Group1Fast.ofCheck 1 2882 point20_1_2Word point20_1_2Expanded point20_1_2Check

private theorem point20_1_3 : stepCheck 1 2883 := Or.inl algebraic20_1_3

private theorem point20_1_4 : stepCheck 1 2884 := Or.inl algebraic20_1_4

private theorem point20_1_5 : stepCheck 1 2885 := Or.inl algebraic20_1_5

private theorem point20_1_6 : stepCheck 1 2886 := Or.inl algebraic20_1_6

private def point20_1_7Word : List (Fin 71) := [7, 61, 8, 21, 40, 37, 43, 53]
private theorem point20_1_7Expanded :
    point20_1_7Word.flatMap Part4Group1Fast.word = L0Factor 1 2887 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point20_1_7Check : Part4Group1Fast.check 1 2887 point20_1_7Word = true := by
  decide +kernel
private theorem point20_1_7 : stepCheck 1 2887 :=
  Part4Group1Fast.ofCheck 1 2887 point20_1_7Word point20_1_7Expanded point20_1_7Check

private def point20_1_8Word : List (Fin 71) := [12, 11, 34, 42, 54, 51, 10, 67, 39]
private theorem point20_1_8Expanded :
    point20_1_8Word.flatMap Part4Group1Fast.word = L0Factor 1 2888 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point20_1_8Check : Part4Group1Fast.check 1 2888 point20_1_8Word = true := by
  decide +kernel
private theorem point20_1_8 : stepCheck 1 2888 :=
  Part4Group1Fast.ofCheck 1 2888 point20_1_8Word point20_1_8Expanded point20_1_8Check

private def point20_1_9Word : List (Fin 71) := [63, 0, 25, 0, 18, 40, 24, 55]
private theorem point20_1_9Expanded :
    point20_1_9Word.flatMap Part4Group1Fast.word = L0Factor 1 2889 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point20_1_9Check : Part4Group1Fast.check 1 2889 point20_1_9Word = true := by
  decide +kernel
private theorem point20_1_9 : stepCheck 1 2889 :=
  Part4Group1Fast.ofCheck 1 2889 point20_1_9Word point20_1_9Expanded point20_1_9Check

private theorem point20_1_10 : stepCheck 1 2890 := Or.inl algebraic20_1_10

private theorem point20_1_11 : stepCheck 1 2891 := Or.inl algebraic20_1_11

private theorem point20_1_12 : stepCheck 1 2892 := Or.inl algebraic20_1_12

private theorem point20_1_13 : stepCheck 1 2893 := Or.inl algebraic20_1_13

private def point20_1_14Word : List (Fin 71) := [0, 6, 7, 5, 17, 10, 68, 42, 43, 60]
private theorem point20_1_14Expanded :
    point20_1_14Word.flatMap Part4Group1Fast.word = L0Factor 1 2894 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point20_1_14Check : Part4Group1Fast.check 1 2894 point20_1_14Word = true := by
  decide +kernel
private theorem point20_1_14 : stepCheck 1 2894 :=
  Part4Group1Fast.ofCheck 1 2894 point20_1_14Word point20_1_14Expanded point20_1_14Check

private theorem point20_1_15 : stepCheck 1 2895 := Or.inl algebraic20_1_15

private theorem point20_1_16 : stepCheck 1 2896 := Or.inl algebraic20_1_16

private theorem point20_1_17 : stepCheck 1 2897 := Or.inl algebraic20_1_17

private theorem point20_1_18 : stepCheck 1 2898 := Or.inl algebraic20_1_18

private theorem point20_1_19 : stepCheck 1 2899 := Or.inl algebraic20_1_19

public theorem group1Batch20 : stepBatch 144 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point20_0_0
  · exact point20_0_1
  · exact point20_0_2
  · exact point20_0_3
  · exact point20_0_4
  · exact point20_0_5
  · exact point20_0_6
  · exact point20_0_7
  · exact point20_0_8
  · exact point20_0_9
  · exact point20_0_10
  · exact point20_0_11
  · exact point20_0_12
  · exact point20_0_13
  · exact point20_0_14
  · exact point20_0_15
  · exact point20_0_16
  · exact point20_0_17
  · exact point20_0_18
  · exact point20_0_19
  · exact point20_1_0
  · exact point20_1_1
  · exact point20_1_2
  · exact point20_1_3
  · exact point20_1_4
  · exact point20_1_5
  · exact point20_1_6
  · exact point20_1_7
  · exact point20_1_8
  · exact point20_1_9
  · exact point20_1_10
  · exact point20_1_11
  · exact point20_1_12
  · exact point20_1_13
  · exact point20_1_14
  · exact point20_1_15
  · exact point20_1_16
  · exact point20_1_17
  · exact point20_1_18
  · exact point20_1_19


end Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
