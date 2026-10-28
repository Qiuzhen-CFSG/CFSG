module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Fast
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Algebraic
import Mathlib.Tactic.FinCases
/-!
# Rudvalis part-4 batch 15

Certify the forty forward transitions in batch 15. Algebraic checks use
`OrderLevel0Part4Algebraic`; residual checks expand compressed factors and
verify their action on all 4060 points through certified lookup tables.
Source: the fixed ATLAS witnesses documented in `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
set_option maxRecDepth 30000
set_option Elab.async false

private theorem point15_0_0 : stepCheck 0 2180 := Or.inl algebraic15_0_0

private def point15_0_1Word : List (Fin 71) := [64, 61, 37, 42, 68, 38]
private theorem point15_0_1Expanded :
    point15_0_1Word.flatMap Part4Group1Fast.word = L0Factor 0 2181 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_0_1Check : Part4Group1Fast.check 0 2181 point15_0_1Word = true := by
  decide +kernel
private theorem point15_0_1 : stepCheck 0 2181 :=
  Part4Group1Fast.ofCheck 0 2181 point15_0_1Word point15_0_1Expanded point15_0_1Check

private def point15_0_2Word : List (Fin 71) := [0, 11, 11, 58, 22, 55]
private theorem point15_0_2Expanded :
    point15_0_2Word.flatMap Part4Group1Fast.word = L0Factor 0 2182 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_0_2Check : Part4Group1Fast.check 0 2182 point15_0_2Word = true := by
  decide +kernel
private theorem point15_0_2 : stepCheck 0 2182 :=
  Part4Group1Fast.ofCheck 0 2182 point15_0_2Word point15_0_2Expanded point15_0_2Check

private theorem point15_0_3 : stepCheck 0 2183 := Or.inl algebraic15_0_3

private def point15_0_4Word : List (Fin 71) := [0, 6, 3, 12, 56, 65, 57]
private theorem point15_0_4Expanded :
    point15_0_4Word.flatMap Part4Group1Fast.word = L0Factor 0 2184 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_0_4Check : Part4Group1Fast.check 0 2184 point15_0_4Word = true := by
  decide +kernel
private theorem point15_0_4 : stepCheck 0 2184 :=
  Part4Group1Fast.ofCheck 0 2184 point15_0_4Word point15_0_4Expanded point15_0_4Check

private theorem point15_0_5 : stepCheck 0 2185 := Or.inl algebraic15_0_5

private theorem point15_0_6 : stepCheck 0 2186 := Or.inl algebraic15_0_6

private theorem point15_0_7 : stepCheck 0 2187 := Or.inl algebraic15_0_7

private theorem point15_0_8 : stepCheck 0 2188 := Or.inl algebraic15_0_8

private theorem point15_0_9 : stepCheck 0 2189 := Or.inl algebraic15_0_9

private theorem point15_0_10 : stepCheck 0 2190 := Or.inl algebraic15_0_10

private theorem point15_0_11 : stepCheck 0 2191 := Or.inl algebraic15_0_11

private theorem point15_0_12 : stepCheck 0 2192 := Or.inl algebraic15_0_12

private theorem point15_0_13 : stepCheck 0 2193 := Or.inl algebraic15_0_13

private def point15_0_14Word : List (Fin 71) := [0, 1, 8, 4, 20, 37, 50, 42, 59, 2, 62]
private theorem point15_0_14Expanded :
    point15_0_14Word.flatMap Part4Group1Fast.word = L0Factor 0 2194 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_0_14Check : Part4Group1Fast.check 0 2194 point15_0_14Word = true := by
  decide +kernel
private theorem point15_0_14 : stepCheck 0 2194 :=
  Part4Group1Fast.ofCheck 0 2194 point15_0_14Word point15_0_14Expanded point15_0_14Check

private theorem point15_0_15 : stepCheck 0 2195 := Or.inl algebraic15_0_15

private def point15_0_16Word : List (Fin 71) := [0, 0, 1, 44, 17, 31, 22, 57]
private theorem point15_0_16Expanded :
    point15_0_16Word.flatMap Part4Group1Fast.word = L0Factor 0 2196 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_0_16Check : Part4Group1Fast.check 0 2196 point15_0_16Word = true := by
  decide +kernel
private theorem point15_0_16 : stepCheck 0 2196 :=
  Part4Group1Fast.ofCheck 0 2196 point15_0_16Word point15_0_16Expanded point15_0_16Check

private theorem point15_0_17 : stepCheck 0 2197 := Or.inl algebraic15_0_17

private theorem point15_0_18 : stepCheck 0 2198 := Or.inl algebraic15_0_18

private theorem point15_0_19 : stepCheck 0 2199 := Or.inl algebraic15_0_19

private theorem point15_1_0 : stepCheck 1 2180 := Or.inl algebraic15_1_0

private theorem point15_1_1 : stepCheck 1 2181 := Or.inl algebraic15_1_1

private theorem point15_1_2 : stepCheck 1 2182 := Or.inl algebraic15_1_2

private def point15_1_3Word : List (Fin 71) := [6, 3, 12, 56, 65, 57]
private theorem point15_1_3Expanded :
    point15_1_3Word.flatMap Part4Group1Fast.word = L0Factor 1 2183 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_1_3Check : Part4Group1Fast.check 1 2183 point15_1_3Word = true := by
  decide +kernel
private theorem point15_1_3 : stepCheck 1 2183 :=
  Part4Group1Fast.ofCheck 1 2183 point15_1_3Word point15_1_3Expanded point15_1_3Check

private theorem point15_1_4 : stepCheck 1 2184 := Or.inl algebraic15_1_4

private def point15_1_5Word : List (Fin 71) := [7, 63, 7, 14, 8, 64, 22, 31, 69]
private theorem point15_1_5Expanded :
    point15_1_5Word.flatMap Part4Group1Fast.word = L0Factor 1 2185 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_1_5Check : Part4Group1Fast.check 1 2185 point15_1_5Word = true := by
  decide +kernel
private theorem point15_1_5 : stepCheck 1 2185 :=
  Part4Group1Fast.ofCheck 1 2185 point15_1_5Word point15_1_5Expanded point15_1_5Check

private def point15_1_6Word : List (Fin 71) := [2, 6, 4, 6, 2, 9, 26, 18, 56, 8, 64, 55]
private theorem point15_1_6Expanded :
    point15_1_6Word.flatMap Part4Group1Fast.word = L0Factor 1 2186 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_1_6Check : Part4Group1Fast.check 1 2186 point15_1_6Word = true := by
  decide +kernel
private theorem point15_1_6 : stepCheck 1 2186 :=
  Part4Group1Fast.ofCheck 1 2186 point15_1_6Word point15_1_6Expanded point15_1_6Check

private def point15_1_7Word : List (Fin 71) := [12, 1, 1, 14, 14, 58, 54, 5, 57]
private theorem point15_1_7Expanded :
    point15_1_7Word.flatMap Part4Group1Fast.word = L0Factor 1 2187 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_1_7Check : Part4Group1Fast.check 1 2187 point15_1_7Word = true := by
  decide +kernel
private theorem point15_1_7 : stepCheck 1 2187 :=
  Part4Group1Fast.ofCheck 1 2187 point15_1_7Word point15_1_7Expanded point15_1_7Check

private theorem point15_1_8 : stepCheck 1 2188 := Or.inl algebraic15_1_8

private theorem point15_1_9 : stepCheck 1 2189 := Or.inl algebraic15_1_9

private theorem point15_1_10 : stepCheck 1 2190 := Or.inl algebraic15_1_10

private theorem point15_1_11 : stepCheck 1 2191 := Or.inl algebraic15_1_11

private theorem point15_1_12 : stepCheck 1 2192 := Or.inl algebraic15_1_12

private theorem point15_1_13 : stepCheck 1 2193 := Or.inl algebraic15_1_13

private theorem point15_1_14 : stepCheck 1 2194 := Or.inl algebraic15_1_14

private def point15_1_15Word : List (Fin 71) := [5, 34, 56, 34, 42, 66, 55]
private theorem point15_1_15Expanded :
    point15_1_15Word.flatMap Part4Group1Fast.word = L0Factor 1 2195 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_1_15Check : Part4Group1Fast.check 1 2195 point15_1_15Word = true := by
  decide +kernel
private theorem point15_1_15 : stepCheck 1 2195 :=
  Part4Group1Fast.ofCheck 1 2195 point15_1_15Word point15_1_15Expanded point15_1_15Check

private theorem point15_1_16 : stepCheck 1 2196 := Or.inl algebraic15_1_16

private def point15_1_17Word : List (Fin 71) := [1, 23, 0, 11, 12, 56, 23, 51, 66, 36]
private theorem point15_1_17Expanded :
    point15_1_17Word.flatMap Part4Group1Fast.word = L0Factor 1 2197 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_1_17Check : Part4Group1Fast.check 1 2197 point15_1_17Word = true := by
  decide +kernel
private theorem point15_1_17 : stepCheck 1 2197 :=
  Part4Group1Fast.ofCheck 1 2197 point15_1_17Word point15_1_17Expanded point15_1_17Check

private theorem point15_1_18 : stepCheck 1 2198 := Or.inl algebraic15_1_18

private theorem point15_1_19 : stepCheck 1 2199 := Or.inl algebraic15_1_19

public theorem group1Batch15 : stepBatch 109 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point15_0_0
  · exact point15_0_1
  · exact point15_0_2
  · exact point15_0_3
  · exact point15_0_4
  · exact point15_0_5
  · exact point15_0_6
  · exact point15_0_7
  · exact point15_0_8
  · exact point15_0_9
  · exact point15_0_10
  · exact point15_0_11
  · exact point15_0_12
  · exact point15_0_13
  · exact point15_0_14
  · exact point15_0_15
  · exact point15_0_16
  · exact point15_0_17
  · exact point15_0_18
  · exact point15_0_19
  · exact point15_1_0
  · exact point15_1_1
  · exact point15_1_2
  · exact point15_1_3
  · exact point15_1_4
  · exact point15_1_5
  · exact point15_1_6
  · exact point15_1_7
  · exact point15_1_8
  · exact point15_1_9
  · exact point15_1_10
  · exact point15_1_11
  · exact point15_1_12
  · exact point15_1_13
  · exact point15_1_14
  · exact point15_1_15
  · exact point15_1_16
  · exact point15_1_17
  · exact point15_1_18
  · exact point15_1_19


end Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
