module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual0.Words
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 64

Certify generator 1 at representative 1896 on all 4060 points, using 29
kernel-checked slices and the packed evaluator's correctness theorem.
Source: `OrderLevel0Data` and `Part3Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

private def sourceWord : List (Fin 4) := [1, 0, 1, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 1]
private def imageWord : List (Fin 4) := [0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
private def factorWord : List (Fin 4) := [2, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]

set_option maxHeartbeats 1600000 in
private theorem slice0 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice2 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice3 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice4 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice5 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice6 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice7 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice8 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice9 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice10 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice11 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice12 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice13 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice14 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice15 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice16 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice17 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice18 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice19 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice20 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice21 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice22 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice23 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice24 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice25 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice26 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice27 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice28 : Residual0Nat.wordSlice 1 sourceWord imageWord factorWord 28 = true := by
  decide +kernel

/-- The prescribed transition at residual index 64. -/
public theorem point64 : stepCheck 1 1896 := by
  apply Residual0Nat.ofWordSlices 1 1896 sourceWord imageWord factorWord
    (by rfl) (by rfl) (by rfl)
  intro b
  fin_cases b
  · exact slice0
  · exact slice1
  · exact slice2
  · exact slice3
  · exact slice4
  · exact slice5
  · exact slice6
  · exact slice7
  · exact slice8
  · exact slice9
  · exact slice10
  · exact slice11
  · exact slice12
  · exact slice13
  · exact slice14
  · exact slice15
  · exact slice16
  · exact slice17
  · exact slice18
  · exact slice19
  · exact slice20
  · exact slice21
  · exact slice22
  · exact slice23
  · exact slice24
  · exact slice25
  · exact slice26
  · exact slice27
  · exact slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual0Checks
