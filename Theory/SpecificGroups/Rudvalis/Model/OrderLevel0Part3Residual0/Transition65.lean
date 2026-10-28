module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual0.Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 65

Certify generator 0 at representative 2027 on all 4060 points, using 29
kernel-checked slices and the packed evaluator's correctness theorem.
Source: `OrderLevel0Data` and `Part3Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem slice0 : Residual0Nat.slice 0 2027 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1 : Residual0Nat.slice 0 2027 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice2 : Residual0Nat.slice 0 2027 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice3 : Residual0Nat.slice 0 2027 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice4 : Residual0Nat.slice 0 2027 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice5 : Residual0Nat.slice 0 2027 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice6 : Residual0Nat.slice 0 2027 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice7 : Residual0Nat.slice 0 2027 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice8 : Residual0Nat.slice 0 2027 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice9 : Residual0Nat.slice 0 2027 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice10 : Residual0Nat.slice 0 2027 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice11 : Residual0Nat.slice 0 2027 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice12 : Residual0Nat.slice 0 2027 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice13 : Residual0Nat.slice 0 2027 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice14 : Residual0Nat.slice 0 2027 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice15 : Residual0Nat.slice 0 2027 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice16 : Residual0Nat.slice 0 2027 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice17 : Residual0Nat.slice 0 2027 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice18 : Residual0Nat.slice 0 2027 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice19 : Residual0Nat.slice 0 2027 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice20 : Residual0Nat.slice 0 2027 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice21 : Residual0Nat.slice 0 2027 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice22 : Residual0Nat.slice 0 2027 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice23 : Residual0Nat.slice 0 2027 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice24 : Residual0Nat.slice 0 2027 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice25 : Residual0Nat.slice 0 2027 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice26 : Residual0Nat.slice 0 2027 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice27 : Residual0Nat.slice 0 2027 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice28 : Residual0Nat.slice 0 2027 28 = true := by
  decide +kernel

/-- The prescribed transition at residual index 65. -/
public theorem point65 : stepCheck 0 2027 := by
  apply Residual0Nat.ofSlices
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
