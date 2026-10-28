module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 17, generator 1, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point1_2500 : stepCheck 1 2500 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2501 : stepCheck 1 2501 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2502 : stepCheck 1 2502 := by
  left
  decide +kernel

private def u1_2503 : List (Fin 96) := [12, 46, 24, 51]
private def v1_2503 : List (Fin 96) := [51, 69, 60, 5, 13, 80, 8, 40, 23, 27, 81]
private def lhs1_2503 (x : Nat) : Nat := Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map51 (x))))
private def rhs1_2503 (x : Nat) : Nat := Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map81 (x)))))))))))
private theorem lhs1_2503_eq : lhs1_2503 = Compressed.eval u1_2503 := by rfl
private theorem rhs1_2503_eq : rhs1_2503 = Compressed.eval v1_2503 := by rfl
private def fastSlice1_2503 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2503 ((100 * b.val + x.val) % 4060) =
      rhs1_2503 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2503 (b : Fin 41) :
    Compressed.slice u1_2503 v1_2503 b = fastSlice1_2503 b := by
  simp only [Compressed.slice, fastSlice1_2503, lhs1_2503_eq, rhs1_2503_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2503 : u1_2503.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2503).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2503 : v1_2503.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2503)).map Compressed.up0 ++
      (L0Factor 1 2503).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_0 : fastSlice1_2503 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_1 : fastSlice1_2503 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_2 : fastSlice1_2503 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_3 : fastSlice1_2503 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_4 : fastSlice1_2503 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_5 : fastSlice1_2503 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_6 : fastSlice1_2503 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_7 : fastSlice1_2503 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_8 : fastSlice1_2503 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_9 : fastSlice1_2503 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_10 : fastSlice1_2503 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_11 : fastSlice1_2503 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_12 : fastSlice1_2503 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_13 : fastSlice1_2503 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_14 : fastSlice1_2503 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_15 : fastSlice1_2503 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_16 : fastSlice1_2503 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_17 : fastSlice1_2503 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_18 : fastSlice1_2503 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_19 : fastSlice1_2503 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_20 : fastSlice1_2503 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_21 : fastSlice1_2503 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_22 : fastSlice1_2503 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_23 : fastSlice1_2503 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_24 : fastSlice1_2503 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_25 : fastSlice1_2503 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_26 : fastSlice1_2503 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_27 : fastSlice1_2503 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_28 : fastSlice1_2503 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_29 : fastSlice1_2503 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_30 : fastSlice1_2503 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_31 : fastSlice1_2503 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_32 : fastSlice1_2503 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_33 : fastSlice1_2503 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_34 : fastSlice1_2503 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_35 : fastSlice1_2503 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_36 : fastSlice1_2503 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_37 : fastSlice1_2503 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_38 : fastSlice1_2503 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_39 : fastSlice1_2503 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2503_40 : fastSlice1_2503 40 = true := by
  decide +kernel

public theorem point1_2503 : stepCheck 1 2503 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2503 u1_2503 v1_2503
    left1_2503 right1_2503
  intro b
  rw [sliceEq1_2503]
  fin_cases b
  · exact slice1_2503_0
  · exact slice1_2503_1
  · exact slice1_2503_2
  · exact slice1_2503_3
  · exact slice1_2503_4
  · exact slice1_2503_5
  · exact slice1_2503_6
  · exact slice1_2503_7
  · exact slice1_2503_8
  · exact slice1_2503_9
  · exact slice1_2503_10
  · exact slice1_2503_11
  · exact slice1_2503_12
  · exact slice1_2503_13
  · exact slice1_2503_14
  · exact slice1_2503_15
  · exact slice1_2503_16
  · exact slice1_2503_17
  · exact slice1_2503_18
  · exact slice1_2503_19
  · exact slice1_2503_20
  · exact slice1_2503_21
  · exact slice1_2503_22
  · exact slice1_2503_23
  · exact slice1_2503_24
  · exact slice1_2503_25
  · exact slice1_2503_26
  · exact slice1_2503_27
  · exact slice1_2503_28
  · exact slice1_2503_29
  · exact slice1_2503_30
  · exact slice1_2503_31
  · exact slice1_2503_32
  · exact slice1_2503_33
  · exact slice1_2503_34
  · exact slice1_2503_35
  · exact slice1_2503_36
  · exact slice1_2503_37
  · exact slice1_2503_38
  · exact slice1_2503_39
  · exact slice1_2503_40

set_option maxHeartbeats 1600000 in
public theorem point1_2504 : stepCheck 1 2504 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2505 : stepCheck 1 2505 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2506 : stepCheck 1 2506 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2507 : stepCheck 1 2507 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2508 : stepCheck 1 2508 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2509 : stepCheck 1 2509 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
