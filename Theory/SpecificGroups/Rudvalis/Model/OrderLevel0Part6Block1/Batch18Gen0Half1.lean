module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 18, generator 0, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u0_2650 : List (Fin 96) := [67, 12, 51, 95]
private def v0_2650 : List (Fin 96) := [14, 63, 75, 3, 5]
private def lhs0_2650 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map95 (x))))
private def rhs0_2650 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map5 (x)))))
private theorem lhs0_2650_eq : lhs0_2650 = Compressed.eval u0_2650 := by rfl
private theorem rhs0_2650_eq : rhs0_2650 = Compressed.eval v0_2650 := by rfl
private def fastSlice0_2650 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2650 ((100 * b.val + x.val) % 4060) =
      rhs0_2650 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2650 (b : Fin 41) :
    Compressed.slice u0_2650 v0_2650 b = fastSlice0_2650 b := by
  simp only [Compressed.slice, fastSlice0_2650, lhs0_2650_eq, rhs0_2650_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2650 : u0_2650.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2650).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2650 : v0_2650.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2650)).map Compressed.up0 ++
      (L0Factor 0 2650).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_0 : fastSlice0_2650 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_1 : fastSlice0_2650 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_2 : fastSlice0_2650 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_3 : fastSlice0_2650 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_4 : fastSlice0_2650 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_5 : fastSlice0_2650 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_6 : fastSlice0_2650 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_7 : fastSlice0_2650 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_8 : fastSlice0_2650 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_9 : fastSlice0_2650 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_10 : fastSlice0_2650 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_11 : fastSlice0_2650 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_12 : fastSlice0_2650 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_13 : fastSlice0_2650 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_14 : fastSlice0_2650 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_15 : fastSlice0_2650 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_16 : fastSlice0_2650 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_17 : fastSlice0_2650 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_18 : fastSlice0_2650 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_19 : fastSlice0_2650 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_20 : fastSlice0_2650 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_21 : fastSlice0_2650 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_22 : fastSlice0_2650 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_23 : fastSlice0_2650 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_24 : fastSlice0_2650 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_25 : fastSlice0_2650 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_26 : fastSlice0_2650 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_27 : fastSlice0_2650 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_28 : fastSlice0_2650 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_29 : fastSlice0_2650 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_30 : fastSlice0_2650 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_31 : fastSlice0_2650 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_32 : fastSlice0_2650 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_33 : fastSlice0_2650 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_34 : fastSlice0_2650 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_35 : fastSlice0_2650 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_36 : fastSlice0_2650 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_37 : fastSlice0_2650 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_38 : fastSlice0_2650 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_39 : fastSlice0_2650 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2650_40 : fastSlice0_2650 40 = true := by
  decide +kernel

public theorem point0_2650 : stepCheck 0 2650 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2650 u0_2650 v0_2650
    left0_2650 right0_2650
  intro b
  rw [sliceEq0_2650]
  fin_cases b
  · exact slice0_2650_0
  · exact slice0_2650_1
  · exact slice0_2650_2
  · exact slice0_2650_3
  · exact slice0_2650_4
  · exact slice0_2650_5
  · exact slice0_2650_6
  · exact slice0_2650_7
  · exact slice0_2650_8
  · exact slice0_2650_9
  · exact slice0_2650_10
  · exact slice0_2650_11
  · exact slice0_2650_12
  · exact slice0_2650_13
  · exact slice0_2650_14
  · exact slice0_2650_15
  · exact slice0_2650_16
  · exact slice0_2650_17
  · exact slice0_2650_18
  · exact slice0_2650_19
  · exact slice0_2650_20
  · exact slice0_2650_21
  · exact slice0_2650_22
  · exact slice0_2650_23
  · exact slice0_2650_24
  · exact slice0_2650_25
  · exact slice0_2650_26
  · exact slice0_2650_27
  · exact slice0_2650_28
  · exact slice0_2650_29
  · exact slice0_2650_30
  · exact slice0_2650_31
  · exact slice0_2650_32
  · exact slice0_2650_33
  · exact slice0_2650_34
  · exact slice0_2650_35
  · exact slice0_2650_36
  · exact slice0_2650_37
  · exact slice0_2650_38
  · exact slice0_2650_39
  · exact slice0_2650_40

set_option maxHeartbeats 1600000 in
public theorem point0_2651 : stepCheck 0 2651 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2652 : stepCheck 0 2652 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2653 : stepCheck 0 2653 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2654 : stepCheck 0 2654 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2655 : stepCheck 0 2655 := by
  left
  decide +kernel

private def u0_2656 : List (Fin 96) := [87, 89, 3]
private def v0_2656 : List (Fin 96) := [21, 24, 69, 60, 4, 4, 16, 9, 27, 31, 53, 80, 71, 88]
private def lhs0_2656 (x : Nat) : Nat := Part6Nat.force Compressed.map87 (Part6Nat.force Compressed.map89 (Part6Nat.force Compressed.map3 (x)))
private def rhs0_2656 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map53 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map88 (x))))))))))))))
private theorem lhs0_2656_eq : lhs0_2656 = Compressed.eval u0_2656 := by rfl
private theorem rhs0_2656_eq : rhs0_2656 = Compressed.eval v0_2656 := by rfl
private def fastSlice0_2656 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2656 ((100 * b.val + x.val) % 4060) =
      rhs0_2656 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2656 (b : Fin 41) :
    Compressed.slice u0_2656 v0_2656 b = fastSlice0_2656 b := by
  simp only [Compressed.slice, fastSlice0_2656, lhs0_2656_eq, rhs0_2656_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2656 : u0_2656.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2656).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2656 : v0_2656.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2656)).map Compressed.up0 ++
      (L0Factor 0 2656).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_0 : fastSlice0_2656 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_1 : fastSlice0_2656 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_2 : fastSlice0_2656 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_3 : fastSlice0_2656 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_4 : fastSlice0_2656 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_5 : fastSlice0_2656 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_6 : fastSlice0_2656 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_7 : fastSlice0_2656 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_8 : fastSlice0_2656 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_9 : fastSlice0_2656 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_10 : fastSlice0_2656 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_11 : fastSlice0_2656 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_12 : fastSlice0_2656 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_13 : fastSlice0_2656 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_14 : fastSlice0_2656 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_15 : fastSlice0_2656 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_16 : fastSlice0_2656 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_17 : fastSlice0_2656 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_18 : fastSlice0_2656 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_19 : fastSlice0_2656 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_20 : fastSlice0_2656 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_21 : fastSlice0_2656 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_22 : fastSlice0_2656 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_23 : fastSlice0_2656 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_24 : fastSlice0_2656 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_25 : fastSlice0_2656 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_26 : fastSlice0_2656 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_27 : fastSlice0_2656 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_28 : fastSlice0_2656 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_29 : fastSlice0_2656 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_30 : fastSlice0_2656 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_31 : fastSlice0_2656 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_32 : fastSlice0_2656 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_33 : fastSlice0_2656 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_34 : fastSlice0_2656 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_35 : fastSlice0_2656 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_36 : fastSlice0_2656 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_37 : fastSlice0_2656 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_38 : fastSlice0_2656 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_39 : fastSlice0_2656 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2656_40 : fastSlice0_2656 40 = true := by
  decide +kernel

public theorem point0_2656 : stepCheck 0 2656 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2656 u0_2656 v0_2656
    left0_2656 right0_2656
  intro b
  rw [sliceEq0_2656]
  fin_cases b
  · exact slice0_2656_0
  · exact slice0_2656_1
  · exact slice0_2656_2
  · exact slice0_2656_3
  · exact slice0_2656_4
  · exact slice0_2656_5
  · exact slice0_2656_6
  · exact slice0_2656_7
  · exact slice0_2656_8
  · exact slice0_2656_9
  · exact slice0_2656_10
  · exact slice0_2656_11
  · exact slice0_2656_12
  · exact slice0_2656_13
  · exact slice0_2656_14
  · exact slice0_2656_15
  · exact slice0_2656_16
  · exact slice0_2656_17
  · exact slice0_2656_18
  · exact slice0_2656_19
  · exact slice0_2656_20
  · exact slice0_2656_21
  · exact slice0_2656_22
  · exact slice0_2656_23
  · exact slice0_2656_24
  · exact slice0_2656_25
  · exact slice0_2656_26
  · exact slice0_2656_27
  · exact slice0_2656_28
  · exact slice0_2656_29
  · exact slice0_2656_30
  · exact slice0_2656_31
  · exact slice0_2656_32
  · exact slice0_2656_33
  · exact slice0_2656_34
  · exact slice0_2656_35
  · exact slice0_2656_36
  · exact slice0_2656_37
  · exact slice0_2656_38
  · exact slice0_2656_39
  · exact slice0_2656_40

set_option maxHeartbeats 1600000 in
public theorem point0_2657 : stepCheck 0 2657 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2658 : stepCheck 0 2658 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2659 : stepCheck 0 2659 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
