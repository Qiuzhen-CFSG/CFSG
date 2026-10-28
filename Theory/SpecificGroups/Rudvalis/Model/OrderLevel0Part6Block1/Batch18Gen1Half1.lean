module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 18, generator 1, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point1_2650 : stepCheck 1 2650 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2651 : stepCheck 1 2651 := by
  left
  decide +kernel

private def u1_2652 : List (Fin 96) := [65, 66, 3]
private def v1_2652 : List (Fin 96) := [67, 58, 46, 3, 17, 4, 36, 4, 53, 80, 27, 22, 8, 6, 73]
private def lhs1_2652 (x : Nat) : Nat := Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map3 (x)))
private def rhs1_2652 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map17 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map53 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map73 (x)))))))))))))))
private theorem lhs1_2652_eq : lhs1_2652 = Compressed.eval u1_2652 := by rfl
private theorem rhs1_2652_eq : rhs1_2652 = Compressed.eval v1_2652 := by rfl
private def fastSlice1_2652 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2652 ((100 * b.val + x.val) % 4060) =
      rhs1_2652 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2652 (b : Fin 41) :
    Compressed.slice u1_2652 v1_2652 b = fastSlice1_2652 b := by
  simp only [Compressed.slice, fastSlice1_2652, lhs1_2652_eq, rhs1_2652_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2652 : u1_2652.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2652).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2652 : v1_2652.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2652)).map Compressed.up0 ++
      (L0Factor 1 2652).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_0 : fastSlice1_2652 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_1 : fastSlice1_2652 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_2 : fastSlice1_2652 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_3 : fastSlice1_2652 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_4 : fastSlice1_2652 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_5 : fastSlice1_2652 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_6 : fastSlice1_2652 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_7 : fastSlice1_2652 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_8 : fastSlice1_2652 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_9 : fastSlice1_2652 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_10 : fastSlice1_2652 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_11 : fastSlice1_2652 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_12 : fastSlice1_2652 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_13 : fastSlice1_2652 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_14 : fastSlice1_2652 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_15 : fastSlice1_2652 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_16 : fastSlice1_2652 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_17 : fastSlice1_2652 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_18 : fastSlice1_2652 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_19 : fastSlice1_2652 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_20 : fastSlice1_2652 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_21 : fastSlice1_2652 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_22 : fastSlice1_2652 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_23 : fastSlice1_2652 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_24 : fastSlice1_2652 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_25 : fastSlice1_2652 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_26 : fastSlice1_2652 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_27 : fastSlice1_2652 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_28 : fastSlice1_2652 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_29 : fastSlice1_2652 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_30 : fastSlice1_2652 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_31 : fastSlice1_2652 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_32 : fastSlice1_2652 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_33 : fastSlice1_2652 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_34 : fastSlice1_2652 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_35 : fastSlice1_2652 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_36 : fastSlice1_2652 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_37 : fastSlice1_2652 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_38 : fastSlice1_2652 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_39 : fastSlice1_2652 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2652_40 : fastSlice1_2652 40 = true := by
  decide +kernel

public theorem point1_2652 : stepCheck 1 2652 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2652 u1_2652 v1_2652
    left1_2652 right1_2652
  intro b
  rw [sliceEq1_2652]
  fin_cases b
  · exact slice1_2652_0
  · exact slice1_2652_1
  · exact slice1_2652_2
  · exact slice1_2652_3
  · exact slice1_2652_4
  · exact slice1_2652_5
  · exact slice1_2652_6
  · exact slice1_2652_7
  · exact slice1_2652_8
  · exact slice1_2652_9
  · exact slice1_2652_10
  · exact slice1_2652_11
  · exact slice1_2652_12
  · exact slice1_2652_13
  · exact slice1_2652_14
  · exact slice1_2652_15
  · exact slice1_2652_16
  · exact slice1_2652_17
  · exact slice1_2652_18
  · exact slice1_2652_19
  · exact slice1_2652_20
  · exact slice1_2652_21
  · exact slice1_2652_22
  · exact slice1_2652_23
  · exact slice1_2652_24
  · exact slice1_2652_25
  · exact slice1_2652_26
  · exact slice1_2652_27
  · exact slice1_2652_28
  · exact slice1_2652_29
  · exact slice1_2652_30
  · exact slice1_2652_31
  · exact slice1_2652_32
  · exact slice1_2652_33
  · exact slice1_2652_34
  · exact slice1_2652_35
  · exact slice1_2652_36
  · exact slice1_2652_37
  · exact slice1_2652_38
  · exact slice1_2652_39
  · exact slice1_2652_40

set_option maxHeartbeats 1600000 in
public theorem point1_2653 : stepCheck 1 2653 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2654 : stepCheck 1 2654 := by
  left
  decide +kernel

private def u1_2655 : List (Fin 96) := [46, 89, 3]
private def v1_2655 : List (Fin 96) := [67, 58, 24, 46, 4, 4, 16, 5, 5, 27, 59, 48, 81]
private def lhs1_2655 (x : Nat) : Nat := Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map89 (Part6Nat.force Compressed.map3 (x)))
private def rhs1_2655 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map48 (Part6Nat.force Compressed.map81 (x)))))))))))))
private theorem lhs1_2655_eq : lhs1_2655 = Compressed.eval u1_2655 := by rfl
private theorem rhs1_2655_eq : rhs1_2655 = Compressed.eval v1_2655 := by rfl
private def fastSlice1_2655 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2655 ((100 * b.val + x.val) % 4060) =
      rhs1_2655 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2655 (b : Fin 41) :
    Compressed.slice u1_2655 v1_2655 b = fastSlice1_2655 b := by
  simp only [Compressed.slice, fastSlice1_2655, lhs1_2655_eq, rhs1_2655_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2655 : u1_2655.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2655).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2655 : v1_2655.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2655)).map Compressed.up0 ++
      (L0Factor 1 2655).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_0 : fastSlice1_2655 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_1 : fastSlice1_2655 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_2 : fastSlice1_2655 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_3 : fastSlice1_2655 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_4 : fastSlice1_2655 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_5 : fastSlice1_2655 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_6 : fastSlice1_2655 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_7 : fastSlice1_2655 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_8 : fastSlice1_2655 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_9 : fastSlice1_2655 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_10 : fastSlice1_2655 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_11 : fastSlice1_2655 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_12 : fastSlice1_2655 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_13 : fastSlice1_2655 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_14 : fastSlice1_2655 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_15 : fastSlice1_2655 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_16 : fastSlice1_2655 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_17 : fastSlice1_2655 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_18 : fastSlice1_2655 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_19 : fastSlice1_2655 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_20 : fastSlice1_2655 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_21 : fastSlice1_2655 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_22 : fastSlice1_2655 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_23 : fastSlice1_2655 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_24 : fastSlice1_2655 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_25 : fastSlice1_2655 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_26 : fastSlice1_2655 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_27 : fastSlice1_2655 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_28 : fastSlice1_2655 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_29 : fastSlice1_2655 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_30 : fastSlice1_2655 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_31 : fastSlice1_2655 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_32 : fastSlice1_2655 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_33 : fastSlice1_2655 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_34 : fastSlice1_2655 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_35 : fastSlice1_2655 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_36 : fastSlice1_2655 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_37 : fastSlice1_2655 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_38 : fastSlice1_2655 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_39 : fastSlice1_2655 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2655_40 : fastSlice1_2655 40 = true := by
  decide +kernel

public theorem point1_2655 : stepCheck 1 2655 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2655 u1_2655 v1_2655
    left1_2655 right1_2655
  intro b
  rw [sliceEq1_2655]
  fin_cases b
  · exact slice1_2655_0
  · exact slice1_2655_1
  · exact slice1_2655_2
  · exact slice1_2655_3
  · exact slice1_2655_4
  · exact slice1_2655_5
  · exact slice1_2655_6
  · exact slice1_2655_7
  · exact slice1_2655_8
  · exact slice1_2655_9
  · exact slice1_2655_10
  · exact slice1_2655_11
  · exact slice1_2655_12
  · exact slice1_2655_13
  · exact slice1_2655_14
  · exact slice1_2655_15
  · exact slice1_2655_16
  · exact slice1_2655_17
  · exact slice1_2655_18
  · exact slice1_2655_19
  · exact slice1_2655_20
  · exact slice1_2655_21
  · exact slice1_2655_22
  · exact slice1_2655_23
  · exact slice1_2655_24
  · exact slice1_2655_25
  · exact slice1_2655_26
  · exact slice1_2655_27
  · exact slice1_2655_28
  · exact slice1_2655_29
  · exact slice1_2655_30
  · exact slice1_2655_31
  · exact slice1_2655_32
  · exact slice1_2655_33
  · exact slice1_2655_34
  · exact slice1_2655_35
  · exact slice1_2655_36
  · exact slice1_2655_37
  · exact slice1_2655_38
  · exact slice1_2655_39
  · exact slice1_2655_40

set_option maxHeartbeats 1600000 in
public theorem point1_2656 : stepCheck 1 2656 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2657 : stepCheck 1 2657 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2658 : stepCheck 1 2658 := by
  left
  decide +kernel

private def u1_2659 : List (Fin 96) := [12, 51, 66, 3]
private def v1_2659 : List (Fin 96) := [51, 19, 75, 15, 5, 5, 8, 40, 59, 42, 17, 31, 56, 56]
private def lhs1_2659 (x : Nat) : Nat := Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map3 (x))))
private def rhs1_2659 (x : Nat) : Nat := Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map15 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map17 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map56 (Part6Nat.force Compressed.map56 (x))))))))))))))
private theorem lhs1_2659_eq : lhs1_2659 = Compressed.eval u1_2659 := by rfl
private theorem rhs1_2659_eq : rhs1_2659 = Compressed.eval v1_2659 := by rfl
private def fastSlice1_2659 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2659 ((100 * b.val + x.val) % 4060) =
      rhs1_2659 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2659 (b : Fin 41) :
    Compressed.slice u1_2659 v1_2659 b = fastSlice1_2659 b := by
  simp only [Compressed.slice, fastSlice1_2659, lhs1_2659_eq, rhs1_2659_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2659 : u1_2659.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2659).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2659 : v1_2659.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2659)).map Compressed.up0 ++
      (L0Factor 1 2659).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_0 : fastSlice1_2659 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_1 : fastSlice1_2659 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_2 : fastSlice1_2659 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_3 : fastSlice1_2659 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_4 : fastSlice1_2659 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_5 : fastSlice1_2659 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_6 : fastSlice1_2659 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_7 : fastSlice1_2659 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_8 : fastSlice1_2659 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_9 : fastSlice1_2659 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_10 : fastSlice1_2659 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_11 : fastSlice1_2659 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_12 : fastSlice1_2659 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_13 : fastSlice1_2659 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_14 : fastSlice1_2659 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_15 : fastSlice1_2659 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_16 : fastSlice1_2659 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_17 : fastSlice1_2659 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_18 : fastSlice1_2659 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_19 : fastSlice1_2659 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_20 : fastSlice1_2659 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_21 : fastSlice1_2659 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_22 : fastSlice1_2659 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_23 : fastSlice1_2659 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_24 : fastSlice1_2659 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_25 : fastSlice1_2659 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_26 : fastSlice1_2659 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_27 : fastSlice1_2659 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_28 : fastSlice1_2659 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_29 : fastSlice1_2659 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_30 : fastSlice1_2659 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_31 : fastSlice1_2659 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_32 : fastSlice1_2659 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_33 : fastSlice1_2659 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_34 : fastSlice1_2659 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_35 : fastSlice1_2659 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_36 : fastSlice1_2659 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_37 : fastSlice1_2659 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_38 : fastSlice1_2659 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_39 : fastSlice1_2659 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2659_40 : fastSlice1_2659 40 = true := by
  decide +kernel

public theorem point1_2659 : stepCheck 1 2659 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2659 u1_2659 v1_2659
    left1_2659 right1_2659
  intro b
  rw [sliceEq1_2659]
  fin_cases b
  · exact slice1_2659_0
  · exact slice1_2659_1
  · exact slice1_2659_2
  · exact slice1_2659_3
  · exact slice1_2659_4
  · exact slice1_2659_5
  · exact slice1_2659_6
  · exact slice1_2659_7
  · exact slice1_2659_8
  · exact slice1_2659_9
  · exact slice1_2659_10
  · exact slice1_2659_11
  · exact slice1_2659_12
  · exact slice1_2659_13
  · exact slice1_2659_14
  · exact slice1_2659_15
  · exact slice1_2659_16
  · exact slice1_2659_17
  · exact slice1_2659_18
  · exact slice1_2659_19
  · exact slice1_2659_20
  · exact slice1_2659_21
  · exact slice1_2659_22
  · exact slice1_2659_23
  · exact slice1_2659_24
  · exact slice1_2659_25
  · exact slice1_2659_26
  · exact slice1_2659_27
  · exact slice1_2659_28
  · exact slice1_2659_29
  · exact slice1_2659_30
  · exact slice1_2659_31
  · exact slice1_2659_32
  · exact slice1_2659_33
  · exact slice1_2659_34
  · exact slice1_2659_35
  · exact slice1_2659_36
  · exact slice1_2659_37
  · exact slice1_2659_38
  · exact slice1_2659_39
  · exact slice1_2659_40

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
