module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 17, generator 1, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point1_2510 : stepCheck 1 2510 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2511 : stepCheck 1 2511 := by
  left
  decide +kernel

private def u1_2512 : List (Fin 96) := [46, 92, 60]
private def v1_2512 : List (Fin 96) := [0, 75, 76, 9, 36, 10, 27, 32, 48, 62, 56]
private def lhs1_2512 (x : Nat) : Nat := Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map92 (Part6Nat.force Compressed.map60 (x)))
private def rhs1_2512 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map76 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map48 (Part6Nat.force Compressed.map62 (Part6Nat.force Compressed.map56 (x)))))))))))
private theorem lhs1_2512_eq : lhs1_2512 = Compressed.eval u1_2512 := by rfl
private theorem rhs1_2512_eq : rhs1_2512 = Compressed.eval v1_2512 := by rfl
private def fastSlice1_2512 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2512 ((100 * b.val + x.val) % 4060) =
      rhs1_2512 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2512 (b : Fin 41) :
    Compressed.slice u1_2512 v1_2512 b = fastSlice1_2512 b := by
  simp only [Compressed.slice, fastSlice1_2512, lhs1_2512_eq, rhs1_2512_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2512 : u1_2512.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2512).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2512 : v1_2512.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2512)).map Compressed.up0 ++
      (L0Factor 1 2512).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_0 : fastSlice1_2512 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_1 : fastSlice1_2512 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_2 : fastSlice1_2512 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_3 : fastSlice1_2512 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_4 : fastSlice1_2512 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_5 : fastSlice1_2512 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_6 : fastSlice1_2512 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_7 : fastSlice1_2512 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_8 : fastSlice1_2512 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_9 : fastSlice1_2512 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_10 : fastSlice1_2512 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_11 : fastSlice1_2512 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_12 : fastSlice1_2512 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_13 : fastSlice1_2512 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_14 : fastSlice1_2512 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_15 : fastSlice1_2512 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_16 : fastSlice1_2512 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_17 : fastSlice1_2512 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_18 : fastSlice1_2512 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_19 : fastSlice1_2512 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_20 : fastSlice1_2512 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_21 : fastSlice1_2512 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_22 : fastSlice1_2512 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_23 : fastSlice1_2512 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_24 : fastSlice1_2512 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_25 : fastSlice1_2512 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_26 : fastSlice1_2512 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_27 : fastSlice1_2512 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_28 : fastSlice1_2512 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_29 : fastSlice1_2512 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_30 : fastSlice1_2512 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_31 : fastSlice1_2512 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_32 : fastSlice1_2512 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_33 : fastSlice1_2512 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_34 : fastSlice1_2512 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_35 : fastSlice1_2512 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_36 : fastSlice1_2512 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_37 : fastSlice1_2512 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_38 : fastSlice1_2512 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_39 : fastSlice1_2512 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2512_40 : fastSlice1_2512 40 = true := by
  decide +kernel

public theorem point1_2512 : stepCheck 1 2512 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2512 u1_2512 v1_2512
    left1_2512 right1_2512
  intro b
  rw [sliceEq1_2512]
  fin_cases b
  · exact slice1_2512_0
  · exact slice1_2512_1
  · exact slice1_2512_2
  · exact slice1_2512_3
  · exact slice1_2512_4
  · exact slice1_2512_5
  · exact slice1_2512_6
  · exact slice1_2512_7
  · exact slice1_2512_8
  · exact slice1_2512_9
  · exact slice1_2512_10
  · exact slice1_2512_11
  · exact slice1_2512_12
  · exact slice1_2512_13
  · exact slice1_2512_14
  · exact slice1_2512_15
  · exact slice1_2512_16
  · exact slice1_2512_17
  · exact slice1_2512_18
  · exact slice1_2512_19
  · exact slice1_2512_20
  · exact slice1_2512_21
  · exact slice1_2512_22
  · exact slice1_2512_23
  · exact slice1_2512_24
  · exact slice1_2512_25
  · exact slice1_2512_26
  · exact slice1_2512_27
  · exact slice1_2512_28
  · exact slice1_2512_29
  · exact slice1_2512_30
  · exact slice1_2512_31
  · exact slice1_2512_32
  · exact slice1_2512_33
  · exact slice1_2512_34
  · exact slice1_2512_35
  · exact slice1_2512_36
  · exact slice1_2512_37
  · exact slice1_2512_38
  · exact slice1_2512_39
  · exact slice1_2512_40

set_option maxHeartbeats 1600000 in
public theorem point1_2513 : stepCheck 1 2513 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2514 : stepCheck 1 2514 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2515 : stepCheck 1 2515 := by
  left
  decide +kernel

private def u1_2516 : List (Fin 96) := [50, 50, 78, 60]
private def v1_2516 : List (Fin 96) := [90, 50, 50, 3]
private def lhs1_2516 (x : Nat) : Nat := Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map60 (x))))
private def rhs1_2516 (x : Nat) : Nat := Part6Nat.force Compressed.map90 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map3 (x))))
private theorem lhs1_2516_eq : lhs1_2516 = Compressed.eval u1_2516 := by rfl
private theorem rhs1_2516_eq : rhs1_2516 = Compressed.eval v1_2516 := by rfl
private def fastSlice1_2516 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2516 ((100 * b.val + x.val) % 4060) =
      rhs1_2516 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2516 (b : Fin 41) :
    Compressed.slice u1_2516 v1_2516 b = fastSlice1_2516 b := by
  simp only [Compressed.slice, fastSlice1_2516, lhs1_2516_eq, rhs1_2516_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2516 : u1_2516.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2516).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2516 : v1_2516.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2516)).map Compressed.up0 ++
      (L0Factor 1 2516).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_0 : fastSlice1_2516 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_1 : fastSlice1_2516 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_2 : fastSlice1_2516 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_3 : fastSlice1_2516 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_4 : fastSlice1_2516 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_5 : fastSlice1_2516 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_6 : fastSlice1_2516 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_7 : fastSlice1_2516 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_8 : fastSlice1_2516 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_9 : fastSlice1_2516 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_10 : fastSlice1_2516 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_11 : fastSlice1_2516 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_12 : fastSlice1_2516 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_13 : fastSlice1_2516 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_14 : fastSlice1_2516 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_15 : fastSlice1_2516 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_16 : fastSlice1_2516 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_17 : fastSlice1_2516 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_18 : fastSlice1_2516 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_19 : fastSlice1_2516 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_20 : fastSlice1_2516 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_21 : fastSlice1_2516 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_22 : fastSlice1_2516 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_23 : fastSlice1_2516 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_24 : fastSlice1_2516 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_25 : fastSlice1_2516 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_26 : fastSlice1_2516 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_27 : fastSlice1_2516 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_28 : fastSlice1_2516 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_29 : fastSlice1_2516 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_30 : fastSlice1_2516 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_31 : fastSlice1_2516 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_32 : fastSlice1_2516 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_33 : fastSlice1_2516 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_34 : fastSlice1_2516 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_35 : fastSlice1_2516 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_36 : fastSlice1_2516 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_37 : fastSlice1_2516 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_38 : fastSlice1_2516 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_39 : fastSlice1_2516 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2516_40 : fastSlice1_2516 40 = true := by
  decide +kernel

public theorem point1_2516 : stepCheck 1 2516 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2516 u1_2516 v1_2516
    left1_2516 right1_2516
  intro b
  rw [sliceEq1_2516]
  fin_cases b
  · exact slice1_2516_0
  · exact slice1_2516_1
  · exact slice1_2516_2
  · exact slice1_2516_3
  · exact slice1_2516_4
  · exact slice1_2516_5
  · exact slice1_2516_6
  · exact slice1_2516_7
  · exact slice1_2516_8
  · exact slice1_2516_9
  · exact slice1_2516_10
  · exact slice1_2516_11
  · exact slice1_2516_12
  · exact slice1_2516_13
  · exact slice1_2516_14
  · exact slice1_2516_15
  · exact slice1_2516_16
  · exact slice1_2516_17
  · exact slice1_2516_18
  · exact slice1_2516_19
  · exact slice1_2516_20
  · exact slice1_2516_21
  · exact slice1_2516_22
  · exact slice1_2516_23
  · exact slice1_2516_24
  · exact slice1_2516_25
  · exact slice1_2516_26
  · exact slice1_2516_27
  · exact slice1_2516_28
  · exact slice1_2516_29
  · exact slice1_2516_30
  · exact slice1_2516_31
  · exact slice1_2516_32
  · exact slice1_2516_33
  · exact slice1_2516_34
  · exact slice1_2516_35
  · exact slice1_2516_36
  · exact slice1_2516_37
  · exact slice1_2516_38
  · exact slice1_2516_39
  · exact slice1_2516_40

set_option maxHeartbeats 1600000 in
public theorem point1_2517 : stepCheck 1 2517 := by
  left
  decide +kernel

private def u1_2518 : List (Fin 96) := [46, 66, 12, 60]
private def v1_2518 : List (Fin 96) := [14, 65, 14, 12, 3, 79, 4, 5, 44, 70, 57]
private def lhs1_2518 (x : Nat) : Nat := Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map60 (x))))
private def rhs1_2518 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map44 (Part6Nat.force Compressed.map70 (Part6Nat.force Compressed.map57 (x)))))))))))
private theorem lhs1_2518_eq : lhs1_2518 = Compressed.eval u1_2518 := by rfl
private theorem rhs1_2518_eq : rhs1_2518 = Compressed.eval v1_2518 := by rfl
private def fastSlice1_2518 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2518 ((100 * b.val + x.val) % 4060) =
      rhs1_2518 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2518 (b : Fin 41) :
    Compressed.slice u1_2518 v1_2518 b = fastSlice1_2518 b := by
  simp only [Compressed.slice, fastSlice1_2518, lhs1_2518_eq, rhs1_2518_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2518 : u1_2518.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2518).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2518 : v1_2518.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2518)).map Compressed.up0 ++
      (L0Factor 1 2518).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_0 : fastSlice1_2518 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_1 : fastSlice1_2518 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_2 : fastSlice1_2518 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_3 : fastSlice1_2518 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_4 : fastSlice1_2518 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_5 : fastSlice1_2518 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_6 : fastSlice1_2518 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_7 : fastSlice1_2518 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_8 : fastSlice1_2518 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_9 : fastSlice1_2518 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_10 : fastSlice1_2518 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_11 : fastSlice1_2518 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_12 : fastSlice1_2518 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_13 : fastSlice1_2518 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_14 : fastSlice1_2518 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_15 : fastSlice1_2518 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_16 : fastSlice1_2518 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_17 : fastSlice1_2518 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_18 : fastSlice1_2518 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_19 : fastSlice1_2518 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_20 : fastSlice1_2518 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_21 : fastSlice1_2518 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_22 : fastSlice1_2518 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_23 : fastSlice1_2518 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_24 : fastSlice1_2518 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_25 : fastSlice1_2518 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_26 : fastSlice1_2518 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_27 : fastSlice1_2518 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_28 : fastSlice1_2518 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_29 : fastSlice1_2518 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_30 : fastSlice1_2518 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_31 : fastSlice1_2518 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_32 : fastSlice1_2518 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_33 : fastSlice1_2518 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_34 : fastSlice1_2518 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_35 : fastSlice1_2518 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_36 : fastSlice1_2518 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_37 : fastSlice1_2518 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_38 : fastSlice1_2518 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_39 : fastSlice1_2518 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2518_40 : fastSlice1_2518 40 = true := by
  decide +kernel

public theorem point1_2518 : stepCheck 1 2518 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2518 u1_2518 v1_2518
    left1_2518 right1_2518
  intro b
  rw [sliceEq1_2518]
  fin_cases b
  · exact slice1_2518_0
  · exact slice1_2518_1
  · exact slice1_2518_2
  · exact slice1_2518_3
  · exact slice1_2518_4
  · exact slice1_2518_5
  · exact slice1_2518_6
  · exact slice1_2518_7
  · exact slice1_2518_8
  · exact slice1_2518_9
  · exact slice1_2518_10
  · exact slice1_2518_11
  · exact slice1_2518_12
  · exact slice1_2518_13
  · exact slice1_2518_14
  · exact slice1_2518_15
  · exact slice1_2518_16
  · exact slice1_2518_17
  · exact slice1_2518_18
  · exact slice1_2518_19
  · exact slice1_2518_20
  · exact slice1_2518_21
  · exact slice1_2518_22
  · exact slice1_2518_23
  · exact slice1_2518_24
  · exact slice1_2518_25
  · exact slice1_2518_26
  · exact slice1_2518_27
  · exact slice1_2518_28
  · exact slice1_2518_29
  · exact slice1_2518_30
  · exact slice1_2518_31
  · exact slice1_2518_32
  · exact slice1_2518_33
  · exact slice1_2518_34
  · exact slice1_2518_35
  · exact slice1_2518_36
  · exact slice1_2518_37
  · exact slice1_2518_38
  · exact slice1_2518_39
  · exact slice1_2518_40

set_option maxHeartbeats 1600000 in
public theorem point1_2519 : stepCheck 1 2519 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
