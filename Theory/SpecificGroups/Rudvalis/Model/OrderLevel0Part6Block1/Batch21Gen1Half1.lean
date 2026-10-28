module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 21, generator 1, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u1_3070 : List (Fin 96) := [89, 12, 46]
private def v1_3070 : List (Fin 96) := [14, 33, 21, 12, 60, 6, 5, 13, 27, 85, 22, 47]
private def lhs1_3070 (x : Nat) : Nat := Part6Nat.force Compressed.map89 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map46 (x)))
private def rhs1_3070 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map85 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map47 (x))))))))))))
private theorem lhs1_3070_eq : lhs1_3070 = Compressed.eval u1_3070 := by rfl
private theorem rhs1_3070_eq : rhs1_3070 = Compressed.eval v1_3070 := by rfl
private def fastSlice1_3070 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3070 ((100 * b.val + x.val) % 4060) =
      rhs1_3070 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3070 (b : Fin 41) :
    Compressed.slice u1_3070 v1_3070 b = fastSlice1_3070 b := by
  simp only [Compressed.slice, fastSlice1_3070, lhs1_3070_eq, rhs1_3070_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3070 : u1_3070.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3070).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3070 : v1_3070.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3070)).map Compressed.up0 ++
      (L0Factor 1 3070).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_0 : fastSlice1_3070 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_1 : fastSlice1_3070 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_2 : fastSlice1_3070 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_3 : fastSlice1_3070 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_4 : fastSlice1_3070 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_5 : fastSlice1_3070 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_6 : fastSlice1_3070 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_7 : fastSlice1_3070 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_8 : fastSlice1_3070 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_9 : fastSlice1_3070 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_10 : fastSlice1_3070 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_11 : fastSlice1_3070 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_12 : fastSlice1_3070 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_13 : fastSlice1_3070 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_14 : fastSlice1_3070 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_15 : fastSlice1_3070 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_16 : fastSlice1_3070 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_17 : fastSlice1_3070 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_18 : fastSlice1_3070 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_19 : fastSlice1_3070 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_20 : fastSlice1_3070 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_21 : fastSlice1_3070 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_22 : fastSlice1_3070 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_23 : fastSlice1_3070 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_24 : fastSlice1_3070 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_25 : fastSlice1_3070 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_26 : fastSlice1_3070 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_27 : fastSlice1_3070 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_28 : fastSlice1_3070 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_29 : fastSlice1_3070 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_30 : fastSlice1_3070 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_31 : fastSlice1_3070 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_32 : fastSlice1_3070 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_33 : fastSlice1_3070 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_34 : fastSlice1_3070 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_35 : fastSlice1_3070 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_36 : fastSlice1_3070 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_37 : fastSlice1_3070 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_38 : fastSlice1_3070 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_39 : fastSlice1_3070 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3070_40 : fastSlice1_3070 40 = true := by
  decide +kernel

public theorem point1_3070 : stepCheck 1 3070 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3070 u1_3070 v1_3070
    left1_3070 right1_3070
  intro b
  rw [sliceEq1_3070]
  fin_cases b
  · exact slice1_3070_0
  · exact slice1_3070_1
  · exact slice1_3070_2
  · exact slice1_3070_3
  · exact slice1_3070_4
  · exact slice1_3070_5
  · exact slice1_3070_6
  · exact slice1_3070_7
  · exact slice1_3070_8
  · exact slice1_3070_9
  · exact slice1_3070_10
  · exact slice1_3070_11
  · exact slice1_3070_12
  · exact slice1_3070_13
  · exact slice1_3070_14
  · exact slice1_3070_15
  · exact slice1_3070_16
  · exact slice1_3070_17
  · exact slice1_3070_18
  · exact slice1_3070_19
  · exact slice1_3070_20
  · exact slice1_3070_21
  · exact slice1_3070_22
  · exact slice1_3070_23
  · exact slice1_3070_24
  · exact slice1_3070_25
  · exact slice1_3070_26
  · exact slice1_3070_27
  · exact slice1_3070_28
  · exact slice1_3070_29
  · exact slice1_3070_30
  · exact slice1_3070_31
  · exact slice1_3070_32
  · exact slice1_3070_33
  · exact slice1_3070_34
  · exact slice1_3070_35
  · exact slice1_3070_36
  · exact slice1_3070_37
  · exact slice1_3070_38
  · exact slice1_3070_39
  · exact slice1_3070_40

set_option maxHeartbeats 1600000 in
public theorem point1_3071 : stepCheck 1 3071 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3072 : stepCheck 1 3072 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3073 : stepCheck 1 3073 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3074 : stepCheck 1 3074 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3075 : stepCheck 1 3075 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3076 : stepCheck 1 3076 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3077 : stepCheck 1 3077 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3078 : stepCheck 1 3078 := by
  left
  decide +kernel

private def u1_3079 : List (Fin 96) := [50, 58, 24, 46]
private def v1_3079 : List (Fin 96) := [21, 89, 3, 11, 11, 11, 16, 94, 45, 53, 80, 55, 42, 86]
private def lhs1_3079 (x : Nat) : Nat := Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map46 (x))))
private def rhs1_3079 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map89 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map94 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map53 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map55 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map86 (x))))))))))))))
private theorem lhs1_3079_eq : lhs1_3079 = Compressed.eval u1_3079 := by rfl
private theorem rhs1_3079_eq : rhs1_3079 = Compressed.eval v1_3079 := by rfl
private def fastSlice1_3079 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3079 ((100 * b.val + x.val) % 4060) =
      rhs1_3079 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3079 (b : Fin 41) :
    Compressed.slice u1_3079 v1_3079 b = fastSlice1_3079 b := by
  simp only [Compressed.slice, fastSlice1_3079, lhs1_3079_eq, rhs1_3079_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3079 : u1_3079.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3079).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3079 : v1_3079.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3079)).map Compressed.up0 ++
      (L0Factor 1 3079).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_0 : fastSlice1_3079 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_1 : fastSlice1_3079 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_2 : fastSlice1_3079 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_3 : fastSlice1_3079 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_4 : fastSlice1_3079 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_5 : fastSlice1_3079 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_6 : fastSlice1_3079 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_7 : fastSlice1_3079 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_8 : fastSlice1_3079 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_9 : fastSlice1_3079 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_10 : fastSlice1_3079 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_11 : fastSlice1_3079 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_12 : fastSlice1_3079 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_13 : fastSlice1_3079 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_14 : fastSlice1_3079 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_15 : fastSlice1_3079 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_16 : fastSlice1_3079 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_17 : fastSlice1_3079 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_18 : fastSlice1_3079 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_19 : fastSlice1_3079 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_20 : fastSlice1_3079 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_21 : fastSlice1_3079 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_22 : fastSlice1_3079 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_23 : fastSlice1_3079 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_24 : fastSlice1_3079 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_25 : fastSlice1_3079 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_26 : fastSlice1_3079 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_27 : fastSlice1_3079 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_28 : fastSlice1_3079 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_29 : fastSlice1_3079 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_30 : fastSlice1_3079 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_31 : fastSlice1_3079 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_32 : fastSlice1_3079 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_33 : fastSlice1_3079 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_34 : fastSlice1_3079 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_35 : fastSlice1_3079 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_36 : fastSlice1_3079 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_37 : fastSlice1_3079 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_38 : fastSlice1_3079 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_39 : fastSlice1_3079 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3079_40 : fastSlice1_3079 40 = true := by
  decide +kernel

public theorem point1_3079 : stepCheck 1 3079 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3079 u1_3079 v1_3079
    left1_3079 right1_3079
  intro b
  rw [sliceEq1_3079]
  fin_cases b
  · exact slice1_3079_0
  · exact slice1_3079_1
  · exact slice1_3079_2
  · exact slice1_3079_3
  · exact slice1_3079_4
  · exact slice1_3079_5
  · exact slice1_3079_6
  · exact slice1_3079_7
  · exact slice1_3079_8
  · exact slice1_3079_9
  · exact slice1_3079_10
  · exact slice1_3079_11
  · exact slice1_3079_12
  · exact slice1_3079_13
  · exact slice1_3079_14
  · exact slice1_3079_15
  · exact slice1_3079_16
  · exact slice1_3079_17
  · exact slice1_3079_18
  · exact slice1_3079_19
  · exact slice1_3079_20
  · exact slice1_3079_21
  · exact slice1_3079_22
  · exact slice1_3079_23
  · exact slice1_3079_24
  · exact slice1_3079_25
  · exact slice1_3079_26
  · exact slice1_3079_27
  · exact slice1_3079_28
  · exact slice1_3079_29
  · exact slice1_3079_30
  · exact slice1_3079_31
  · exact slice1_3079_32
  · exact slice1_3079_33
  · exact slice1_3079_34
  · exact slice1_3079_35
  · exact slice1_3079_36
  · exact slice1_3079_37
  · exact slice1_3079_38
  · exact slice1_3079_39
  · exact slice1_3079_40

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
