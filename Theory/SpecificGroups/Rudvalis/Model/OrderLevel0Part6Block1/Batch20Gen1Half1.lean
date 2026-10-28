module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 20, generator 1, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point1_2930 : stepCheck 1 2930 := by
  left
  decide +kernel

private def u1_2931 : List (Fin 96) := [58, 46, 19, 24]
private def v1_2931 : List (Fin 96) := [14, 46, 82, 3, 6, 11, 8, 10, 6, 15, 32, 18, 59, 84, 88]
private def lhs1_2931 (x : Nat) : Nat := Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map24 (x))))
private def rhs1_2931 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map15 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map84 (Part6Nat.force Compressed.map88 (x)))))))))))))))
private theorem lhs1_2931_eq : lhs1_2931 = Compressed.eval u1_2931 := by rfl
private theorem rhs1_2931_eq : rhs1_2931 = Compressed.eval v1_2931 := by rfl
private def fastSlice1_2931 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2931 ((100 * b.val + x.val) % 4060) =
      rhs1_2931 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2931 (b : Fin 41) :
    Compressed.slice u1_2931 v1_2931 b = fastSlice1_2931 b := by
  simp only [Compressed.slice, fastSlice1_2931, lhs1_2931_eq, rhs1_2931_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2931 : u1_2931.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2931).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2931 : v1_2931.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2931)).map Compressed.up0 ++
      (L0Factor 1 2931).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_0 : fastSlice1_2931 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_1 : fastSlice1_2931 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_2 : fastSlice1_2931 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_3 : fastSlice1_2931 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_4 : fastSlice1_2931 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_5 : fastSlice1_2931 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_6 : fastSlice1_2931 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_7 : fastSlice1_2931 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_8 : fastSlice1_2931 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_9 : fastSlice1_2931 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_10 : fastSlice1_2931 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_11 : fastSlice1_2931 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_12 : fastSlice1_2931 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_13 : fastSlice1_2931 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_14 : fastSlice1_2931 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_15 : fastSlice1_2931 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_16 : fastSlice1_2931 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_17 : fastSlice1_2931 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_18 : fastSlice1_2931 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_19 : fastSlice1_2931 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_20 : fastSlice1_2931 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_21 : fastSlice1_2931 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_22 : fastSlice1_2931 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_23 : fastSlice1_2931 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_24 : fastSlice1_2931 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_25 : fastSlice1_2931 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_26 : fastSlice1_2931 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_27 : fastSlice1_2931 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_28 : fastSlice1_2931 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_29 : fastSlice1_2931 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_30 : fastSlice1_2931 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_31 : fastSlice1_2931 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_32 : fastSlice1_2931 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_33 : fastSlice1_2931 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_34 : fastSlice1_2931 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_35 : fastSlice1_2931 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_36 : fastSlice1_2931 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_37 : fastSlice1_2931 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_38 : fastSlice1_2931 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_39 : fastSlice1_2931 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2931_40 : fastSlice1_2931 40 = true := by
  decide +kernel

public theorem point1_2931 : stepCheck 1 2931 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2931 u1_2931 v1_2931
    left1_2931 right1_2931
  intro b
  rw [sliceEq1_2931]
  fin_cases b
  · exact slice1_2931_0
  · exact slice1_2931_1
  · exact slice1_2931_2
  · exact slice1_2931_3
  · exact slice1_2931_4
  · exact slice1_2931_5
  · exact slice1_2931_6
  · exact slice1_2931_7
  · exact slice1_2931_8
  · exact slice1_2931_9
  · exact slice1_2931_10
  · exact slice1_2931_11
  · exact slice1_2931_12
  · exact slice1_2931_13
  · exact slice1_2931_14
  · exact slice1_2931_15
  · exact slice1_2931_16
  · exact slice1_2931_17
  · exact slice1_2931_18
  · exact slice1_2931_19
  · exact slice1_2931_20
  · exact slice1_2931_21
  · exact slice1_2931_22
  · exact slice1_2931_23
  · exact slice1_2931_24
  · exact slice1_2931_25
  · exact slice1_2931_26
  · exact slice1_2931_27
  · exact slice1_2931_28
  · exact slice1_2931_29
  · exact slice1_2931_30
  · exact slice1_2931_31
  · exact slice1_2931_32
  · exact slice1_2931_33
  · exact slice1_2931_34
  · exact slice1_2931_35
  · exact slice1_2931_36
  · exact slice1_2931_37
  · exact slice1_2931_38
  · exact slice1_2931_39
  · exact slice1_2931_40

set_option maxHeartbeats 1600000 in
public theorem point1_2932 : stepCheck 1 2932 := by
  left
  decide +kernel

private def u1_2933 : List (Fin 96) := [92, 33, 24]
private def v1_2933 : List (Fin 96) := [14, 64, 63, 6, 16, 4, 93, 37, 25, 45, 74, 22, 8, 6, 73]
private def lhs1_2933 (x : Nat) : Nat := Part6Nat.force Compressed.map92 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map24 (x)))
private def rhs1_2933 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map93 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map73 (x)))))))))))))))
private theorem lhs1_2933_eq : lhs1_2933 = Compressed.eval u1_2933 := by rfl
private theorem rhs1_2933_eq : rhs1_2933 = Compressed.eval v1_2933 := by rfl
private def fastSlice1_2933 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2933 ((100 * b.val + x.val) % 4060) =
      rhs1_2933 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2933 (b : Fin 41) :
    Compressed.slice u1_2933 v1_2933 b = fastSlice1_2933 b := by
  simp only [Compressed.slice, fastSlice1_2933, lhs1_2933_eq, rhs1_2933_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2933 : u1_2933.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2933).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2933 : v1_2933.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2933)).map Compressed.up0 ++
      (L0Factor 1 2933).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_0 : fastSlice1_2933 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_1 : fastSlice1_2933 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_2 : fastSlice1_2933 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_3 : fastSlice1_2933 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_4 : fastSlice1_2933 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_5 : fastSlice1_2933 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_6 : fastSlice1_2933 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_7 : fastSlice1_2933 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_8 : fastSlice1_2933 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_9 : fastSlice1_2933 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_10 : fastSlice1_2933 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_11 : fastSlice1_2933 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_12 : fastSlice1_2933 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_13 : fastSlice1_2933 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_14 : fastSlice1_2933 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_15 : fastSlice1_2933 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_16 : fastSlice1_2933 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_17 : fastSlice1_2933 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_18 : fastSlice1_2933 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_19 : fastSlice1_2933 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_20 : fastSlice1_2933 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_21 : fastSlice1_2933 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_22 : fastSlice1_2933 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_23 : fastSlice1_2933 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_24 : fastSlice1_2933 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_25 : fastSlice1_2933 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_26 : fastSlice1_2933 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_27 : fastSlice1_2933 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_28 : fastSlice1_2933 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_29 : fastSlice1_2933 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_30 : fastSlice1_2933 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_31 : fastSlice1_2933 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_32 : fastSlice1_2933 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_33 : fastSlice1_2933 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_34 : fastSlice1_2933 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_35 : fastSlice1_2933 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_36 : fastSlice1_2933 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_37 : fastSlice1_2933 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_38 : fastSlice1_2933 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_39 : fastSlice1_2933 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2933_40 : fastSlice1_2933 40 = true := by
  decide +kernel

public theorem point1_2933 : stepCheck 1 2933 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2933 u1_2933 v1_2933
    left1_2933 right1_2933
  intro b
  rw [sliceEq1_2933]
  fin_cases b
  · exact slice1_2933_0
  · exact slice1_2933_1
  · exact slice1_2933_2
  · exact slice1_2933_3
  · exact slice1_2933_4
  · exact slice1_2933_5
  · exact slice1_2933_6
  · exact slice1_2933_7
  · exact slice1_2933_8
  · exact slice1_2933_9
  · exact slice1_2933_10
  · exact slice1_2933_11
  · exact slice1_2933_12
  · exact slice1_2933_13
  · exact slice1_2933_14
  · exact slice1_2933_15
  · exact slice1_2933_16
  · exact slice1_2933_17
  · exact slice1_2933_18
  · exact slice1_2933_19
  · exact slice1_2933_20
  · exact slice1_2933_21
  · exact slice1_2933_22
  · exact slice1_2933_23
  · exact slice1_2933_24
  · exact slice1_2933_25
  · exact slice1_2933_26
  · exact slice1_2933_27
  · exact slice1_2933_28
  · exact slice1_2933_29
  · exact slice1_2933_30
  · exact slice1_2933_31
  · exact slice1_2933_32
  · exact slice1_2933_33
  · exact slice1_2933_34
  · exact slice1_2933_35
  · exact slice1_2933_36
  · exact slice1_2933_37
  · exact slice1_2933_38
  · exact slice1_2933_39
  · exact slice1_2933_40

private def u1_2934 : List (Fin 96) := [19, 89, 24]
private def v1_2934 : List (Fin 96) := [0, 51, 92, 6, 10, 9, 36, 27, 31, 94, 10, 39, 18, 42, 86]
private def lhs1_2934 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map89 (Part6Nat.force Compressed.map24 (x)))
private def rhs1_2934 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map92 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map94 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map39 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map86 (x)))))))))))))))
private theorem lhs1_2934_eq : lhs1_2934 = Compressed.eval u1_2934 := by rfl
private theorem rhs1_2934_eq : rhs1_2934 = Compressed.eval v1_2934 := by rfl
private def fastSlice1_2934 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2934 ((100 * b.val + x.val) % 4060) =
      rhs1_2934 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2934 (b : Fin 41) :
    Compressed.slice u1_2934 v1_2934 b = fastSlice1_2934 b := by
  simp only [Compressed.slice, fastSlice1_2934, lhs1_2934_eq, rhs1_2934_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2934 : u1_2934.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2934).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2934 : v1_2934.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2934)).map Compressed.up0 ++
      (L0Factor 1 2934).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_0 : fastSlice1_2934 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_1 : fastSlice1_2934 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_2 : fastSlice1_2934 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_3 : fastSlice1_2934 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_4 : fastSlice1_2934 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_5 : fastSlice1_2934 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_6 : fastSlice1_2934 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_7 : fastSlice1_2934 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_8 : fastSlice1_2934 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_9 : fastSlice1_2934 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_10 : fastSlice1_2934 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_11 : fastSlice1_2934 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_12 : fastSlice1_2934 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_13 : fastSlice1_2934 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_14 : fastSlice1_2934 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_15 : fastSlice1_2934 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_16 : fastSlice1_2934 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_17 : fastSlice1_2934 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_18 : fastSlice1_2934 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_19 : fastSlice1_2934 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_20 : fastSlice1_2934 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_21 : fastSlice1_2934 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_22 : fastSlice1_2934 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_23 : fastSlice1_2934 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_24 : fastSlice1_2934 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_25 : fastSlice1_2934 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_26 : fastSlice1_2934 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_27 : fastSlice1_2934 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_28 : fastSlice1_2934 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_29 : fastSlice1_2934 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_30 : fastSlice1_2934 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_31 : fastSlice1_2934 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_32 : fastSlice1_2934 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_33 : fastSlice1_2934 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_34 : fastSlice1_2934 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_35 : fastSlice1_2934 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_36 : fastSlice1_2934 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_37 : fastSlice1_2934 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_38 : fastSlice1_2934 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_39 : fastSlice1_2934 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2934_40 : fastSlice1_2934 40 = true := by
  decide +kernel

public theorem point1_2934 : stepCheck 1 2934 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2934 u1_2934 v1_2934
    left1_2934 right1_2934
  intro b
  rw [sliceEq1_2934]
  fin_cases b
  · exact slice1_2934_0
  · exact slice1_2934_1
  · exact slice1_2934_2
  · exact slice1_2934_3
  · exact slice1_2934_4
  · exact slice1_2934_5
  · exact slice1_2934_6
  · exact slice1_2934_7
  · exact slice1_2934_8
  · exact slice1_2934_9
  · exact slice1_2934_10
  · exact slice1_2934_11
  · exact slice1_2934_12
  · exact slice1_2934_13
  · exact slice1_2934_14
  · exact slice1_2934_15
  · exact slice1_2934_16
  · exact slice1_2934_17
  · exact slice1_2934_18
  · exact slice1_2934_19
  · exact slice1_2934_20
  · exact slice1_2934_21
  · exact slice1_2934_22
  · exact slice1_2934_23
  · exact slice1_2934_24
  · exact slice1_2934_25
  · exact slice1_2934_26
  · exact slice1_2934_27
  · exact slice1_2934_28
  · exact slice1_2934_29
  · exact slice1_2934_30
  · exact slice1_2934_31
  · exact slice1_2934_32
  · exact slice1_2934_33
  · exact slice1_2934_34
  · exact slice1_2934_35
  · exact slice1_2934_36
  · exact slice1_2934_37
  · exact slice1_2934_38
  · exact slice1_2934_39
  · exact slice1_2934_40

set_option maxHeartbeats 1600000 in
public theorem point1_2935 : stepCheck 1 2935 := by
  left
  decide +kernel

private def u1_2936 : List (Fin 96) := [50, 89, 24]
private def v1_2936 : List (Fin 96) := [90, 46, 58, 6, 16, 4, 93, 37, 25, 45, 74, 22, 8, 6, 73]
private def lhs1_2936 (x : Nat) : Nat := Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map89 (Part6Nat.force Compressed.map24 (x)))
private def rhs1_2936 (x : Nat) : Nat := Part6Nat.force Compressed.map90 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map93 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map73 (x)))))))))))))))
private theorem lhs1_2936_eq : lhs1_2936 = Compressed.eval u1_2936 := by rfl
private theorem rhs1_2936_eq : rhs1_2936 = Compressed.eval v1_2936 := by rfl
private def fastSlice1_2936 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2936 ((100 * b.val + x.val) % 4060) =
      rhs1_2936 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2936 (b : Fin 41) :
    Compressed.slice u1_2936 v1_2936 b = fastSlice1_2936 b := by
  simp only [Compressed.slice, fastSlice1_2936, lhs1_2936_eq, rhs1_2936_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2936 : u1_2936.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2936).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2936 : v1_2936.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2936)).map Compressed.up0 ++
      (L0Factor 1 2936).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_0 : fastSlice1_2936 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_1 : fastSlice1_2936 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_2 : fastSlice1_2936 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_3 : fastSlice1_2936 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_4 : fastSlice1_2936 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_5 : fastSlice1_2936 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_6 : fastSlice1_2936 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_7 : fastSlice1_2936 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_8 : fastSlice1_2936 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_9 : fastSlice1_2936 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_10 : fastSlice1_2936 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_11 : fastSlice1_2936 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_12 : fastSlice1_2936 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_13 : fastSlice1_2936 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_14 : fastSlice1_2936 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_15 : fastSlice1_2936 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_16 : fastSlice1_2936 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_17 : fastSlice1_2936 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_18 : fastSlice1_2936 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_19 : fastSlice1_2936 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_20 : fastSlice1_2936 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_21 : fastSlice1_2936 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_22 : fastSlice1_2936 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_23 : fastSlice1_2936 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_24 : fastSlice1_2936 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_25 : fastSlice1_2936 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_26 : fastSlice1_2936 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_27 : fastSlice1_2936 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_28 : fastSlice1_2936 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_29 : fastSlice1_2936 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_30 : fastSlice1_2936 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_31 : fastSlice1_2936 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_32 : fastSlice1_2936 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_33 : fastSlice1_2936 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_34 : fastSlice1_2936 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_35 : fastSlice1_2936 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_36 : fastSlice1_2936 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_37 : fastSlice1_2936 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_38 : fastSlice1_2936 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_39 : fastSlice1_2936 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2936_40 : fastSlice1_2936 40 = true := by
  decide +kernel

public theorem point1_2936 : stepCheck 1 2936 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2936 u1_2936 v1_2936
    left1_2936 right1_2936
  intro b
  rw [sliceEq1_2936]
  fin_cases b
  · exact slice1_2936_0
  · exact slice1_2936_1
  · exact slice1_2936_2
  · exact slice1_2936_3
  · exact slice1_2936_4
  · exact slice1_2936_5
  · exact slice1_2936_6
  · exact slice1_2936_7
  · exact slice1_2936_8
  · exact slice1_2936_9
  · exact slice1_2936_10
  · exact slice1_2936_11
  · exact slice1_2936_12
  · exact slice1_2936_13
  · exact slice1_2936_14
  · exact slice1_2936_15
  · exact slice1_2936_16
  · exact slice1_2936_17
  · exact slice1_2936_18
  · exact slice1_2936_19
  · exact slice1_2936_20
  · exact slice1_2936_21
  · exact slice1_2936_22
  · exact slice1_2936_23
  · exact slice1_2936_24
  · exact slice1_2936_25
  · exact slice1_2936_26
  · exact slice1_2936_27
  · exact slice1_2936_28
  · exact slice1_2936_29
  · exact slice1_2936_30
  · exact slice1_2936_31
  · exact slice1_2936_32
  · exact slice1_2936_33
  · exact slice1_2936_34
  · exact slice1_2936_35
  · exact slice1_2936_36
  · exact slice1_2936_37
  · exact slice1_2936_38
  · exact slice1_2936_39
  · exact slice1_2936_40

private def u1_2937 : List (Fin 96) := [64, 66, 24]
private def v1_2937 : List (Fin 96) := [14, 92, 21, 6, 16, 25, 71, 23, 13, 68, 88]
private def lhs1_2937 (x : Nat) : Nat := Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map24 (x)))
private def rhs1_2937 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map92 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map68 (Part6Nat.force Compressed.map88 (x)))))))))))
private theorem lhs1_2937_eq : lhs1_2937 = Compressed.eval u1_2937 := by rfl
private theorem rhs1_2937_eq : rhs1_2937 = Compressed.eval v1_2937 := by rfl
private def fastSlice1_2937 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2937 ((100 * b.val + x.val) % 4060) =
      rhs1_2937 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2937 (b : Fin 41) :
    Compressed.slice u1_2937 v1_2937 b = fastSlice1_2937 b := by
  simp only [Compressed.slice, fastSlice1_2937, lhs1_2937_eq, rhs1_2937_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2937 : u1_2937.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2937).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2937 : v1_2937.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2937)).map Compressed.up0 ++
      (L0Factor 1 2937).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_0 : fastSlice1_2937 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_1 : fastSlice1_2937 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_2 : fastSlice1_2937 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_3 : fastSlice1_2937 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_4 : fastSlice1_2937 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_5 : fastSlice1_2937 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_6 : fastSlice1_2937 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_7 : fastSlice1_2937 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_8 : fastSlice1_2937 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_9 : fastSlice1_2937 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_10 : fastSlice1_2937 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_11 : fastSlice1_2937 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_12 : fastSlice1_2937 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_13 : fastSlice1_2937 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_14 : fastSlice1_2937 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_15 : fastSlice1_2937 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_16 : fastSlice1_2937 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_17 : fastSlice1_2937 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_18 : fastSlice1_2937 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_19 : fastSlice1_2937 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_20 : fastSlice1_2937 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_21 : fastSlice1_2937 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_22 : fastSlice1_2937 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_23 : fastSlice1_2937 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_24 : fastSlice1_2937 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_25 : fastSlice1_2937 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_26 : fastSlice1_2937 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_27 : fastSlice1_2937 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_28 : fastSlice1_2937 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_29 : fastSlice1_2937 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_30 : fastSlice1_2937 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_31 : fastSlice1_2937 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_32 : fastSlice1_2937 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_33 : fastSlice1_2937 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_34 : fastSlice1_2937 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_35 : fastSlice1_2937 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_36 : fastSlice1_2937 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_37 : fastSlice1_2937 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_38 : fastSlice1_2937 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_39 : fastSlice1_2937 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2937_40 : fastSlice1_2937 40 = true := by
  decide +kernel

public theorem point1_2937 : stepCheck 1 2937 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2937 u1_2937 v1_2937
    left1_2937 right1_2937
  intro b
  rw [sliceEq1_2937]
  fin_cases b
  · exact slice1_2937_0
  · exact slice1_2937_1
  · exact slice1_2937_2
  · exact slice1_2937_3
  · exact slice1_2937_4
  · exact slice1_2937_5
  · exact slice1_2937_6
  · exact slice1_2937_7
  · exact slice1_2937_8
  · exact slice1_2937_9
  · exact slice1_2937_10
  · exact slice1_2937_11
  · exact slice1_2937_12
  · exact slice1_2937_13
  · exact slice1_2937_14
  · exact slice1_2937_15
  · exact slice1_2937_16
  · exact slice1_2937_17
  · exact slice1_2937_18
  · exact slice1_2937_19
  · exact slice1_2937_20
  · exact slice1_2937_21
  · exact slice1_2937_22
  · exact slice1_2937_23
  · exact slice1_2937_24
  · exact slice1_2937_25
  · exact slice1_2937_26
  · exact slice1_2937_27
  · exact slice1_2937_28
  · exact slice1_2937_29
  · exact slice1_2937_30
  · exact slice1_2937_31
  · exact slice1_2937_32
  · exact slice1_2937_33
  · exact slice1_2937_34
  · exact slice1_2937_35
  · exact slice1_2937_36
  · exact slice1_2937_37
  · exact slice1_2937_38
  · exact slice1_2937_39
  · exact slice1_2937_40

private def u1_2938 : List (Fin 96) := [50, 19, 50, 58]
private def v1_2938 : List (Fin 96) := [0, 50, 19, 63]
private def lhs1_2938 (x : Nat) : Nat := Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map58 (x))))
private def rhs1_2938 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map63 (x))))
private theorem lhs1_2938_eq : lhs1_2938 = Compressed.eval u1_2938 := by rfl
private theorem rhs1_2938_eq : rhs1_2938 = Compressed.eval v1_2938 := by rfl
private def fastSlice1_2938 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2938 ((100 * b.val + x.val) % 4060) =
      rhs1_2938 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2938 (b : Fin 41) :
    Compressed.slice u1_2938 v1_2938 b = fastSlice1_2938 b := by
  simp only [Compressed.slice, fastSlice1_2938, lhs1_2938_eq, rhs1_2938_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2938 : u1_2938.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2938).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2938 : v1_2938.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2938)).map Compressed.up0 ++
      (L0Factor 1 2938).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_0 : fastSlice1_2938 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_1 : fastSlice1_2938 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_2 : fastSlice1_2938 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_3 : fastSlice1_2938 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_4 : fastSlice1_2938 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_5 : fastSlice1_2938 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_6 : fastSlice1_2938 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_7 : fastSlice1_2938 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_8 : fastSlice1_2938 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_9 : fastSlice1_2938 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_10 : fastSlice1_2938 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_11 : fastSlice1_2938 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_12 : fastSlice1_2938 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_13 : fastSlice1_2938 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_14 : fastSlice1_2938 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_15 : fastSlice1_2938 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_16 : fastSlice1_2938 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_17 : fastSlice1_2938 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_18 : fastSlice1_2938 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_19 : fastSlice1_2938 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_20 : fastSlice1_2938 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_21 : fastSlice1_2938 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_22 : fastSlice1_2938 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_23 : fastSlice1_2938 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_24 : fastSlice1_2938 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_25 : fastSlice1_2938 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_26 : fastSlice1_2938 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_27 : fastSlice1_2938 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_28 : fastSlice1_2938 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_29 : fastSlice1_2938 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_30 : fastSlice1_2938 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_31 : fastSlice1_2938 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_32 : fastSlice1_2938 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_33 : fastSlice1_2938 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_34 : fastSlice1_2938 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_35 : fastSlice1_2938 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_36 : fastSlice1_2938 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_37 : fastSlice1_2938 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_38 : fastSlice1_2938 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_39 : fastSlice1_2938 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2938_40 : fastSlice1_2938 40 = true := by
  decide +kernel

public theorem point1_2938 : stepCheck 1 2938 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2938 u1_2938 v1_2938
    left1_2938 right1_2938
  intro b
  rw [sliceEq1_2938]
  fin_cases b
  · exact slice1_2938_0
  · exact slice1_2938_1
  · exact slice1_2938_2
  · exact slice1_2938_3
  · exact slice1_2938_4
  · exact slice1_2938_5
  · exact slice1_2938_6
  · exact slice1_2938_7
  · exact slice1_2938_8
  · exact slice1_2938_9
  · exact slice1_2938_10
  · exact slice1_2938_11
  · exact slice1_2938_12
  · exact slice1_2938_13
  · exact slice1_2938_14
  · exact slice1_2938_15
  · exact slice1_2938_16
  · exact slice1_2938_17
  · exact slice1_2938_18
  · exact slice1_2938_19
  · exact slice1_2938_20
  · exact slice1_2938_21
  · exact slice1_2938_22
  · exact slice1_2938_23
  · exact slice1_2938_24
  · exact slice1_2938_25
  · exact slice1_2938_26
  · exact slice1_2938_27
  · exact slice1_2938_28
  · exact slice1_2938_29
  · exact slice1_2938_30
  · exact slice1_2938_31
  · exact slice1_2938_32
  · exact slice1_2938_33
  · exact slice1_2938_34
  · exact slice1_2938_35
  · exact slice1_2938_36
  · exact slice1_2938_37
  · exact slice1_2938_38
  · exact slice1_2938_39
  · exact slice1_2938_40

set_option maxHeartbeats 1600000 in
public theorem point1_2939 : stepCheck 1 2939 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
