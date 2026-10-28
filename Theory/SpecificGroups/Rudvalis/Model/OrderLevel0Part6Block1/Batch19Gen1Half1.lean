module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 19, generator 1, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point1_2790 : stepCheck 1 2790 := by
  left
  decide +kernel

private def u1_2791 : List (Fin 96) := [63, 24, 76]
private def v1_2791 : List (Fin 96) := [0, 82, 19, 60, 8, 5, 30, 71, 59, 18, 37, 61]
private def lhs1_2791 (x : Nat) : Nat := Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map76 (x)))
private def rhs1_2791 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map30 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map61 (x))))))))))))
private theorem lhs1_2791_eq : lhs1_2791 = Compressed.eval u1_2791 := by rfl
private theorem rhs1_2791_eq : rhs1_2791 = Compressed.eval v1_2791 := by rfl
private def fastSlice1_2791 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2791 ((100 * b.val + x.val) % 4060) =
      rhs1_2791 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2791 (b : Fin 41) :
    Compressed.slice u1_2791 v1_2791 b = fastSlice1_2791 b := by
  simp only [Compressed.slice, fastSlice1_2791, lhs1_2791_eq, rhs1_2791_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2791 : u1_2791.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2791).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2791 : v1_2791.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2791)).map Compressed.up0 ++
      (L0Factor 1 2791).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_0 : fastSlice1_2791 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_1 : fastSlice1_2791 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_2 : fastSlice1_2791 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_3 : fastSlice1_2791 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_4 : fastSlice1_2791 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_5 : fastSlice1_2791 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_6 : fastSlice1_2791 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_7 : fastSlice1_2791 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_8 : fastSlice1_2791 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_9 : fastSlice1_2791 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_10 : fastSlice1_2791 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_11 : fastSlice1_2791 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_12 : fastSlice1_2791 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_13 : fastSlice1_2791 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_14 : fastSlice1_2791 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_15 : fastSlice1_2791 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_16 : fastSlice1_2791 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_17 : fastSlice1_2791 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_18 : fastSlice1_2791 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_19 : fastSlice1_2791 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_20 : fastSlice1_2791 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_21 : fastSlice1_2791 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_22 : fastSlice1_2791 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_23 : fastSlice1_2791 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_24 : fastSlice1_2791 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_25 : fastSlice1_2791 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_26 : fastSlice1_2791 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_27 : fastSlice1_2791 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_28 : fastSlice1_2791 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_29 : fastSlice1_2791 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_30 : fastSlice1_2791 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_31 : fastSlice1_2791 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_32 : fastSlice1_2791 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_33 : fastSlice1_2791 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_34 : fastSlice1_2791 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_35 : fastSlice1_2791 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_36 : fastSlice1_2791 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_37 : fastSlice1_2791 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_38 : fastSlice1_2791 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_39 : fastSlice1_2791 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2791_40 : fastSlice1_2791 40 = true := by
  decide +kernel

public theorem point1_2791 : stepCheck 1 2791 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2791 u1_2791 v1_2791
    left1_2791 right1_2791
  intro b
  rw [sliceEq1_2791]
  fin_cases b
  · exact slice1_2791_0
  · exact slice1_2791_1
  · exact slice1_2791_2
  · exact slice1_2791_3
  · exact slice1_2791_4
  · exact slice1_2791_5
  · exact slice1_2791_6
  · exact slice1_2791_7
  · exact slice1_2791_8
  · exact slice1_2791_9
  · exact slice1_2791_10
  · exact slice1_2791_11
  · exact slice1_2791_12
  · exact slice1_2791_13
  · exact slice1_2791_14
  · exact slice1_2791_15
  · exact slice1_2791_16
  · exact slice1_2791_17
  · exact slice1_2791_18
  · exact slice1_2791_19
  · exact slice1_2791_20
  · exact slice1_2791_21
  · exact slice1_2791_22
  · exact slice1_2791_23
  · exact slice1_2791_24
  · exact slice1_2791_25
  · exact slice1_2791_26
  · exact slice1_2791_27
  · exact slice1_2791_28
  · exact slice1_2791_29
  · exact slice1_2791_30
  · exact slice1_2791_31
  · exact slice1_2791_32
  · exact slice1_2791_33
  · exact slice1_2791_34
  · exact slice1_2791_35
  · exact slice1_2791_36
  · exact slice1_2791_37
  · exact slice1_2791_38
  · exact slice1_2791_39
  · exact slice1_2791_40

set_option maxHeartbeats 1600000 in
public theorem point1_2792 : stepCheck 1 2792 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2793 : stepCheck 1 2793 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2794 : stepCheck 1 2794 := by
  left
  decide +kernel

private def u1_2795 : List (Fin 96) := [75, 33, 78]
private def v1_2795 : List (Fin 96) := [21, 46, 19, 24, 84, 10, 93, 32, 32, 32, 52]
private def lhs1_2795 (x : Nat) : Nat := Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map78 (x)))
private def rhs1_2795 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map84 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map93 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map52 (x)))))))))))
private theorem lhs1_2795_eq : lhs1_2795 = Compressed.eval u1_2795 := by rfl
private theorem rhs1_2795_eq : rhs1_2795 = Compressed.eval v1_2795 := by rfl
private def fastSlice1_2795 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2795 ((100 * b.val + x.val) % 4060) =
      rhs1_2795 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2795 (b : Fin 41) :
    Compressed.slice u1_2795 v1_2795 b = fastSlice1_2795 b := by
  simp only [Compressed.slice, fastSlice1_2795, lhs1_2795_eq, rhs1_2795_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2795 : u1_2795.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2795).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2795 : v1_2795.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2795)).map Compressed.up0 ++
      (L0Factor 1 2795).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_0 : fastSlice1_2795 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_1 : fastSlice1_2795 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_2 : fastSlice1_2795 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_3 : fastSlice1_2795 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_4 : fastSlice1_2795 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_5 : fastSlice1_2795 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_6 : fastSlice1_2795 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_7 : fastSlice1_2795 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_8 : fastSlice1_2795 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_9 : fastSlice1_2795 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_10 : fastSlice1_2795 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_11 : fastSlice1_2795 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_12 : fastSlice1_2795 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_13 : fastSlice1_2795 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_14 : fastSlice1_2795 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_15 : fastSlice1_2795 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_16 : fastSlice1_2795 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_17 : fastSlice1_2795 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_18 : fastSlice1_2795 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_19 : fastSlice1_2795 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_20 : fastSlice1_2795 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_21 : fastSlice1_2795 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_22 : fastSlice1_2795 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_23 : fastSlice1_2795 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_24 : fastSlice1_2795 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_25 : fastSlice1_2795 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_26 : fastSlice1_2795 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_27 : fastSlice1_2795 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_28 : fastSlice1_2795 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_29 : fastSlice1_2795 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_30 : fastSlice1_2795 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_31 : fastSlice1_2795 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_32 : fastSlice1_2795 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_33 : fastSlice1_2795 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_34 : fastSlice1_2795 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_35 : fastSlice1_2795 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_36 : fastSlice1_2795 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_37 : fastSlice1_2795 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_38 : fastSlice1_2795 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_39 : fastSlice1_2795 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2795_40 : fastSlice1_2795 40 = true := by
  decide +kernel

public theorem point1_2795 : stepCheck 1 2795 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2795 u1_2795 v1_2795
    left1_2795 right1_2795
  intro b
  rw [sliceEq1_2795]
  fin_cases b
  · exact slice1_2795_0
  · exact slice1_2795_1
  · exact slice1_2795_2
  · exact slice1_2795_3
  · exact slice1_2795_4
  · exact slice1_2795_5
  · exact slice1_2795_6
  · exact slice1_2795_7
  · exact slice1_2795_8
  · exact slice1_2795_9
  · exact slice1_2795_10
  · exact slice1_2795_11
  · exact slice1_2795_12
  · exact slice1_2795_13
  · exact slice1_2795_14
  · exact slice1_2795_15
  · exact slice1_2795_16
  · exact slice1_2795_17
  · exact slice1_2795_18
  · exact slice1_2795_19
  · exact slice1_2795_20
  · exact slice1_2795_21
  · exact slice1_2795_22
  · exact slice1_2795_23
  · exact slice1_2795_24
  · exact slice1_2795_25
  · exact slice1_2795_26
  · exact slice1_2795_27
  · exact slice1_2795_28
  · exact slice1_2795_29
  · exact slice1_2795_30
  · exact slice1_2795_31
  · exact slice1_2795_32
  · exact slice1_2795_33
  · exact slice1_2795_34
  · exact slice1_2795_35
  · exact slice1_2795_36
  · exact slice1_2795_37
  · exact slice1_2795_38
  · exact slice1_2795_39
  · exact slice1_2795_40

set_option maxHeartbeats 1600000 in
public theorem point1_2796 : stepCheck 1 2796 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2797 : stepCheck 1 2797 := by
  left
  decide +kernel

private def u1_2798 : List (Fin 96) := [24, 51, 65]
private def v1_2798 : List (Fin 96) := [67, 46, 46, 60, 9, 9, 9, 5, 17, 23, 74, 84, 52, 56]
private def lhs1_2798 (x : Nat) : Nat := Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map65 (x)))
private def rhs1_2798 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map17 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map84 (Part6Nat.force Compressed.map52 (Part6Nat.force Compressed.map56 (x))))))))))))))
private theorem lhs1_2798_eq : lhs1_2798 = Compressed.eval u1_2798 := by rfl
private theorem rhs1_2798_eq : rhs1_2798 = Compressed.eval v1_2798 := by rfl
private def fastSlice1_2798 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2798 ((100 * b.val + x.val) % 4060) =
      rhs1_2798 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2798 (b : Fin 41) :
    Compressed.slice u1_2798 v1_2798 b = fastSlice1_2798 b := by
  simp only [Compressed.slice, fastSlice1_2798, lhs1_2798_eq, rhs1_2798_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2798 : u1_2798.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2798).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2798 : v1_2798.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2798)).map Compressed.up0 ++
      (L0Factor 1 2798).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_0 : fastSlice1_2798 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_1 : fastSlice1_2798 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_2 : fastSlice1_2798 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_3 : fastSlice1_2798 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_4 : fastSlice1_2798 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_5 : fastSlice1_2798 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_6 : fastSlice1_2798 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_7 : fastSlice1_2798 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_8 : fastSlice1_2798 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_9 : fastSlice1_2798 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_10 : fastSlice1_2798 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_11 : fastSlice1_2798 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_12 : fastSlice1_2798 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_13 : fastSlice1_2798 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_14 : fastSlice1_2798 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_15 : fastSlice1_2798 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_16 : fastSlice1_2798 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_17 : fastSlice1_2798 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_18 : fastSlice1_2798 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_19 : fastSlice1_2798 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_20 : fastSlice1_2798 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_21 : fastSlice1_2798 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_22 : fastSlice1_2798 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_23 : fastSlice1_2798 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_24 : fastSlice1_2798 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_25 : fastSlice1_2798 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_26 : fastSlice1_2798 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_27 : fastSlice1_2798 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_28 : fastSlice1_2798 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_29 : fastSlice1_2798 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_30 : fastSlice1_2798 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_31 : fastSlice1_2798 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_32 : fastSlice1_2798 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_33 : fastSlice1_2798 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_34 : fastSlice1_2798 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_35 : fastSlice1_2798 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_36 : fastSlice1_2798 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_37 : fastSlice1_2798 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_38 : fastSlice1_2798 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_39 : fastSlice1_2798 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2798_40 : fastSlice1_2798 40 = true := by
  decide +kernel

public theorem point1_2798 : stepCheck 1 2798 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2798 u1_2798 v1_2798
    left1_2798 right1_2798
  intro b
  rw [sliceEq1_2798]
  fin_cases b
  · exact slice1_2798_0
  · exact slice1_2798_1
  · exact slice1_2798_2
  · exact slice1_2798_3
  · exact slice1_2798_4
  · exact slice1_2798_5
  · exact slice1_2798_6
  · exact slice1_2798_7
  · exact slice1_2798_8
  · exact slice1_2798_9
  · exact slice1_2798_10
  · exact slice1_2798_11
  · exact slice1_2798_12
  · exact slice1_2798_13
  · exact slice1_2798_14
  · exact slice1_2798_15
  · exact slice1_2798_16
  · exact slice1_2798_17
  · exact slice1_2798_18
  · exact slice1_2798_19
  · exact slice1_2798_20
  · exact slice1_2798_21
  · exact slice1_2798_22
  · exact slice1_2798_23
  · exact slice1_2798_24
  · exact slice1_2798_25
  · exact slice1_2798_26
  · exact slice1_2798_27
  · exact slice1_2798_28
  · exact slice1_2798_29
  · exact slice1_2798_30
  · exact slice1_2798_31
  · exact slice1_2798_32
  · exact slice1_2798_33
  · exact slice1_2798_34
  · exact slice1_2798_35
  · exact slice1_2798_36
  · exact slice1_2798_37
  · exact slice1_2798_38
  · exact slice1_2798_39
  · exact slice1_2798_40

set_option maxHeartbeats 1600000 in
public theorem point1_2799 : stepCheck 1 2799 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
