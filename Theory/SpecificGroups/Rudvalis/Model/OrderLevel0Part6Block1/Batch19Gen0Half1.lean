module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 19, generator 0, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u0_2790 : List (Fin 96) := [0, 46, 24, 76]
private def v0_2790 : List (Fin 96) := [21, 75, 51, 36, 36, 13, 32, 23, 74, 6, 47, 56]
private def lhs0_2790 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map76 (x))))
private def rhs0_2790 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map47 (Part6Nat.force Compressed.map56 (x))))))))))))
private theorem lhs0_2790_eq : lhs0_2790 = Compressed.eval u0_2790 := by rfl
private theorem rhs0_2790_eq : rhs0_2790 = Compressed.eval v0_2790 := by rfl
private def fastSlice0_2790 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2790 ((100 * b.val + x.val) % 4060) =
      rhs0_2790 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2790 (b : Fin 41) :
    Compressed.slice u0_2790 v0_2790 b = fastSlice0_2790 b := by
  simp only [Compressed.slice, fastSlice0_2790, lhs0_2790_eq, rhs0_2790_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2790 : u0_2790.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2790).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2790 : v0_2790.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2790)).map Compressed.up0 ++
      (L0Factor 0 2790).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_0 : fastSlice0_2790 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_1 : fastSlice0_2790 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_2 : fastSlice0_2790 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_3 : fastSlice0_2790 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_4 : fastSlice0_2790 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_5 : fastSlice0_2790 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_6 : fastSlice0_2790 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_7 : fastSlice0_2790 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_8 : fastSlice0_2790 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_9 : fastSlice0_2790 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_10 : fastSlice0_2790 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_11 : fastSlice0_2790 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_12 : fastSlice0_2790 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_13 : fastSlice0_2790 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_14 : fastSlice0_2790 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_15 : fastSlice0_2790 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_16 : fastSlice0_2790 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_17 : fastSlice0_2790 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_18 : fastSlice0_2790 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_19 : fastSlice0_2790 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_20 : fastSlice0_2790 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_21 : fastSlice0_2790 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_22 : fastSlice0_2790 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_23 : fastSlice0_2790 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_24 : fastSlice0_2790 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_25 : fastSlice0_2790 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_26 : fastSlice0_2790 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_27 : fastSlice0_2790 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_28 : fastSlice0_2790 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_29 : fastSlice0_2790 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_30 : fastSlice0_2790 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_31 : fastSlice0_2790 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_32 : fastSlice0_2790 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_33 : fastSlice0_2790 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_34 : fastSlice0_2790 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_35 : fastSlice0_2790 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_36 : fastSlice0_2790 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_37 : fastSlice0_2790 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_38 : fastSlice0_2790 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_39 : fastSlice0_2790 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2790_40 : fastSlice0_2790 40 = true := by
  decide +kernel

public theorem point0_2790 : stepCheck 0 2790 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2790 u0_2790 v0_2790
    left0_2790 right0_2790
  intro b
  rw [sliceEq0_2790]
  fin_cases b
  · exact slice0_2790_0
  · exact slice0_2790_1
  · exact slice0_2790_2
  · exact slice0_2790_3
  · exact slice0_2790_4
  · exact slice0_2790_5
  · exact slice0_2790_6
  · exact slice0_2790_7
  · exact slice0_2790_8
  · exact slice0_2790_9
  · exact slice0_2790_10
  · exact slice0_2790_11
  · exact slice0_2790_12
  · exact slice0_2790_13
  · exact slice0_2790_14
  · exact slice0_2790_15
  · exact slice0_2790_16
  · exact slice0_2790_17
  · exact slice0_2790_18
  · exact slice0_2790_19
  · exact slice0_2790_20
  · exact slice0_2790_21
  · exact slice0_2790_22
  · exact slice0_2790_23
  · exact slice0_2790_24
  · exact slice0_2790_25
  · exact slice0_2790_26
  · exact slice0_2790_27
  · exact slice0_2790_28
  · exact slice0_2790_29
  · exact slice0_2790_30
  · exact slice0_2790_31
  · exact slice0_2790_32
  · exact slice0_2790_33
  · exact slice0_2790_34
  · exact slice0_2790_35
  · exact slice0_2790_36
  · exact slice0_2790_37
  · exact slice0_2790_38
  · exact slice0_2790_39
  · exact slice0_2790_40

set_option maxHeartbeats 1600000 in
public theorem point0_2791 : stepCheck 0 2791 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2792 : stepCheck 0 2792 := by
  left
  decide +kernel

private def u0_2793 : List (Fin 96) := [87, 65, 19]
private def v0_2793 : List (Fin 96) := [46, 65, 19, 5, 8, 11, 4, 5, 8, 6, 15, 84, 23, 27, 18, 88]
private def lhs0_2793 (x : Nat) : Nat := Part6Nat.force Compressed.map87 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map19 (x)))
private def rhs0_2793 (x : Nat) : Nat := Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map15 (Part6Nat.force Compressed.map84 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map88 (x))))))))))))))))
private theorem lhs0_2793_eq : lhs0_2793 = Compressed.eval u0_2793 := by rfl
private theorem rhs0_2793_eq : rhs0_2793 = Compressed.eval v0_2793 := by rfl
private def fastSlice0_2793 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2793 ((100 * b.val + x.val) % 4060) =
      rhs0_2793 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2793 (b : Fin 41) :
    Compressed.slice u0_2793 v0_2793 b = fastSlice0_2793 b := by
  simp only [Compressed.slice, fastSlice0_2793, lhs0_2793_eq, rhs0_2793_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2793 : u0_2793.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2793).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2793 : v0_2793.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2793)).map Compressed.up0 ++
      (L0Factor 0 2793).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_0 : fastSlice0_2793 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_1 : fastSlice0_2793 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_2 : fastSlice0_2793 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_3 : fastSlice0_2793 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_4 : fastSlice0_2793 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_5 : fastSlice0_2793 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_6 : fastSlice0_2793 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_7 : fastSlice0_2793 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_8 : fastSlice0_2793 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_9 : fastSlice0_2793 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_10 : fastSlice0_2793 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_11 : fastSlice0_2793 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_12 : fastSlice0_2793 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_13 : fastSlice0_2793 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_14 : fastSlice0_2793 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_15 : fastSlice0_2793 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_16 : fastSlice0_2793 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_17 : fastSlice0_2793 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_18 : fastSlice0_2793 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_19 : fastSlice0_2793 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_20 : fastSlice0_2793 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_21 : fastSlice0_2793 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_22 : fastSlice0_2793 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_23 : fastSlice0_2793 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_24 : fastSlice0_2793 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_25 : fastSlice0_2793 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_26 : fastSlice0_2793 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_27 : fastSlice0_2793 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_28 : fastSlice0_2793 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_29 : fastSlice0_2793 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_30 : fastSlice0_2793 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_31 : fastSlice0_2793 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_32 : fastSlice0_2793 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_33 : fastSlice0_2793 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_34 : fastSlice0_2793 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_35 : fastSlice0_2793 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_36 : fastSlice0_2793 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_37 : fastSlice0_2793 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_38 : fastSlice0_2793 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_39 : fastSlice0_2793 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2793_40 : fastSlice0_2793 40 = true := by
  decide +kernel

public theorem point0_2793 : stepCheck 0 2793 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2793 u0_2793 v0_2793
    left0_2793 right0_2793
  intro b
  rw [sliceEq0_2793]
  fin_cases b
  · exact slice0_2793_0
  · exact slice0_2793_1
  · exact slice0_2793_2
  · exact slice0_2793_3
  · exact slice0_2793_4
  · exact slice0_2793_5
  · exact slice0_2793_6
  · exact slice0_2793_7
  · exact slice0_2793_8
  · exact slice0_2793_9
  · exact slice0_2793_10
  · exact slice0_2793_11
  · exact slice0_2793_12
  · exact slice0_2793_13
  · exact slice0_2793_14
  · exact slice0_2793_15
  · exact slice0_2793_16
  · exact slice0_2793_17
  · exact slice0_2793_18
  · exact slice0_2793_19
  · exact slice0_2793_20
  · exact slice0_2793_21
  · exact slice0_2793_22
  · exact slice0_2793_23
  · exact slice0_2793_24
  · exact slice0_2793_25
  · exact slice0_2793_26
  · exact slice0_2793_27
  · exact slice0_2793_28
  · exact slice0_2793_29
  · exact slice0_2793_30
  · exact slice0_2793_31
  · exact slice0_2793_32
  · exact slice0_2793_33
  · exact slice0_2793_34
  · exact slice0_2793_35
  · exact slice0_2793_36
  · exact slice0_2793_37
  · exact slice0_2793_38
  · exact slice0_2793_39
  · exact slice0_2793_40

set_option maxHeartbeats 1600000 in
public theorem point0_2794 : stepCheck 0 2794 := by
  left
  decide +kernel

private def u0_2795 : List (Fin 96) := [0, 58, 33, 78]
private def v0_2795 : List (Fin 96) := [63, 89, 30, 79, 80, 27, 59, 81, 56]
private def lhs0_2795 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map78 (x))))
private def rhs0_2795 (x : Nat) : Nat := Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map89 (Part6Nat.force Compressed.map30 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map81 (Part6Nat.force Compressed.map56 (x)))))))))
private theorem lhs0_2795_eq : lhs0_2795 = Compressed.eval u0_2795 := by rfl
private theorem rhs0_2795_eq : rhs0_2795 = Compressed.eval v0_2795 := by rfl
private def fastSlice0_2795 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2795 ((100 * b.val + x.val) % 4060) =
      rhs0_2795 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2795 (b : Fin 41) :
    Compressed.slice u0_2795 v0_2795 b = fastSlice0_2795 b := by
  simp only [Compressed.slice, fastSlice0_2795, lhs0_2795_eq, rhs0_2795_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2795 : u0_2795.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2795).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2795 : v0_2795.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2795)).map Compressed.up0 ++
      (L0Factor 0 2795).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_0 : fastSlice0_2795 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_1 : fastSlice0_2795 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_2 : fastSlice0_2795 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_3 : fastSlice0_2795 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_4 : fastSlice0_2795 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_5 : fastSlice0_2795 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_6 : fastSlice0_2795 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_7 : fastSlice0_2795 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_8 : fastSlice0_2795 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_9 : fastSlice0_2795 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_10 : fastSlice0_2795 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_11 : fastSlice0_2795 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_12 : fastSlice0_2795 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_13 : fastSlice0_2795 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_14 : fastSlice0_2795 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_15 : fastSlice0_2795 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_16 : fastSlice0_2795 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_17 : fastSlice0_2795 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_18 : fastSlice0_2795 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_19 : fastSlice0_2795 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_20 : fastSlice0_2795 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_21 : fastSlice0_2795 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_22 : fastSlice0_2795 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_23 : fastSlice0_2795 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_24 : fastSlice0_2795 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_25 : fastSlice0_2795 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_26 : fastSlice0_2795 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_27 : fastSlice0_2795 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_28 : fastSlice0_2795 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_29 : fastSlice0_2795 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_30 : fastSlice0_2795 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_31 : fastSlice0_2795 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_32 : fastSlice0_2795 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_33 : fastSlice0_2795 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_34 : fastSlice0_2795 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_35 : fastSlice0_2795 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_36 : fastSlice0_2795 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_37 : fastSlice0_2795 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_38 : fastSlice0_2795 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_39 : fastSlice0_2795 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2795_40 : fastSlice0_2795 40 = true := by
  decide +kernel

public theorem point0_2795 : stepCheck 0 2795 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2795 u0_2795 v0_2795
    left0_2795 right0_2795
  intro b
  rw [sliceEq0_2795]
  fin_cases b
  · exact slice0_2795_0
  · exact slice0_2795_1
  · exact slice0_2795_2
  · exact slice0_2795_3
  · exact slice0_2795_4
  · exact slice0_2795_5
  · exact slice0_2795_6
  · exact slice0_2795_7
  · exact slice0_2795_8
  · exact slice0_2795_9
  · exact slice0_2795_10
  · exact slice0_2795_11
  · exact slice0_2795_12
  · exact slice0_2795_13
  · exact slice0_2795_14
  · exact slice0_2795_15
  · exact slice0_2795_16
  · exact slice0_2795_17
  · exact slice0_2795_18
  · exact slice0_2795_19
  · exact slice0_2795_20
  · exact slice0_2795_21
  · exact slice0_2795_22
  · exact slice0_2795_23
  · exact slice0_2795_24
  · exact slice0_2795_25
  · exact slice0_2795_26
  · exact slice0_2795_27
  · exact slice0_2795_28
  · exact slice0_2795_29
  · exact slice0_2795_30
  · exact slice0_2795_31
  · exact slice0_2795_32
  · exact slice0_2795_33
  · exact slice0_2795_34
  · exact slice0_2795_35
  · exact slice0_2795_36
  · exact slice0_2795_37
  · exact slice0_2795_38
  · exact slice0_2795_39
  · exact slice0_2795_40

set_option maxHeartbeats 1600000 in
public theorem point0_2796 : stepCheck 0 2796 := by
  left
  decide +kernel

private def u0_2797 : List (Fin 96) := [0, 24, 46, 65]
private def v0_2797 : List (Fin 96) := [14, 50, 77, 24, 4, 4, 30, 5, 44, 84, 48, 85, 31]
private def lhs0_2797 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map65 (x))))
private def rhs0_2797 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map30 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map44 (Part6Nat.force Compressed.map84 (Part6Nat.force Compressed.map48 (Part6Nat.force Compressed.map85 (Part6Nat.force Compressed.map31 (x)))))))))))))
private theorem lhs0_2797_eq : lhs0_2797 = Compressed.eval u0_2797 := by rfl
private theorem rhs0_2797_eq : rhs0_2797 = Compressed.eval v0_2797 := by rfl
private def fastSlice0_2797 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2797 ((100 * b.val + x.val) % 4060) =
      rhs0_2797 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2797 (b : Fin 41) :
    Compressed.slice u0_2797 v0_2797 b = fastSlice0_2797 b := by
  simp only [Compressed.slice, fastSlice0_2797, lhs0_2797_eq, rhs0_2797_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2797 : u0_2797.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2797).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2797 : v0_2797.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2797)).map Compressed.up0 ++
      (L0Factor 0 2797).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_0 : fastSlice0_2797 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_1 : fastSlice0_2797 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_2 : fastSlice0_2797 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_3 : fastSlice0_2797 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_4 : fastSlice0_2797 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_5 : fastSlice0_2797 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_6 : fastSlice0_2797 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_7 : fastSlice0_2797 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_8 : fastSlice0_2797 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_9 : fastSlice0_2797 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_10 : fastSlice0_2797 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_11 : fastSlice0_2797 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_12 : fastSlice0_2797 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_13 : fastSlice0_2797 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_14 : fastSlice0_2797 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_15 : fastSlice0_2797 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_16 : fastSlice0_2797 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_17 : fastSlice0_2797 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_18 : fastSlice0_2797 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_19 : fastSlice0_2797 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_20 : fastSlice0_2797 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_21 : fastSlice0_2797 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_22 : fastSlice0_2797 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_23 : fastSlice0_2797 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_24 : fastSlice0_2797 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_25 : fastSlice0_2797 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_26 : fastSlice0_2797 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_27 : fastSlice0_2797 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_28 : fastSlice0_2797 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_29 : fastSlice0_2797 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_30 : fastSlice0_2797 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_31 : fastSlice0_2797 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_32 : fastSlice0_2797 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_33 : fastSlice0_2797 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_34 : fastSlice0_2797 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_35 : fastSlice0_2797 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_36 : fastSlice0_2797 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_37 : fastSlice0_2797 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_38 : fastSlice0_2797 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_39 : fastSlice0_2797 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2797_40 : fastSlice0_2797 40 = true := by
  decide +kernel

public theorem point0_2797 : stepCheck 0 2797 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2797 u0_2797 v0_2797
    left0_2797 right0_2797
  intro b
  rw [sliceEq0_2797]
  fin_cases b
  · exact slice0_2797_0
  · exact slice0_2797_1
  · exact slice0_2797_2
  · exact slice0_2797_3
  · exact slice0_2797_4
  · exact slice0_2797_5
  · exact slice0_2797_6
  · exact slice0_2797_7
  · exact slice0_2797_8
  · exact slice0_2797_9
  · exact slice0_2797_10
  · exact slice0_2797_11
  · exact slice0_2797_12
  · exact slice0_2797_13
  · exact slice0_2797_14
  · exact slice0_2797_15
  · exact slice0_2797_16
  · exact slice0_2797_17
  · exact slice0_2797_18
  · exact slice0_2797_19
  · exact slice0_2797_20
  · exact slice0_2797_21
  · exact slice0_2797_22
  · exact slice0_2797_23
  · exact slice0_2797_24
  · exact slice0_2797_25
  · exact slice0_2797_26
  · exact slice0_2797_27
  · exact slice0_2797_28
  · exact slice0_2797_29
  · exact slice0_2797_30
  · exact slice0_2797_31
  · exact slice0_2797_32
  · exact slice0_2797_33
  · exact slice0_2797_34
  · exact slice0_2797_35
  · exact slice0_2797_36
  · exact slice0_2797_37
  · exact slice0_2797_38
  · exact slice0_2797_39
  · exact slice0_2797_40

set_option maxHeartbeats 1600000 in
public theorem point0_2798 : stepCheck 0 2798 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2799 : stepCheck 0 2799 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
