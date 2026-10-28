module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 18, generator 1, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u1_2640 : List (Fin 96) := [12, 51, 33, 12, 3]
private def v1_2640 : List (Fin 96) := [90, 66, 50, 36, 8, 11, 44, 84, 83, 59, 22, 47]
private def lhs1_2640 (x : Nat) : Nat := Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map3 (x)))))
private def rhs1_2640 (x : Nat) : Nat := Part6Nat.force Compressed.map90 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map44 (Part6Nat.force Compressed.map84 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map47 (x))))))))))))
private theorem lhs1_2640_eq : lhs1_2640 = Compressed.eval u1_2640 := by rfl
private theorem rhs1_2640_eq : rhs1_2640 = Compressed.eval v1_2640 := by rfl
private def fastSlice1_2640 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2640 ((100 * b.val + x.val) % 4060) =
      rhs1_2640 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2640 (b : Fin 41) :
    Compressed.slice u1_2640 v1_2640 b = fastSlice1_2640 b := by
  simp only [Compressed.slice, fastSlice1_2640, lhs1_2640_eq, rhs1_2640_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2640 : u1_2640.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2640).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2640 : v1_2640.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2640)).map Compressed.up0 ++
      (L0Factor 1 2640).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_0 : fastSlice1_2640 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_1 : fastSlice1_2640 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_2 : fastSlice1_2640 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_3 : fastSlice1_2640 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_4 : fastSlice1_2640 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_5 : fastSlice1_2640 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_6 : fastSlice1_2640 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_7 : fastSlice1_2640 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_8 : fastSlice1_2640 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_9 : fastSlice1_2640 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_10 : fastSlice1_2640 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_11 : fastSlice1_2640 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_12 : fastSlice1_2640 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_13 : fastSlice1_2640 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_14 : fastSlice1_2640 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_15 : fastSlice1_2640 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_16 : fastSlice1_2640 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_17 : fastSlice1_2640 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_18 : fastSlice1_2640 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_19 : fastSlice1_2640 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_20 : fastSlice1_2640 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_21 : fastSlice1_2640 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_22 : fastSlice1_2640 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_23 : fastSlice1_2640 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_24 : fastSlice1_2640 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_25 : fastSlice1_2640 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_26 : fastSlice1_2640 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_27 : fastSlice1_2640 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_28 : fastSlice1_2640 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_29 : fastSlice1_2640 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_30 : fastSlice1_2640 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_31 : fastSlice1_2640 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_32 : fastSlice1_2640 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_33 : fastSlice1_2640 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_34 : fastSlice1_2640 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_35 : fastSlice1_2640 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_36 : fastSlice1_2640 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_37 : fastSlice1_2640 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_38 : fastSlice1_2640 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_39 : fastSlice1_2640 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2640_40 : fastSlice1_2640 40 = true := by
  decide +kernel

public theorem point1_2640 : stepCheck 1 2640 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2640 u1_2640 v1_2640
    left1_2640 right1_2640
  intro b
  rw [sliceEq1_2640]
  fin_cases b
  · exact slice1_2640_0
  · exact slice1_2640_1
  · exact slice1_2640_2
  · exact slice1_2640_3
  · exact slice1_2640_4
  · exact slice1_2640_5
  · exact slice1_2640_6
  · exact slice1_2640_7
  · exact slice1_2640_8
  · exact slice1_2640_9
  · exact slice1_2640_10
  · exact slice1_2640_11
  · exact slice1_2640_12
  · exact slice1_2640_13
  · exact slice1_2640_14
  · exact slice1_2640_15
  · exact slice1_2640_16
  · exact slice1_2640_17
  · exact slice1_2640_18
  · exact slice1_2640_19
  · exact slice1_2640_20
  · exact slice1_2640_21
  · exact slice1_2640_22
  · exact slice1_2640_23
  · exact slice1_2640_24
  · exact slice1_2640_25
  · exact slice1_2640_26
  · exact slice1_2640_27
  · exact slice1_2640_28
  · exact slice1_2640_29
  · exact slice1_2640_30
  · exact slice1_2640_31
  · exact slice1_2640_32
  · exact slice1_2640_33
  · exact slice1_2640_34
  · exact slice1_2640_35
  · exact slice1_2640_36
  · exact slice1_2640_37
  · exact slice1_2640_38
  · exact slice1_2640_39
  · exact slice1_2640_40

set_option maxHeartbeats 1600000 in
public theorem point1_2641 : stepCheck 1 2641 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2642 : stepCheck 1 2642 := by
  left
  decide +kernel

private def u1_2643 : List (Fin 96) := [78, 46, 95]
private def v1_2643 : List (Fin 96) := [90, 50, 33, 12, 6, 11, 5, 30, 4, 74, 6, 40, 23, 74, 22, 86]
private def lhs1_2643 (x : Nat) : Nat := Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map95 (x)))
private def rhs1_2643 (x : Nat) : Nat := Part6Nat.force Compressed.map90 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map30 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map86 (x))))))))))))))))
private theorem lhs1_2643_eq : lhs1_2643 = Compressed.eval u1_2643 := by rfl
private theorem rhs1_2643_eq : rhs1_2643 = Compressed.eval v1_2643 := by rfl
private def fastSlice1_2643 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2643 ((100 * b.val + x.val) % 4060) =
      rhs1_2643 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2643 (b : Fin 41) :
    Compressed.slice u1_2643 v1_2643 b = fastSlice1_2643 b := by
  simp only [Compressed.slice, fastSlice1_2643, lhs1_2643_eq, rhs1_2643_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2643 : u1_2643.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2643).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2643 : v1_2643.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2643)).map Compressed.up0 ++
      (L0Factor 1 2643).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_0 : fastSlice1_2643 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_1 : fastSlice1_2643 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_2 : fastSlice1_2643 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_3 : fastSlice1_2643 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_4 : fastSlice1_2643 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_5 : fastSlice1_2643 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_6 : fastSlice1_2643 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_7 : fastSlice1_2643 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_8 : fastSlice1_2643 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_9 : fastSlice1_2643 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_10 : fastSlice1_2643 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_11 : fastSlice1_2643 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_12 : fastSlice1_2643 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_13 : fastSlice1_2643 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_14 : fastSlice1_2643 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_15 : fastSlice1_2643 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_16 : fastSlice1_2643 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_17 : fastSlice1_2643 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_18 : fastSlice1_2643 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_19 : fastSlice1_2643 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_20 : fastSlice1_2643 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_21 : fastSlice1_2643 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_22 : fastSlice1_2643 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_23 : fastSlice1_2643 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_24 : fastSlice1_2643 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_25 : fastSlice1_2643 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_26 : fastSlice1_2643 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_27 : fastSlice1_2643 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_28 : fastSlice1_2643 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_29 : fastSlice1_2643 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_30 : fastSlice1_2643 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_31 : fastSlice1_2643 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_32 : fastSlice1_2643 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_33 : fastSlice1_2643 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_34 : fastSlice1_2643 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_35 : fastSlice1_2643 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_36 : fastSlice1_2643 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_37 : fastSlice1_2643 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_38 : fastSlice1_2643 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_39 : fastSlice1_2643 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2643_40 : fastSlice1_2643 40 = true := by
  decide +kernel

public theorem point1_2643 : stepCheck 1 2643 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2643 u1_2643 v1_2643
    left1_2643 right1_2643
  intro b
  rw [sliceEq1_2643]
  fin_cases b
  · exact slice1_2643_0
  · exact slice1_2643_1
  · exact slice1_2643_2
  · exact slice1_2643_3
  · exact slice1_2643_4
  · exact slice1_2643_5
  · exact slice1_2643_6
  · exact slice1_2643_7
  · exact slice1_2643_8
  · exact slice1_2643_9
  · exact slice1_2643_10
  · exact slice1_2643_11
  · exact slice1_2643_12
  · exact slice1_2643_13
  · exact slice1_2643_14
  · exact slice1_2643_15
  · exact slice1_2643_16
  · exact slice1_2643_17
  · exact slice1_2643_18
  · exact slice1_2643_19
  · exact slice1_2643_20
  · exact slice1_2643_21
  · exact slice1_2643_22
  · exact slice1_2643_23
  · exact slice1_2643_24
  · exact slice1_2643_25
  · exact slice1_2643_26
  · exact slice1_2643_27
  · exact slice1_2643_28
  · exact slice1_2643_29
  · exact slice1_2643_30
  · exact slice1_2643_31
  · exact slice1_2643_32
  · exact slice1_2643_33
  · exact slice1_2643_34
  · exact slice1_2643_35
  · exact slice1_2643_36
  · exact slice1_2643_37
  · exact slice1_2643_38
  · exact slice1_2643_39
  · exact slice1_2643_40

set_option maxHeartbeats 1600000 in
public theorem point1_2644 : stepCheck 1 2644 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2645 : stepCheck 1 2645 := by
  left
  decide +kernel

private def u1_2646 : List (Fin 96) := [63, 46, 95]
private def v1_2646 : List (Fin 96) := [0, 58, 69, 24, 10, 9, 20, 93, 32, 37, 25, 61]
private def lhs1_2646 (x : Nat) : Nat := Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map95 (x)))
private def rhs1_2646 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map20 (Part6Nat.force Compressed.map93 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map61 (x))))))))))))
private theorem lhs1_2646_eq : lhs1_2646 = Compressed.eval u1_2646 := by rfl
private theorem rhs1_2646_eq : rhs1_2646 = Compressed.eval v1_2646 := by rfl
private def fastSlice1_2646 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2646 ((100 * b.val + x.val) % 4060) =
      rhs1_2646 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2646 (b : Fin 41) :
    Compressed.slice u1_2646 v1_2646 b = fastSlice1_2646 b := by
  simp only [Compressed.slice, fastSlice1_2646, lhs1_2646_eq, rhs1_2646_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2646 : u1_2646.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2646).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2646 : v1_2646.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2646)).map Compressed.up0 ++
      (L0Factor 1 2646).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_0 : fastSlice1_2646 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_1 : fastSlice1_2646 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_2 : fastSlice1_2646 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_3 : fastSlice1_2646 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_4 : fastSlice1_2646 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_5 : fastSlice1_2646 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_6 : fastSlice1_2646 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_7 : fastSlice1_2646 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_8 : fastSlice1_2646 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_9 : fastSlice1_2646 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_10 : fastSlice1_2646 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_11 : fastSlice1_2646 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_12 : fastSlice1_2646 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_13 : fastSlice1_2646 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_14 : fastSlice1_2646 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_15 : fastSlice1_2646 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_16 : fastSlice1_2646 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_17 : fastSlice1_2646 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_18 : fastSlice1_2646 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_19 : fastSlice1_2646 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_20 : fastSlice1_2646 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_21 : fastSlice1_2646 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_22 : fastSlice1_2646 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_23 : fastSlice1_2646 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_24 : fastSlice1_2646 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_25 : fastSlice1_2646 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_26 : fastSlice1_2646 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_27 : fastSlice1_2646 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_28 : fastSlice1_2646 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_29 : fastSlice1_2646 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_30 : fastSlice1_2646 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_31 : fastSlice1_2646 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_32 : fastSlice1_2646 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_33 : fastSlice1_2646 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_34 : fastSlice1_2646 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_35 : fastSlice1_2646 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_36 : fastSlice1_2646 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_37 : fastSlice1_2646 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_38 : fastSlice1_2646 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_39 : fastSlice1_2646 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2646_40 : fastSlice1_2646 40 = true := by
  decide +kernel

public theorem point1_2646 : stepCheck 1 2646 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2646 u1_2646 v1_2646
    left1_2646 right1_2646
  intro b
  rw [sliceEq1_2646]
  fin_cases b
  · exact slice1_2646_0
  · exact slice1_2646_1
  · exact slice1_2646_2
  · exact slice1_2646_3
  · exact slice1_2646_4
  · exact slice1_2646_5
  · exact slice1_2646_6
  · exact slice1_2646_7
  · exact slice1_2646_8
  · exact slice1_2646_9
  · exact slice1_2646_10
  · exact slice1_2646_11
  · exact slice1_2646_12
  · exact slice1_2646_13
  · exact slice1_2646_14
  · exact slice1_2646_15
  · exact slice1_2646_16
  · exact slice1_2646_17
  · exact slice1_2646_18
  · exact slice1_2646_19
  · exact slice1_2646_20
  · exact slice1_2646_21
  · exact slice1_2646_22
  · exact slice1_2646_23
  · exact slice1_2646_24
  · exact slice1_2646_25
  · exact slice1_2646_26
  · exact slice1_2646_27
  · exact slice1_2646_28
  · exact slice1_2646_29
  · exact slice1_2646_30
  · exact slice1_2646_31
  · exact slice1_2646_32
  · exact slice1_2646_33
  · exact slice1_2646_34
  · exact slice1_2646_35
  · exact slice1_2646_36
  · exact slice1_2646_37
  · exact slice1_2646_38
  · exact slice1_2646_39
  · exact slice1_2646_40

private def u1_2647 : List (Fin 96) := [66, 21, 95]
private def v1_2647 : List (Fin 96) := [14, 24, 46, 63, 4, 13, 44, 91, 23, 71, 70, 61]
private def lhs1_2647 (x : Nat) : Nat := Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map95 (x)))
private def rhs1_2647 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map44 (Part6Nat.force Compressed.map91 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map70 (Part6Nat.force Compressed.map61 (x))))))))))))
private theorem lhs1_2647_eq : lhs1_2647 = Compressed.eval u1_2647 := by rfl
private theorem rhs1_2647_eq : rhs1_2647 = Compressed.eval v1_2647 := by rfl
private def fastSlice1_2647 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2647 ((100 * b.val + x.val) % 4060) =
      rhs1_2647 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2647 (b : Fin 41) :
    Compressed.slice u1_2647 v1_2647 b = fastSlice1_2647 b := by
  simp only [Compressed.slice, fastSlice1_2647, lhs1_2647_eq, rhs1_2647_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2647 : u1_2647.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2647).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2647 : v1_2647.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2647)).map Compressed.up0 ++
      (L0Factor 1 2647).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_0 : fastSlice1_2647 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_1 : fastSlice1_2647 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_2 : fastSlice1_2647 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_3 : fastSlice1_2647 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_4 : fastSlice1_2647 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_5 : fastSlice1_2647 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_6 : fastSlice1_2647 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_7 : fastSlice1_2647 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_8 : fastSlice1_2647 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_9 : fastSlice1_2647 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_10 : fastSlice1_2647 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_11 : fastSlice1_2647 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_12 : fastSlice1_2647 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_13 : fastSlice1_2647 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_14 : fastSlice1_2647 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_15 : fastSlice1_2647 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_16 : fastSlice1_2647 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_17 : fastSlice1_2647 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_18 : fastSlice1_2647 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_19 : fastSlice1_2647 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_20 : fastSlice1_2647 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_21 : fastSlice1_2647 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_22 : fastSlice1_2647 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_23 : fastSlice1_2647 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_24 : fastSlice1_2647 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_25 : fastSlice1_2647 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_26 : fastSlice1_2647 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_27 : fastSlice1_2647 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_28 : fastSlice1_2647 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_29 : fastSlice1_2647 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_30 : fastSlice1_2647 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_31 : fastSlice1_2647 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_32 : fastSlice1_2647 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_33 : fastSlice1_2647 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_34 : fastSlice1_2647 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_35 : fastSlice1_2647 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_36 : fastSlice1_2647 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_37 : fastSlice1_2647 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_38 : fastSlice1_2647 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_39 : fastSlice1_2647 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2647_40 : fastSlice1_2647 40 = true := by
  decide +kernel

public theorem point1_2647 : stepCheck 1 2647 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2647 u1_2647 v1_2647
    left1_2647 right1_2647
  intro b
  rw [sliceEq1_2647]
  fin_cases b
  · exact slice1_2647_0
  · exact slice1_2647_1
  · exact slice1_2647_2
  · exact slice1_2647_3
  · exact slice1_2647_4
  · exact slice1_2647_5
  · exact slice1_2647_6
  · exact slice1_2647_7
  · exact slice1_2647_8
  · exact slice1_2647_9
  · exact slice1_2647_10
  · exact slice1_2647_11
  · exact slice1_2647_12
  · exact slice1_2647_13
  · exact slice1_2647_14
  · exact slice1_2647_15
  · exact slice1_2647_16
  · exact slice1_2647_17
  · exact slice1_2647_18
  · exact slice1_2647_19
  · exact slice1_2647_20
  · exact slice1_2647_21
  · exact slice1_2647_22
  · exact slice1_2647_23
  · exact slice1_2647_24
  · exact slice1_2647_25
  · exact slice1_2647_26
  · exact slice1_2647_27
  · exact slice1_2647_28
  · exact slice1_2647_29
  · exact slice1_2647_30
  · exact slice1_2647_31
  · exact slice1_2647_32
  · exact slice1_2647_33
  · exact slice1_2647_34
  · exact slice1_2647_35
  · exact slice1_2647_36
  · exact slice1_2647_37
  · exact slice1_2647_38
  · exact slice1_2647_39
  · exact slice1_2647_40

set_option maxHeartbeats 1600000 in
public theorem point1_2648 : stepCheck 1 2648 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2649 : stepCheck 1 2649 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
