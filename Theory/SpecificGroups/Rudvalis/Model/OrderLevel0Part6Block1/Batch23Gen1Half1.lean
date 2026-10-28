module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 23, generator 1, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point1_3350 : stepCheck 1 3350 := by
  left
  decide +kernel

private def u1_3351 : List (Fin 96) := [19, 21, 12, 76]
private def v1_3351 : List (Fin 96) := [67, 69, 58, 3, 6, 11, 17, 4, 71, 59, 91, 70, 61]
private def lhs1_3351 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map76 (x))))
private def rhs1_3351 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map17 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map91 (Part6Nat.force Compressed.map70 (Part6Nat.force Compressed.map61 (x)))))))))))))
private theorem lhs1_3351_eq : lhs1_3351 = Compressed.eval u1_3351 := by rfl
private theorem rhs1_3351_eq : rhs1_3351 = Compressed.eval v1_3351 := by rfl
private def fastSlice1_3351 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3351 ((100 * b.val + x.val) % 4060) =
      rhs1_3351 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3351 (b : Fin 41) :
    Compressed.slice u1_3351 v1_3351 b = fastSlice1_3351 b := by
  simp only [Compressed.slice, fastSlice1_3351, lhs1_3351_eq, rhs1_3351_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3351 : u1_3351.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3351).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3351 : v1_3351.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3351)).map Compressed.up0 ++
      (L0Factor 1 3351).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_0 : fastSlice1_3351 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_1 : fastSlice1_3351 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_2 : fastSlice1_3351 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_3 : fastSlice1_3351 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_4 : fastSlice1_3351 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_5 : fastSlice1_3351 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_6 : fastSlice1_3351 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_7 : fastSlice1_3351 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_8 : fastSlice1_3351 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_9 : fastSlice1_3351 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_10 : fastSlice1_3351 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_11 : fastSlice1_3351 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_12 : fastSlice1_3351 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_13 : fastSlice1_3351 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_14 : fastSlice1_3351 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_15 : fastSlice1_3351 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_16 : fastSlice1_3351 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_17 : fastSlice1_3351 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_18 : fastSlice1_3351 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_19 : fastSlice1_3351 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_20 : fastSlice1_3351 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_21 : fastSlice1_3351 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_22 : fastSlice1_3351 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_23 : fastSlice1_3351 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_24 : fastSlice1_3351 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_25 : fastSlice1_3351 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_26 : fastSlice1_3351 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_27 : fastSlice1_3351 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_28 : fastSlice1_3351 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_29 : fastSlice1_3351 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_30 : fastSlice1_3351 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_31 : fastSlice1_3351 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_32 : fastSlice1_3351 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_33 : fastSlice1_3351 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_34 : fastSlice1_3351 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_35 : fastSlice1_3351 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_36 : fastSlice1_3351 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_37 : fastSlice1_3351 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_38 : fastSlice1_3351 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_39 : fastSlice1_3351 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3351_40 : fastSlice1_3351 40 = true := by
  decide +kernel

public theorem point1_3351 : stepCheck 1 3351 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3351 u1_3351 v1_3351
    left1_3351 right1_3351
  intro b
  rw [sliceEq1_3351]
  fin_cases b
  · exact slice1_3351_0
  · exact slice1_3351_1
  · exact slice1_3351_2
  · exact slice1_3351_3
  · exact slice1_3351_4
  · exact slice1_3351_5
  · exact slice1_3351_6
  · exact slice1_3351_7
  · exact slice1_3351_8
  · exact slice1_3351_9
  · exact slice1_3351_10
  · exact slice1_3351_11
  · exact slice1_3351_12
  · exact slice1_3351_13
  · exact slice1_3351_14
  · exact slice1_3351_15
  · exact slice1_3351_16
  · exact slice1_3351_17
  · exact slice1_3351_18
  · exact slice1_3351_19
  · exact slice1_3351_20
  · exact slice1_3351_21
  · exact slice1_3351_22
  · exact slice1_3351_23
  · exact slice1_3351_24
  · exact slice1_3351_25
  · exact slice1_3351_26
  · exact slice1_3351_27
  · exact slice1_3351_28
  · exact slice1_3351_29
  · exact slice1_3351_30
  · exact slice1_3351_31
  · exact slice1_3351_32
  · exact slice1_3351_33
  · exact slice1_3351_34
  · exact slice1_3351_35
  · exact slice1_3351_36
  · exact slice1_3351_37
  · exact slice1_3351_38
  · exact slice1_3351_39
  · exact slice1_3351_40

set_option maxHeartbeats 1600000 in
public theorem point1_3352 : stepCheck 1 3352 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3353 : stepCheck 1 3353 := by
  left
  decide +kernel

private def u1_3354 : List (Fin 96) := [77, 65, 19]
private def v1_3354 : List (Fin 96) := [87, 33, 69, 9, 93, 91, 32, 32, 52]
private def lhs1_3354 (x : Nat) : Nat := Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map19 (x)))
private def rhs1_3354 (x : Nat) : Nat := Part6Nat.force Compressed.map87 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map93 (Part6Nat.force Compressed.map91 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map52 (x)))))))))
private theorem lhs1_3354_eq : lhs1_3354 = Compressed.eval u1_3354 := by rfl
private theorem rhs1_3354_eq : rhs1_3354 = Compressed.eval v1_3354 := by rfl
private def fastSlice1_3354 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3354 ((100 * b.val + x.val) % 4060) =
      rhs1_3354 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3354 (b : Fin 41) :
    Compressed.slice u1_3354 v1_3354 b = fastSlice1_3354 b := by
  simp only [Compressed.slice, fastSlice1_3354, lhs1_3354_eq, rhs1_3354_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3354 : u1_3354.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3354).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3354 : v1_3354.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3354)).map Compressed.up0 ++
      (L0Factor 1 3354).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_0 : fastSlice1_3354 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_1 : fastSlice1_3354 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_2 : fastSlice1_3354 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_3 : fastSlice1_3354 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_4 : fastSlice1_3354 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_5 : fastSlice1_3354 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_6 : fastSlice1_3354 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_7 : fastSlice1_3354 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_8 : fastSlice1_3354 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_9 : fastSlice1_3354 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_10 : fastSlice1_3354 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_11 : fastSlice1_3354 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_12 : fastSlice1_3354 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_13 : fastSlice1_3354 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_14 : fastSlice1_3354 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_15 : fastSlice1_3354 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_16 : fastSlice1_3354 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_17 : fastSlice1_3354 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_18 : fastSlice1_3354 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_19 : fastSlice1_3354 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_20 : fastSlice1_3354 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_21 : fastSlice1_3354 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_22 : fastSlice1_3354 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_23 : fastSlice1_3354 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_24 : fastSlice1_3354 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_25 : fastSlice1_3354 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_26 : fastSlice1_3354 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_27 : fastSlice1_3354 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_28 : fastSlice1_3354 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_29 : fastSlice1_3354 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_30 : fastSlice1_3354 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_31 : fastSlice1_3354 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_32 : fastSlice1_3354 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_33 : fastSlice1_3354 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_34 : fastSlice1_3354 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_35 : fastSlice1_3354 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_36 : fastSlice1_3354 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_37 : fastSlice1_3354 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_38 : fastSlice1_3354 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_39 : fastSlice1_3354 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3354_40 : fastSlice1_3354 40 = true := by
  decide +kernel

public theorem point1_3354 : stepCheck 1 3354 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3354 u1_3354 v1_3354
    left1_3354 right1_3354
  intro b
  rw [sliceEq1_3354]
  fin_cases b
  · exact slice1_3354_0
  · exact slice1_3354_1
  · exact slice1_3354_2
  · exact slice1_3354_3
  · exact slice1_3354_4
  · exact slice1_3354_5
  · exact slice1_3354_6
  · exact slice1_3354_7
  · exact slice1_3354_8
  · exact slice1_3354_9
  · exact slice1_3354_10
  · exact slice1_3354_11
  · exact slice1_3354_12
  · exact slice1_3354_13
  · exact slice1_3354_14
  · exact slice1_3354_15
  · exact slice1_3354_16
  · exact slice1_3354_17
  · exact slice1_3354_18
  · exact slice1_3354_19
  · exact slice1_3354_20
  · exact slice1_3354_21
  · exact slice1_3354_22
  · exact slice1_3354_23
  · exact slice1_3354_24
  · exact slice1_3354_25
  · exact slice1_3354_26
  · exact slice1_3354_27
  · exact slice1_3354_28
  · exact slice1_3354_29
  · exact slice1_3354_30
  · exact slice1_3354_31
  · exact slice1_3354_32
  · exact slice1_3354_33
  · exact slice1_3354_34
  · exact slice1_3354_35
  · exact slice1_3354_36
  · exact slice1_3354_37
  · exact slice1_3354_38
  · exact slice1_3354_39
  · exact slice1_3354_40

set_option maxHeartbeats 1600000 in
public theorem point1_3355 : stepCheck 1 3355 := by
  left
  decide +kernel

private def u1_3356 : List (Fin 96) := [89, 65]
private def v1_3356 : List (Fin 96) := [0, 66, 65, 6, 11, 4, 36, 11, 27, 31, 45, 71, 88]
private def lhs1_3356 (x : Nat) : Nat := Part6Nat.force Compressed.map89 (Part6Nat.force Compressed.map65 (x))
private def rhs1_3356 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map88 (x)))))))))))))
private theorem lhs1_3356_eq : lhs1_3356 = Compressed.eval u1_3356 := by rfl
private theorem rhs1_3356_eq : rhs1_3356 = Compressed.eval v1_3356 := by rfl
private def fastSlice1_3356 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3356 ((100 * b.val + x.val) % 4060) =
      rhs1_3356 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3356 (b : Fin 41) :
    Compressed.slice u1_3356 v1_3356 b = fastSlice1_3356 b := by
  simp only [Compressed.slice, fastSlice1_3356, lhs1_3356_eq, rhs1_3356_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3356 : u1_3356.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3356).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3356 : v1_3356.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3356)).map Compressed.up0 ++
      (L0Factor 1 3356).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_0 : fastSlice1_3356 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_1 : fastSlice1_3356 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_2 : fastSlice1_3356 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_3 : fastSlice1_3356 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_4 : fastSlice1_3356 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_5 : fastSlice1_3356 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_6 : fastSlice1_3356 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_7 : fastSlice1_3356 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_8 : fastSlice1_3356 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_9 : fastSlice1_3356 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_10 : fastSlice1_3356 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_11 : fastSlice1_3356 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_12 : fastSlice1_3356 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_13 : fastSlice1_3356 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_14 : fastSlice1_3356 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_15 : fastSlice1_3356 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_16 : fastSlice1_3356 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_17 : fastSlice1_3356 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_18 : fastSlice1_3356 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_19 : fastSlice1_3356 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_20 : fastSlice1_3356 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_21 : fastSlice1_3356 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_22 : fastSlice1_3356 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_23 : fastSlice1_3356 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_24 : fastSlice1_3356 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_25 : fastSlice1_3356 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_26 : fastSlice1_3356 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_27 : fastSlice1_3356 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_28 : fastSlice1_3356 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_29 : fastSlice1_3356 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_30 : fastSlice1_3356 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_31 : fastSlice1_3356 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_32 : fastSlice1_3356 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_33 : fastSlice1_3356 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_34 : fastSlice1_3356 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_35 : fastSlice1_3356 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_36 : fastSlice1_3356 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_37 : fastSlice1_3356 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_38 : fastSlice1_3356 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_39 : fastSlice1_3356 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3356_40 : fastSlice1_3356 40 = true := by
  decide +kernel

public theorem point1_3356 : stepCheck 1 3356 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3356 u1_3356 v1_3356
    left1_3356 right1_3356
  intro b
  rw [sliceEq1_3356]
  fin_cases b
  · exact slice1_3356_0
  · exact slice1_3356_1
  · exact slice1_3356_2
  · exact slice1_3356_3
  · exact slice1_3356_4
  · exact slice1_3356_5
  · exact slice1_3356_6
  · exact slice1_3356_7
  · exact slice1_3356_8
  · exact slice1_3356_9
  · exact slice1_3356_10
  · exact slice1_3356_11
  · exact slice1_3356_12
  · exact slice1_3356_13
  · exact slice1_3356_14
  · exact slice1_3356_15
  · exact slice1_3356_16
  · exact slice1_3356_17
  · exact slice1_3356_18
  · exact slice1_3356_19
  · exact slice1_3356_20
  · exact slice1_3356_21
  · exact slice1_3356_22
  · exact slice1_3356_23
  · exact slice1_3356_24
  · exact slice1_3356_25
  · exact slice1_3356_26
  · exact slice1_3356_27
  · exact slice1_3356_28
  · exact slice1_3356_29
  · exact slice1_3356_30
  · exact slice1_3356_31
  · exact slice1_3356_32
  · exact slice1_3356_33
  · exact slice1_3356_34
  · exact slice1_3356_35
  · exact slice1_3356_36
  · exact slice1_3356_37
  · exact slice1_3356_38
  · exact slice1_3356_39
  · exact slice1_3356_40

set_option maxHeartbeats 1600000 in
public theorem point1_3357 : stepCheck 1 3357 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3358 : stepCheck 1 3358 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3359 : stepCheck 1 3359 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
