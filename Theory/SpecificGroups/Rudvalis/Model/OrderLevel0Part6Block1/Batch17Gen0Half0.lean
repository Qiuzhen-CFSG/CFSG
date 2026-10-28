module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 17, generator 0, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point0_2500 : stepCheck 0 2500 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2501 : stepCheck 0 2501 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2502 : stepCheck 0 2502 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2503 : stepCheck 0 2503 := by
  left
  decide +kernel

private def u0_2504 : List (Fin 96) := [0, 63, 24, 51]
private def v0_2504 : List (Fin 96) := [58, 89, 4, 20, 8, 10, 45, 71, 23, 29, 81]
private def lhs0_2504 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map51 (x))))
private def rhs0_2504 (x : Nat) : Nat := Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map89 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map20 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map81 (x)))))))))))
private theorem lhs0_2504_eq : lhs0_2504 = Compressed.eval u0_2504 := by rfl
private theorem rhs0_2504_eq : rhs0_2504 = Compressed.eval v0_2504 := by rfl
private def fastSlice0_2504 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2504 ((100 * b.val + x.val) % 4060) =
      rhs0_2504 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2504 (b : Fin 41) :
    Compressed.slice u0_2504 v0_2504 b = fastSlice0_2504 b := by
  simp only [Compressed.slice, fastSlice0_2504, lhs0_2504_eq, rhs0_2504_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2504 : u0_2504.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2504).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2504 : v0_2504.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2504)).map Compressed.up0 ++
      (L0Factor 0 2504).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_0 : fastSlice0_2504 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_1 : fastSlice0_2504 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_2 : fastSlice0_2504 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_3 : fastSlice0_2504 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_4 : fastSlice0_2504 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_5 : fastSlice0_2504 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_6 : fastSlice0_2504 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_7 : fastSlice0_2504 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_8 : fastSlice0_2504 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_9 : fastSlice0_2504 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_10 : fastSlice0_2504 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_11 : fastSlice0_2504 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_12 : fastSlice0_2504 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_13 : fastSlice0_2504 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_14 : fastSlice0_2504 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_15 : fastSlice0_2504 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_16 : fastSlice0_2504 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_17 : fastSlice0_2504 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_18 : fastSlice0_2504 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_19 : fastSlice0_2504 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_20 : fastSlice0_2504 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_21 : fastSlice0_2504 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_22 : fastSlice0_2504 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_23 : fastSlice0_2504 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_24 : fastSlice0_2504 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_25 : fastSlice0_2504 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_26 : fastSlice0_2504 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_27 : fastSlice0_2504 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_28 : fastSlice0_2504 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_29 : fastSlice0_2504 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_30 : fastSlice0_2504 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_31 : fastSlice0_2504 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_32 : fastSlice0_2504 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_33 : fastSlice0_2504 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_34 : fastSlice0_2504 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_35 : fastSlice0_2504 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_36 : fastSlice0_2504 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_37 : fastSlice0_2504 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_38 : fastSlice0_2504 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_39 : fastSlice0_2504 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2504_40 : fastSlice0_2504 40 = true := by
  decide +kernel

public theorem point0_2504 : stepCheck 0 2504 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2504 u0_2504 v0_2504
    left0_2504 right0_2504
  intro b
  rw [sliceEq0_2504]
  fin_cases b
  · exact slice0_2504_0
  · exact slice0_2504_1
  · exact slice0_2504_2
  · exact slice0_2504_3
  · exact slice0_2504_4
  · exact slice0_2504_5
  · exact slice0_2504_6
  · exact slice0_2504_7
  · exact slice0_2504_8
  · exact slice0_2504_9
  · exact slice0_2504_10
  · exact slice0_2504_11
  · exact slice0_2504_12
  · exact slice0_2504_13
  · exact slice0_2504_14
  · exact slice0_2504_15
  · exact slice0_2504_16
  · exact slice0_2504_17
  · exact slice0_2504_18
  · exact slice0_2504_19
  · exact slice0_2504_20
  · exact slice0_2504_21
  · exact slice0_2504_22
  · exact slice0_2504_23
  · exact slice0_2504_24
  · exact slice0_2504_25
  · exact slice0_2504_26
  · exact slice0_2504_27
  · exact slice0_2504_28
  · exact slice0_2504_29
  · exact slice0_2504_30
  · exact slice0_2504_31
  · exact slice0_2504_32
  · exact slice0_2504_33
  · exact slice0_2504_34
  · exact slice0_2504_35
  · exact slice0_2504_36
  · exact slice0_2504_37
  · exact slice0_2504_38
  · exact slice0_2504_39
  · exact slice0_2504_40

set_option maxHeartbeats 1600000 in
public theorem point0_2505 : stepCheck 0 2505 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2506 : stepCheck 0 2506 := by
  left
  decide +kernel

private def u0_2507 : List (Fin 96) := [90, 64, 21]
private def v0_2507 : List (Fin 96) := [50, 19, 33, 3, 9, 9, 79, 11, 15, 91, 59, 84, 70, 61]
private def lhs0_2507 (x : Nat) : Nat := Part6Nat.force Compressed.map90 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map21 (x)))
private def rhs0_2507 (x : Nat) : Nat := Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map15 (Part6Nat.force Compressed.map91 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map84 (Part6Nat.force Compressed.map70 (Part6Nat.force Compressed.map61 (x))))))))))))))
private theorem lhs0_2507_eq : lhs0_2507 = Compressed.eval u0_2507 := by rfl
private theorem rhs0_2507_eq : rhs0_2507 = Compressed.eval v0_2507 := by rfl
private def fastSlice0_2507 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2507 ((100 * b.val + x.val) % 4060) =
      rhs0_2507 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2507 (b : Fin 41) :
    Compressed.slice u0_2507 v0_2507 b = fastSlice0_2507 b := by
  simp only [Compressed.slice, fastSlice0_2507, lhs0_2507_eq, rhs0_2507_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2507 : u0_2507.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2507).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2507 : v0_2507.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2507)).map Compressed.up0 ++
      (L0Factor 0 2507).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_0 : fastSlice0_2507 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_1 : fastSlice0_2507 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_2 : fastSlice0_2507 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_3 : fastSlice0_2507 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_4 : fastSlice0_2507 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_5 : fastSlice0_2507 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_6 : fastSlice0_2507 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_7 : fastSlice0_2507 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_8 : fastSlice0_2507 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_9 : fastSlice0_2507 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_10 : fastSlice0_2507 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_11 : fastSlice0_2507 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_12 : fastSlice0_2507 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_13 : fastSlice0_2507 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_14 : fastSlice0_2507 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_15 : fastSlice0_2507 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_16 : fastSlice0_2507 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_17 : fastSlice0_2507 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_18 : fastSlice0_2507 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_19 : fastSlice0_2507 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_20 : fastSlice0_2507 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_21 : fastSlice0_2507 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_22 : fastSlice0_2507 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_23 : fastSlice0_2507 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_24 : fastSlice0_2507 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_25 : fastSlice0_2507 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_26 : fastSlice0_2507 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_27 : fastSlice0_2507 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_28 : fastSlice0_2507 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_29 : fastSlice0_2507 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_30 : fastSlice0_2507 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_31 : fastSlice0_2507 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_32 : fastSlice0_2507 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_33 : fastSlice0_2507 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_34 : fastSlice0_2507 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_35 : fastSlice0_2507 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_36 : fastSlice0_2507 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_37 : fastSlice0_2507 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_38 : fastSlice0_2507 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_39 : fastSlice0_2507 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2507_40 : fastSlice0_2507 40 = true := by
  decide +kernel

public theorem point0_2507 : stepCheck 0 2507 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2507 u0_2507 v0_2507
    left0_2507 right0_2507
  intro b
  rw [sliceEq0_2507]
  fin_cases b
  · exact slice0_2507_0
  · exact slice0_2507_1
  · exact slice0_2507_2
  · exact slice0_2507_3
  · exact slice0_2507_4
  · exact slice0_2507_5
  · exact slice0_2507_6
  · exact slice0_2507_7
  · exact slice0_2507_8
  · exact slice0_2507_9
  · exact slice0_2507_10
  · exact slice0_2507_11
  · exact slice0_2507_12
  · exact slice0_2507_13
  · exact slice0_2507_14
  · exact slice0_2507_15
  · exact slice0_2507_16
  · exact slice0_2507_17
  · exact slice0_2507_18
  · exact slice0_2507_19
  · exact slice0_2507_20
  · exact slice0_2507_21
  · exact slice0_2507_22
  · exact slice0_2507_23
  · exact slice0_2507_24
  · exact slice0_2507_25
  · exact slice0_2507_26
  · exact slice0_2507_27
  · exact slice0_2507_28
  · exact slice0_2507_29
  · exact slice0_2507_30
  · exact slice0_2507_31
  · exact slice0_2507_32
  · exact slice0_2507_33
  · exact slice0_2507_34
  · exact slice0_2507_35
  · exact slice0_2507_36
  · exact slice0_2507_37
  · exact slice0_2507_38
  · exact slice0_2507_39
  · exact slice0_2507_40

private def u0_2508 : List (Fin 96) := [67, 58, 21, 21]
private def v0_2508 : List (Fin 96) := [50, 33, 63, 20, 10, 9, 8, 94, 94, 27, 59, 85, 31, 56]
private def lhs0_2508 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map21 (x))))
private def rhs0_2508 (x : Nat) : Nat := Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map20 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map94 (Part6Nat.force Compressed.map94 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map85 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map56 (x))))))))))))))
private theorem lhs0_2508_eq : lhs0_2508 = Compressed.eval u0_2508 := by rfl
private theorem rhs0_2508_eq : rhs0_2508 = Compressed.eval v0_2508 := by rfl
private def fastSlice0_2508 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2508 ((100 * b.val + x.val) % 4060) =
      rhs0_2508 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2508 (b : Fin 41) :
    Compressed.slice u0_2508 v0_2508 b = fastSlice0_2508 b := by
  simp only [Compressed.slice, fastSlice0_2508, lhs0_2508_eq, rhs0_2508_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2508 : u0_2508.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2508).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2508 : v0_2508.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2508)).map Compressed.up0 ++
      (L0Factor 0 2508).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_0 : fastSlice0_2508 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_1 : fastSlice0_2508 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_2 : fastSlice0_2508 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_3 : fastSlice0_2508 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_4 : fastSlice0_2508 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_5 : fastSlice0_2508 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_6 : fastSlice0_2508 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_7 : fastSlice0_2508 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_8 : fastSlice0_2508 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_9 : fastSlice0_2508 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_10 : fastSlice0_2508 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_11 : fastSlice0_2508 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_12 : fastSlice0_2508 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_13 : fastSlice0_2508 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_14 : fastSlice0_2508 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_15 : fastSlice0_2508 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_16 : fastSlice0_2508 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_17 : fastSlice0_2508 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_18 : fastSlice0_2508 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_19 : fastSlice0_2508 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_20 : fastSlice0_2508 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_21 : fastSlice0_2508 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_22 : fastSlice0_2508 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_23 : fastSlice0_2508 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_24 : fastSlice0_2508 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_25 : fastSlice0_2508 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_26 : fastSlice0_2508 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_27 : fastSlice0_2508 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_28 : fastSlice0_2508 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_29 : fastSlice0_2508 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_30 : fastSlice0_2508 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_31 : fastSlice0_2508 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_32 : fastSlice0_2508 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_33 : fastSlice0_2508 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_34 : fastSlice0_2508 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_35 : fastSlice0_2508 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_36 : fastSlice0_2508 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_37 : fastSlice0_2508 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_38 : fastSlice0_2508 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_39 : fastSlice0_2508 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2508_40 : fastSlice0_2508 40 = true := by
  decide +kernel

public theorem point0_2508 : stepCheck 0 2508 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2508 u0_2508 v0_2508
    left0_2508 right0_2508
  intro b
  rw [sliceEq0_2508]
  fin_cases b
  · exact slice0_2508_0
  · exact slice0_2508_1
  · exact slice0_2508_2
  · exact slice0_2508_3
  · exact slice0_2508_4
  · exact slice0_2508_5
  · exact slice0_2508_6
  · exact slice0_2508_7
  · exact slice0_2508_8
  · exact slice0_2508_9
  · exact slice0_2508_10
  · exact slice0_2508_11
  · exact slice0_2508_12
  · exact slice0_2508_13
  · exact slice0_2508_14
  · exact slice0_2508_15
  · exact slice0_2508_16
  · exact slice0_2508_17
  · exact slice0_2508_18
  · exact slice0_2508_19
  · exact slice0_2508_20
  · exact slice0_2508_21
  · exact slice0_2508_22
  · exact slice0_2508_23
  · exact slice0_2508_24
  · exact slice0_2508_25
  · exact slice0_2508_26
  · exact slice0_2508_27
  · exact slice0_2508_28
  · exact slice0_2508_29
  · exact slice0_2508_30
  · exact slice0_2508_31
  · exact slice0_2508_32
  · exact slice0_2508_33
  · exact slice0_2508_34
  · exact slice0_2508_35
  · exact slice0_2508_36
  · exact slice0_2508_37
  · exact slice0_2508_38
  · exact slice0_2508_39
  · exact slice0_2508_40

set_option maxHeartbeats 1600000 in
public theorem point0_2509 : stepCheck 0 2509 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
