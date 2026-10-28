module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 23, generator 0, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point0_3340 : stepCheck 0 3340 := by
  left
  decide +kernel

private def u0_3341 : List (Fin 96) := [0, 50, 63, 46, 3]
private def v0_3341 : List (Fin 96) := [21, 24, 64, 60, 6, 36, 10, 11, 8, 40, 37, 25]
private def lhs0_3341 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map3 (x)))))
private def rhs0_3341 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map25 (x))))))))))))
private theorem lhs0_3341_eq : lhs0_3341 = Compressed.eval u0_3341 := by rfl
private theorem rhs0_3341_eq : rhs0_3341 = Compressed.eval v0_3341 := by rfl
private def fastSlice0_3341 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3341 ((100 * b.val + x.val) % 4060) =
      rhs0_3341 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3341 (b : Fin 41) :
    Compressed.slice u0_3341 v0_3341 b = fastSlice0_3341 b := by
  simp only [Compressed.slice, fastSlice0_3341, lhs0_3341_eq, rhs0_3341_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3341 : u0_3341.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3341).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3341 : v0_3341.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3341)).map Compressed.up0 ++
      (L0Factor 0 3341).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_0 : fastSlice0_3341 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_1 : fastSlice0_3341 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_2 : fastSlice0_3341 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_3 : fastSlice0_3341 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_4 : fastSlice0_3341 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_5 : fastSlice0_3341 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_6 : fastSlice0_3341 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_7 : fastSlice0_3341 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_8 : fastSlice0_3341 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_9 : fastSlice0_3341 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_10 : fastSlice0_3341 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_11 : fastSlice0_3341 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_12 : fastSlice0_3341 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_13 : fastSlice0_3341 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_14 : fastSlice0_3341 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_15 : fastSlice0_3341 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_16 : fastSlice0_3341 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_17 : fastSlice0_3341 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_18 : fastSlice0_3341 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_19 : fastSlice0_3341 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_20 : fastSlice0_3341 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_21 : fastSlice0_3341 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_22 : fastSlice0_3341 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_23 : fastSlice0_3341 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_24 : fastSlice0_3341 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_25 : fastSlice0_3341 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_26 : fastSlice0_3341 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_27 : fastSlice0_3341 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_28 : fastSlice0_3341 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_29 : fastSlice0_3341 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_30 : fastSlice0_3341 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_31 : fastSlice0_3341 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_32 : fastSlice0_3341 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_33 : fastSlice0_3341 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_34 : fastSlice0_3341 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_35 : fastSlice0_3341 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_36 : fastSlice0_3341 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_37 : fastSlice0_3341 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_38 : fastSlice0_3341 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_39 : fastSlice0_3341 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3341_40 : fastSlice0_3341 40 = true := by
  decide +kernel

public theorem point0_3341 : stepCheck 0 3341 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3341 u0_3341 v0_3341
    left0_3341 right0_3341
  intro b
  rw [sliceEq0_3341]
  fin_cases b
  · exact slice0_3341_0
  · exact slice0_3341_1
  · exact slice0_3341_2
  · exact slice0_3341_3
  · exact slice0_3341_4
  · exact slice0_3341_5
  · exact slice0_3341_6
  · exact slice0_3341_7
  · exact slice0_3341_8
  · exact slice0_3341_9
  · exact slice0_3341_10
  · exact slice0_3341_11
  · exact slice0_3341_12
  · exact slice0_3341_13
  · exact slice0_3341_14
  · exact slice0_3341_15
  · exact slice0_3341_16
  · exact slice0_3341_17
  · exact slice0_3341_18
  · exact slice0_3341_19
  · exact slice0_3341_20
  · exact slice0_3341_21
  · exact slice0_3341_22
  · exact slice0_3341_23
  · exact slice0_3341_24
  · exact slice0_3341_25
  · exact slice0_3341_26
  · exact slice0_3341_27
  · exact slice0_3341_28
  · exact slice0_3341_29
  · exact slice0_3341_30
  · exact slice0_3341_31
  · exact slice0_3341_32
  · exact slice0_3341_33
  · exact slice0_3341_34
  · exact slice0_3341_35
  · exact slice0_3341_36
  · exact slice0_3341_37
  · exact slice0_3341_38
  · exact slice0_3341_39
  · exact slice0_3341_40

private def u0_3342 : List (Fin 96) := [87, 63, 46, 3]
private def v0_3342 : List (Fin 96) := [19, 46, 78, 3, 4, 5, 8, 11, 23, 71, 85, 59, 62, 61]
private def lhs0_3342 (x : Nat) : Nat := Part6Nat.force Compressed.map87 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map3 (x))))
private def rhs0_3342 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map85 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map62 (Part6Nat.force Compressed.map61 (x))))))))))))))
private theorem lhs0_3342_eq : lhs0_3342 = Compressed.eval u0_3342 := by rfl
private theorem rhs0_3342_eq : rhs0_3342 = Compressed.eval v0_3342 := by rfl
private def fastSlice0_3342 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3342 ((100 * b.val + x.val) % 4060) =
      rhs0_3342 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3342 (b : Fin 41) :
    Compressed.slice u0_3342 v0_3342 b = fastSlice0_3342 b := by
  simp only [Compressed.slice, fastSlice0_3342, lhs0_3342_eq, rhs0_3342_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3342 : u0_3342.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3342).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3342 : v0_3342.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3342)).map Compressed.up0 ++
      (L0Factor 0 3342).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_0 : fastSlice0_3342 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_1 : fastSlice0_3342 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_2 : fastSlice0_3342 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_3 : fastSlice0_3342 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_4 : fastSlice0_3342 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_5 : fastSlice0_3342 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_6 : fastSlice0_3342 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_7 : fastSlice0_3342 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_8 : fastSlice0_3342 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_9 : fastSlice0_3342 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_10 : fastSlice0_3342 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_11 : fastSlice0_3342 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_12 : fastSlice0_3342 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_13 : fastSlice0_3342 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_14 : fastSlice0_3342 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_15 : fastSlice0_3342 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_16 : fastSlice0_3342 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_17 : fastSlice0_3342 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_18 : fastSlice0_3342 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_19 : fastSlice0_3342 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_20 : fastSlice0_3342 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_21 : fastSlice0_3342 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_22 : fastSlice0_3342 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_23 : fastSlice0_3342 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_24 : fastSlice0_3342 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_25 : fastSlice0_3342 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_26 : fastSlice0_3342 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_27 : fastSlice0_3342 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_28 : fastSlice0_3342 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_29 : fastSlice0_3342 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_30 : fastSlice0_3342 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_31 : fastSlice0_3342 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_32 : fastSlice0_3342 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_33 : fastSlice0_3342 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_34 : fastSlice0_3342 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_35 : fastSlice0_3342 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_36 : fastSlice0_3342 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_37 : fastSlice0_3342 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_38 : fastSlice0_3342 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_39 : fastSlice0_3342 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3342_40 : fastSlice0_3342 40 = true := by
  decide +kernel

public theorem point0_3342 : stepCheck 0 3342 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3342 u0_3342 v0_3342
    left0_3342 right0_3342
  intro b
  rw [sliceEq0_3342]
  fin_cases b
  · exact slice0_3342_0
  · exact slice0_3342_1
  · exact slice0_3342_2
  · exact slice0_3342_3
  · exact slice0_3342_4
  · exact slice0_3342_5
  · exact slice0_3342_6
  · exact slice0_3342_7
  · exact slice0_3342_8
  · exact slice0_3342_9
  · exact slice0_3342_10
  · exact slice0_3342_11
  · exact slice0_3342_12
  · exact slice0_3342_13
  · exact slice0_3342_14
  · exact slice0_3342_15
  · exact slice0_3342_16
  · exact slice0_3342_17
  · exact slice0_3342_18
  · exact slice0_3342_19
  · exact slice0_3342_20
  · exact slice0_3342_21
  · exact slice0_3342_22
  · exact slice0_3342_23
  · exact slice0_3342_24
  · exact slice0_3342_25
  · exact slice0_3342_26
  · exact slice0_3342_27
  · exact slice0_3342_28
  · exact slice0_3342_29
  · exact slice0_3342_30
  · exact slice0_3342_31
  · exact slice0_3342_32
  · exact slice0_3342_33
  · exact slice0_3342_34
  · exact slice0_3342_35
  · exact slice0_3342_36
  · exact slice0_3342_37
  · exact slice0_3342_38
  · exact slice0_3342_39
  · exact slice0_3342_40

private def u0_3343 : List (Fin 96) := [67, 19, 33, 21, 3]
private def v0_3343 : List (Fin 96) := [92, 21, 12, 60, 17, 93, 37, 45, 29, 81]
private def lhs0_3343 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map3 (x)))))
private def rhs0_3343 (x : Nat) : Nat := Part6Nat.force Compressed.map92 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map17 (Part6Nat.force Compressed.map93 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map81 (x))))))))))
private theorem lhs0_3343_eq : lhs0_3343 = Compressed.eval u0_3343 := by rfl
private theorem rhs0_3343_eq : rhs0_3343 = Compressed.eval v0_3343 := by rfl
private def fastSlice0_3343 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3343 ((100 * b.val + x.val) % 4060) =
      rhs0_3343 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3343 (b : Fin 41) :
    Compressed.slice u0_3343 v0_3343 b = fastSlice0_3343 b := by
  simp only [Compressed.slice, fastSlice0_3343, lhs0_3343_eq, rhs0_3343_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3343 : u0_3343.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3343).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3343 : v0_3343.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3343)).map Compressed.up0 ++
      (L0Factor 0 3343).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_0 : fastSlice0_3343 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_1 : fastSlice0_3343 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_2 : fastSlice0_3343 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_3 : fastSlice0_3343 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_4 : fastSlice0_3343 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_5 : fastSlice0_3343 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_6 : fastSlice0_3343 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_7 : fastSlice0_3343 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_8 : fastSlice0_3343 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_9 : fastSlice0_3343 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_10 : fastSlice0_3343 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_11 : fastSlice0_3343 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_12 : fastSlice0_3343 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_13 : fastSlice0_3343 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_14 : fastSlice0_3343 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_15 : fastSlice0_3343 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_16 : fastSlice0_3343 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_17 : fastSlice0_3343 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_18 : fastSlice0_3343 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_19 : fastSlice0_3343 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_20 : fastSlice0_3343 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_21 : fastSlice0_3343 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_22 : fastSlice0_3343 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_23 : fastSlice0_3343 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_24 : fastSlice0_3343 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_25 : fastSlice0_3343 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_26 : fastSlice0_3343 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_27 : fastSlice0_3343 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_28 : fastSlice0_3343 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_29 : fastSlice0_3343 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_30 : fastSlice0_3343 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_31 : fastSlice0_3343 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_32 : fastSlice0_3343 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_33 : fastSlice0_3343 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_34 : fastSlice0_3343 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_35 : fastSlice0_3343 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_36 : fastSlice0_3343 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_37 : fastSlice0_3343 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_38 : fastSlice0_3343 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_39 : fastSlice0_3343 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3343_40 : fastSlice0_3343 40 = true := by
  decide +kernel

public theorem point0_3343 : stepCheck 0 3343 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3343 u0_3343 v0_3343
    left0_3343 right0_3343
  intro b
  rw [sliceEq0_3343]
  fin_cases b
  · exact slice0_3343_0
  · exact slice0_3343_1
  · exact slice0_3343_2
  · exact slice0_3343_3
  · exact slice0_3343_4
  · exact slice0_3343_5
  · exact slice0_3343_6
  · exact slice0_3343_7
  · exact slice0_3343_8
  · exact slice0_3343_9
  · exact slice0_3343_10
  · exact slice0_3343_11
  · exact slice0_3343_12
  · exact slice0_3343_13
  · exact slice0_3343_14
  · exact slice0_3343_15
  · exact slice0_3343_16
  · exact slice0_3343_17
  · exact slice0_3343_18
  · exact slice0_3343_19
  · exact slice0_3343_20
  · exact slice0_3343_21
  · exact slice0_3343_22
  · exact slice0_3343_23
  · exact slice0_3343_24
  · exact slice0_3343_25
  · exact slice0_3343_26
  · exact slice0_3343_27
  · exact slice0_3343_28
  · exact slice0_3343_29
  · exact slice0_3343_30
  · exact slice0_3343_31
  · exact slice0_3343_32
  · exact slice0_3343_33
  · exact slice0_3343_34
  · exact slice0_3343_35
  · exact slice0_3343_36
  · exact slice0_3343_37
  · exact slice0_3343_38
  · exact slice0_3343_39
  · exact slice0_3343_40

set_option maxHeartbeats 1600000 in
public theorem point0_3344 : stepCheck 0 3344 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3345 : stepCheck 0 3345 := by
  left
  decide +kernel

private def u0_3346 : List (Fin 96) := [0, 58, 21, 63, 3]
private def v0_3346 : List (Fin 96) := [21, 51, 75, 4, 4, 5, 8, 36, 11, 29, 37, 45, 53, 5]
private def lhs0_3346 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map3 (x)))))
private def rhs0_3346 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map53 (Part6Nat.force Compressed.map5 (x))))))))))))))
private theorem lhs0_3346_eq : lhs0_3346 = Compressed.eval u0_3346 := by rfl
private theorem rhs0_3346_eq : rhs0_3346 = Compressed.eval v0_3346 := by rfl
private def fastSlice0_3346 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3346 ((100 * b.val + x.val) % 4060) =
      rhs0_3346 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3346 (b : Fin 41) :
    Compressed.slice u0_3346 v0_3346 b = fastSlice0_3346 b := by
  simp only [Compressed.slice, fastSlice0_3346, lhs0_3346_eq, rhs0_3346_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3346 : u0_3346.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3346).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3346 : v0_3346.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3346)).map Compressed.up0 ++
      (L0Factor 0 3346).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_0 : fastSlice0_3346 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_1 : fastSlice0_3346 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_2 : fastSlice0_3346 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_3 : fastSlice0_3346 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_4 : fastSlice0_3346 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_5 : fastSlice0_3346 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_6 : fastSlice0_3346 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_7 : fastSlice0_3346 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_8 : fastSlice0_3346 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_9 : fastSlice0_3346 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_10 : fastSlice0_3346 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_11 : fastSlice0_3346 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_12 : fastSlice0_3346 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_13 : fastSlice0_3346 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_14 : fastSlice0_3346 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_15 : fastSlice0_3346 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_16 : fastSlice0_3346 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_17 : fastSlice0_3346 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_18 : fastSlice0_3346 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_19 : fastSlice0_3346 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_20 : fastSlice0_3346 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_21 : fastSlice0_3346 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_22 : fastSlice0_3346 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_23 : fastSlice0_3346 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_24 : fastSlice0_3346 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_25 : fastSlice0_3346 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_26 : fastSlice0_3346 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_27 : fastSlice0_3346 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_28 : fastSlice0_3346 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_29 : fastSlice0_3346 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_30 : fastSlice0_3346 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_31 : fastSlice0_3346 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_32 : fastSlice0_3346 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_33 : fastSlice0_3346 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_34 : fastSlice0_3346 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_35 : fastSlice0_3346 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_36 : fastSlice0_3346 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_37 : fastSlice0_3346 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_38 : fastSlice0_3346 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_39 : fastSlice0_3346 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3346_40 : fastSlice0_3346 40 = true := by
  decide +kernel

public theorem point0_3346 : stepCheck 0 3346 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3346 u0_3346 v0_3346
    left0_3346 right0_3346
  intro b
  rw [sliceEq0_3346]
  fin_cases b
  · exact slice0_3346_0
  · exact slice0_3346_1
  · exact slice0_3346_2
  · exact slice0_3346_3
  · exact slice0_3346_4
  · exact slice0_3346_5
  · exact slice0_3346_6
  · exact slice0_3346_7
  · exact slice0_3346_8
  · exact slice0_3346_9
  · exact slice0_3346_10
  · exact slice0_3346_11
  · exact slice0_3346_12
  · exact slice0_3346_13
  · exact slice0_3346_14
  · exact slice0_3346_15
  · exact slice0_3346_16
  · exact slice0_3346_17
  · exact slice0_3346_18
  · exact slice0_3346_19
  · exact slice0_3346_20
  · exact slice0_3346_21
  · exact slice0_3346_22
  · exact slice0_3346_23
  · exact slice0_3346_24
  · exact slice0_3346_25
  · exact slice0_3346_26
  · exact slice0_3346_27
  · exact slice0_3346_28
  · exact slice0_3346_29
  · exact slice0_3346_30
  · exact slice0_3346_31
  · exact slice0_3346_32
  · exact slice0_3346_33
  · exact slice0_3346_34
  · exact slice0_3346_35
  · exact slice0_3346_36
  · exact slice0_3346_37
  · exact slice0_3346_38
  · exact slice0_3346_39
  · exact slice0_3346_40

private def u0_3347 : List (Fin 96) := [67, 64, 63, 3]
private def v0_3347 : List (Fin 96) := [58, 33, 75, 3, 6, 11, 11, 4, 29, 23, 74, 22, 47, 56]
private def lhs0_3347 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map3 (x))))
private def rhs0_3347 (x : Nat) : Nat := Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map47 (Part6Nat.force Compressed.map56 (x))))))))))))))
private theorem lhs0_3347_eq : lhs0_3347 = Compressed.eval u0_3347 := by rfl
private theorem rhs0_3347_eq : rhs0_3347 = Compressed.eval v0_3347 := by rfl
private def fastSlice0_3347 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3347 ((100 * b.val + x.val) % 4060) =
      rhs0_3347 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3347 (b : Fin 41) :
    Compressed.slice u0_3347 v0_3347 b = fastSlice0_3347 b := by
  simp only [Compressed.slice, fastSlice0_3347, lhs0_3347_eq, rhs0_3347_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3347 : u0_3347.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3347).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3347 : v0_3347.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3347)).map Compressed.up0 ++
      (L0Factor 0 3347).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_0 : fastSlice0_3347 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_1 : fastSlice0_3347 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_2 : fastSlice0_3347 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_3 : fastSlice0_3347 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_4 : fastSlice0_3347 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_5 : fastSlice0_3347 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_6 : fastSlice0_3347 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_7 : fastSlice0_3347 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_8 : fastSlice0_3347 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_9 : fastSlice0_3347 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_10 : fastSlice0_3347 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_11 : fastSlice0_3347 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_12 : fastSlice0_3347 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_13 : fastSlice0_3347 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_14 : fastSlice0_3347 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_15 : fastSlice0_3347 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_16 : fastSlice0_3347 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_17 : fastSlice0_3347 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_18 : fastSlice0_3347 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_19 : fastSlice0_3347 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_20 : fastSlice0_3347 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_21 : fastSlice0_3347 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_22 : fastSlice0_3347 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_23 : fastSlice0_3347 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_24 : fastSlice0_3347 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_25 : fastSlice0_3347 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_26 : fastSlice0_3347 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_27 : fastSlice0_3347 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_28 : fastSlice0_3347 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_29 : fastSlice0_3347 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_30 : fastSlice0_3347 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_31 : fastSlice0_3347 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_32 : fastSlice0_3347 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_33 : fastSlice0_3347 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_34 : fastSlice0_3347 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_35 : fastSlice0_3347 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_36 : fastSlice0_3347 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_37 : fastSlice0_3347 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_38 : fastSlice0_3347 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_39 : fastSlice0_3347 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3347_40 : fastSlice0_3347 40 = true := by
  decide +kernel

public theorem point0_3347 : stepCheck 0 3347 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3347 u0_3347 v0_3347
    left0_3347 right0_3347
  intro b
  rw [sliceEq0_3347]
  fin_cases b
  · exact slice0_3347_0
  · exact slice0_3347_1
  · exact slice0_3347_2
  · exact slice0_3347_3
  · exact slice0_3347_4
  · exact slice0_3347_5
  · exact slice0_3347_6
  · exact slice0_3347_7
  · exact slice0_3347_8
  · exact slice0_3347_9
  · exact slice0_3347_10
  · exact slice0_3347_11
  · exact slice0_3347_12
  · exact slice0_3347_13
  · exact slice0_3347_14
  · exact slice0_3347_15
  · exact slice0_3347_16
  · exact slice0_3347_17
  · exact slice0_3347_18
  · exact slice0_3347_19
  · exact slice0_3347_20
  · exact slice0_3347_21
  · exact slice0_3347_22
  · exact slice0_3347_23
  · exact slice0_3347_24
  · exact slice0_3347_25
  · exact slice0_3347_26
  · exact slice0_3347_27
  · exact slice0_3347_28
  · exact slice0_3347_29
  · exact slice0_3347_30
  · exact slice0_3347_31
  · exact slice0_3347_32
  · exact slice0_3347_33
  · exact slice0_3347_34
  · exact slice0_3347_35
  · exact slice0_3347_36
  · exact slice0_3347_37
  · exact slice0_3347_38
  · exact slice0_3347_39
  · exact slice0_3347_40

set_option maxHeartbeats 1600000 in
public theorem point0_3348 : stepCheck 0 3348 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3349 : stepCheck 0 3349 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
