module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 21, generator 0, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u0_3060 : List (Fin 96) := [0, 58, 64, 50]
private def v0_3060 : List (Fin 96) := [51, 12, 76, 6, 36, 4, 44, 59, 18, 59, 62]
private def lhs0_3060 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map50 (x))))
private def rhs0_3060 (x : Nat) : Nat := Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map76 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map44 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map62 (x)))))))))))
private theorem lhs0_3060_eq : lhs0_3060 = Compressed.eval u0_3060 := by rfl
private theorem rhs0_3060_eq : rhs0_3060 = Compressed.eval v0_3060 := by rfl
private def fastSlice0_3060 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3060 ((100 * b.val + x.val) % 4060) =
      rhs0_3060 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3060 (b : Fin 41) :
    Compressed.slice u0_3060 v0_3060 b = fastSlice0_3060 b := by
  simp only [Compressed.slice, fastSlice0_3060, lhs0_3060_eq, rhs0_3060_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3060 : u0_3060.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3060).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3060 : v0_3060.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3060)).map Compressed.up0 ++
      (L0Factor 0 3060).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_0 : fastSlice0_3060 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_1 : fastSlice0_3060 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_2 : fastSlice0_3060 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_3 : fastSlice0_3060 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_4 : fastSlice0_3060 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_5 : fastSlice0_3060 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_6 : fastSlice0_3060 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_7 : fastSlice0_3060 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_8 : fastSlice0_3060 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_9 : fastSlice0_3060 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_10 : fastSlice0_3060 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_11 : fastSlice0_3060 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_12 : fastSlice0_3060 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_13 : fastSlice0_3060 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_14 : fastSlice0_3060 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_15 : fastSlice0_3060 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_16 : fastSlice0_3060 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_17 : fastSlice0_3060 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_18 : fastSlice0_3060 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_19 : fastSlice0_3060 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_20 : fastSlice0_3060 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_21 : fastSlice0_3060 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_22 : fastSlice0_3060 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_23 : fastSlice0_3060 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_24 : fastSlice0_3060 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_25 : fastSlice0_3060 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_26 : fastSlice0_3060 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_27 : fastSlice0_3060 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_28 : fastSlice0_3060 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_29 : fastSlice0_3060 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_30 : fastSlice0_3060 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_31 : fastSlice0_3060 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_32 : fastSlice0_3060 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_33 : fastSlice0_3060 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_34 : fastSlice0_3060 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_35 : fastSlice0_3060 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_36 : fastSlice0_3060 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_37 : fastSlice0_3060 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_38 : fastSlice0_3060 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_39 : fastSlice0_3060 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3060_40 : fastSlice0_3060 40 = true := by
  decide +kernel

public theorem point0_3060 : stepCheck 0 3060 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3060 u0_3060 v0_3060
    left0_3060 right0_3060
  intro b
  rw [sliceEq0_3060]
  fin_cases b
  · exact slice0_3060_0
  · exact slice0_3060_1
  · exact slice0_3060_2
  · exact slice0_3060_3
  · exact slice0_3060_4
  · exact slice0_3060_5
  · exact slice0_3060_6
  · exact slice0_3060_7
  · exact slice0_3060_8
  · exact slice0_3060_9
  · exact slice0_3060_10
  · exact slice0_3060_11
  · exact slice0_3060_12
  · exact slice0_3060_13
  · exact slice0_3060_14
  · exact slice0_3060_15
  · exact slice0_3060_16
  · exact slice0_3060_17
  · exact slice0_3060_18
  · exact slice0_3060_19
  · exact slice0_3060_20
  · exact slice0_3060_21
  · exact slice0_3060_22
  · exact slice0_3060_23
  · exact slice0_3060_24
  · exact slice0_3060_25
  · exact slice0_3060_26
  · exact slice0_3060_27
  · exact slice0_3060_28
  · exact slice0_3060_29
  · exact slice0_3060_30
  · exact slice0_3060_31
  · exact slice0_3060_32
  · exact slice0_3060_33
  · exact slice0_3060_34
  · exact slice0_3060_35
  · exact slice0_3060_36
  · exact slice0_3060_37
  · exact slice0_3060_38
  · exact slice0_3060_39
  · exact slice0_3060_40

private def u0_3061 : List (Fin 96) := [67, 24, 64, 50]
private def v0_3061 : List (Fin 96) := [78, 51, 19, 10, 10, 9, 13, 47, 25, 71, 88]
private def lhs0_3061 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map50 (x))))
private def rhs0_3061 (x : Nat) : Nat := Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map47 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map88 (x)))))))))))
private theorem lhs0_3061_eq : lhs0_3061 = Compressed.eval u0_3061 := by rfl
private theorem rhs0_3061_eq : rhs0_3061 = Compressed.eval v0_3061 := by rfl
private def fastSlice0_3061 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3061 ((100 * b.val + x.val) % 4060) =
      rhs0_3061 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3061 (b : Fin 41) :
    Compressed.slice u0_3061 v0_3061 b = fastSlice0_3061 b := by
  simp only [Compressed.slice, fastSlice0_3061, lhs0_3061_eq, rhs0_3061_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3061 : u0_3061.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3061).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3061 : v0_3061.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3061)).map Compressed.up0 ++
      (L0Factor 0 3061).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_0 : fastSlice0_3061 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_1 : fastSlice0_3061 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_2 : fastSlice0_3061 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_3 : fastSlice0_3061 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_4 : fastSlice0_3061 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_5 : fastSlice0_3061 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_6 : fastSlice0_3061 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_7 : fastSlice0_3061 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_8 : fastSlice0_3061 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_9 : fastSlice0_3061 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_10 : fastSlice0_3061 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_11 : fastSlice0_3061 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_12 : fastSlice0_3061 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_13 : fastSlice0_3061 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_14 : fastSlice0_3061 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_15 : fastSlice0_3061 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_16 : fastSlice0_3061 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_17 : fastSlice0_3061 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_18 : fastSlice0_3061 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_19 : fastSlice0_3061 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_20 : fastSlice0_3061 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_21 : fastSlice0_3061 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_22 : fastSlice0_3061 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_23 : fastSlice0_3061 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_24 : fastSlice0_3061 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_25 : fastSlice0_3061 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_26 : fastSlice0_3061 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_27 : fastSlice0_3061 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_28 : fastSlice0_3061 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_29 : fastSlice0_3061 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_30 : fastSlice0_3061 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_31 : fastSlice0_3061 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_32 : fastSlice0_3061 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_33 : fastSlice0_3061 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_34 : fastSlice0_3061 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_35 : fastSlice0_3061 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_36 : fastSlice0_3061 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_37 : fastSlice0_3061 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_38 : fastSlice0_3061 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_39 : fastSlice0_3061 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3061_40 : fastSlice0_3061 40 = true := by
  decide +kernel

public theorem point0_3061 : stepCheck 0 3061 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3061 u0_3061 v0_3061
    left0_3061 right0_3061
  intro b
  rw [sliceEq0_3061]
  fin_cases b
  · exact slice0_3061_0
  · exact slice0_3061_1
  · exact slice0_3061_2
  · exact slice0_3061_3
  · exact slice0_3061_4
  · exact slice0_3061_5
  · exact slice0_3061_6
  · exact slice0_3061_7
  · exact slice0_3061_8
  · exact slice0_3061_9
  · exact slice0_3061_10
  · exact slice0_3061_11
  · exact slice0_3061_12
  · exact slice0_3061_13
  · exact slice0_3061_14
  · exact slice0_3061_15
  · exact slice0_3061_16
  · exact slice0_3061_17
  · exact slice0_3061_18
  · exact slice0_3061_19
  · exact slice0_3061_20
  · exact slice0_3061_21
  · exact slice0_3061_22
  · exact slice0_3061_23
  · exact slice0_3061_24
  · exact slice0_3061_25
  · exact slice0_3061_26
  · exact slice0_3061_27
  · exact slice0_3061_28
  · exact slice0_3061_29
  · exact slice0_3061_30
  · exact slice0_3061_31
  · exact slice0_3061_32
  · exact slice0_3061_33
  · exact slice0_3061_34
  · exact slice0_3061_35
  · exact slice0_3061_36
  · exact slice0_3061_37
  · exact slice0_3061_38
  · exact slice0_3061_39
  · exact slice0_3061_40

set_option maxHeartbeats 1600000 in
public theorem point0_3062 : stepCheck 0 3062 := by
  left
  decide +kernel

private def u0_3063 : List (Fin 96) := [0, 78, 51, 50]
private def v0_3063 : List (Fin 96) := [14, 82, 58, 3, 68, 20, 4, 45, 8, 40, 81, 56]
private def lhs0_3063 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map50 (x))))
private def rhs0_3063 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map68 (Part6Nat.force Compressed.map20 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map81 (Part6Nat.force Compressed.map56 (x))))))))))))
private theorem lhs0_3063_eq : lhs0_3063 = Compressed.eval u0_3063 := by rfl
private theorem rhs0_3063_eq : rhs0_3063 = Compressed.eval v0_3063 := by rfl
private def fastSlice0_3063 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3063 ((100 * b.val + x.val) % 4060) =
      rhs0_3063 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3063 (b : Fin 41) :
    Compressed.slice u0_3063 v0_3063 b = fastSlice0_3063 b := by
  simp only [Compressed.slice, fastSlice0_3063, lhs0_3063_eq, rhs0_3063_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3063 : u0_3063.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3063).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3063 : v0_3063.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3063)).map Compressed.up0 ++
      (L0Factor 0 3063).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_0 : fastSlice0_3063 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_1 : fastSlice0_3063 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_2 : fastSlice0_3063 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_3 : fastSlice0_3063 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_4 : fastSlice0_3063 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_5 : fastSlice0_3063 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_6 : fastSlice0_3063 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_7 : fastSlice0_3063 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_8 : fastSlice0_3063 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_9 : fastSlice0_3063 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_10 : fastSlice0_3063 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_11 : fastSlice0_3063 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_12 : fastSlice0_3063 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_13 : fastSlice0_3063 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_14 : fastSlice0_3063 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_15 : fastSlice0_3063 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_16 : fastSlice0_3063 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_17 : fastSlice0_3063 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_18 : fastSlice0_3063 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_19 : fastSlice0_3063 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_20 : fastSlice0_3063 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_21 : fastSlice0_3063 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_22 : fastSlice0_3063 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_23 : fastSlice0_3063 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_24 : fastSlice0_3063 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_25 : fastSlice0_3063 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_26 : fastSlice0_3063 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_27 : fastSlice0_3063 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_28 : fastSlice0_3063 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_29 : fastSlice0_3063 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_30 : fastSlice0_3063 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_31 : fastSlice0_3063 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_32 : fastSlice0_3063 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_33 : fastSlice0_3063 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_34 : fastSlice0_3063 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_35 : fastSlice0_3063 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_36 : fastSlice0_3063 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_37 : fastSlice0_3063 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_38 : fastSlice0_3063 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_39 : fastSlice0_3063 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3063_40 : fastSlice0_3063 40 = true := by
  decide +kernel

public theorem point0_3063 : stepCheck 0 3063 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3063 u0_3063 v0_3063
    left0_3063 right0_3063
  intro b
  rw [sliceEq0_3063]
  fin_cases b
  · exact slice0_3063_0
  · exact slice0_3063_1
  · exact slice0_3063_2
  · exact slice0_3063_3
  · exact slice0_3063_4
  · exact slice0_3063_5
  · exact slice0_3063_6
  · exact slice0_3063_7
  · exact slice0_3063_8
  · exact slice0_3063_9
  · exact slice0_3063_10
  · exact slice0_3063_11
  · exact slice0_3063_12
  · exact slice0_3063_13
  · exact slice0_3063_14
  · exact slice0_3063_15
  · exact slice0_3063_16
  · exact slice0_3063_17
  · exact slice0_3063_18
  · exact slice0_3063_19
  · exact slice0_3063_20
  · exact slice0_3063_21
  · exact slice0_3063_22
  · exact slice0_3063_23
  · exact slice0_3063_24
  · exact slice0_3063_25
  · exact slice0_3063_26
  · exact slice0_3063_27
  · exact slice0_3063_28
  · exact slice0_3063_29
  · exact slice0_3063_30
  · exact slice0_3063_31
  · exact slice0_3063_32
  · exact slice0_3063_33
  · exact slice0_3063_34
  · exact slice0_3063_35
  · exact slice0_3063_36
  · exact slice0_3063_37
  · exact slice0_3063_38
  · exact slice0_3063_39
  · exact slice0_3063_40

private def u0_3064 : List (Fin 96) := [67, 19, 51, 50]
private def v0_3064 : List (Fin 96) := [12, 46, 24, 69, 6, 10, 5, 8, 80, 29, 59, 84, 83, 41, 32, 52]
private def lhs0_3064 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map50 (x))))
private def rhs0_3064 (x : Nat) : Nat := Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map84 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map41 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map52 (x))))))))))))))))
private theorem lhs0_3064_eq : lhs0_3064 = Compressed.eval u0_3064 := by rfl
private theorem rhs0_3064_eq : rhs0_3064 = Compressed.eval v0_3064 := by rfl
private def fastSlice0_3064 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3064 ((100 * b.val + x.val) % 4060) =
      rhs0_3064 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3064 (b : Fin 41) :
    Compressed.slice u0_3064 v0_3064 b = fastSlice0_3064 b := by
  simp only [Compressed.slice, fastSlice0_3064, lhs0_3064_eq, rhs0_3064_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3064 : u0_3064.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3064).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3064 : v0_3064.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3064)).map Compressed.up0 ++
      (L0Factor 0 3064).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_0 : fastSlice0_3064 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_1 : fastSlice0_3064 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_2 : fastSlice0_3064 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_3 : fastSlice0_3064 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_4 : fastSlice0_3064 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_5 : fastSlice0_3064 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_6 : fastSlice0_3064 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_7 : fastSlice0_3064 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_8 : fastSlice0_3064 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_9 : fastSlice0_3064 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_10 : fastSlice0_3064 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_11 : fastSlice0_3064 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_12 : fastSlice0_3064 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_13 : fastSlice0_3064 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_14 : fastSlice0_3064 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_15 : fastSlice0_3064 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_16 : fastSlice0_3064 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_17 : fastSlice0_3064 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_18 : fastSlice0_3064 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_19 : fastSlice0_3064 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_20 : fastSlice0_3064 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_21 : fastSlice0_3064 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_22 : fastSlice0_3064 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_23 : fastSlice0_3064 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_24 : fastSlice0_3064 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_25 : fastSlice0_3064 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_26 : fastSlice0_3064 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_27 : fastSlice0_3064 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_28 : fastSlice0_3064 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_29 : fastSlice0_3064 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_30 : fastSlice0_3064 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_31 : fastSlice0_3064 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_32 : fastSlice0_3064 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_33 : fastSlice0_3064 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_34 : fastSlice0_3064 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_35 : fastSlice0_3064 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_36 : fastSlice0_3064 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_37 : fastSlice0_3064 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_38 : fastSlice0_3064 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_39 : fastSlice0_3064 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3064_40 : fastSlice0_3064 40 = true := by
  decide +kernel

public theorem point0_3064 : stepCheck 0 3064 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3064 u0_3064 v0_3064
    left0_3064 right0_3064
  intro b
  rw [sliceEq0_3064]
  fin_cases b
  · exact slice0_3064_0
  · exact slice0_3064_1
  · exact slice0_3064_2
  · exact slice0_3064_3
  · exact slice0_3064_4
  · exact slice0_3064_5
  · exact slice0_3064_6
  · exact slice0_3064_7
  · exact slice0_3064_8
  · exact slice0_3064_9
  · exact slice0_3064_10
  · exact slice0_3064_11
  · exact slice0_3064_12
  · exact slice0_3064_13
  · exact slice0_3064_14
  · exact slice0_3064_15
  · exact slice0_3064_16
  · exact slice0_3064_17
  · exact slice0_3064_18
  · exact slice0_3064_19
  · exact slice0_3064_20
  · exact slice0_3064_21
  · exact slice0_3064_22
  · exact slice0_3064_23
  · exact slice0_3064_24
  · exact slice0_3064_25
  · exact slice0_3064_26
  · exact slice0_3064_27
  · exact slice0_3064_28
  · exact slice0_3064_29
  · exact slice0_3064_30
  · exact slice0_3064_31
  · exact slice0_3064_32
  · exact slice0_3064_33
  · exact slice0_3064_34
  · exact slice0_3064_35
  · exact slice0_3064_36
  · exact slice0_3064_37
  · exact slice0_3064_38
  · exact slice0_3064_39
  · exact slice0_3064_40

set_option maxHeartbeats 1600000 in
public theorem point0_3065 : stepCheck 0 3065 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3066 : stepCheck 0 3066 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3067 : stepCheck 0 3067 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3068 : stepCheck 0 3068 := by
  left
  decide +kernel

private def u0_3069 : List (Fin 96) := [0, 46, 78, 46]
private def v0_3069 : List (Fin 96) := [24, 51, 33, 60, 4, 8, 5, 13, 15, 91, 83, 37, 61]
private def lhs0_3069 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map46 (x))))
private def rhs0_3069 (x : Nat) : Nat := Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map15 (Part6Nat.force Compressed.map91 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map61 (x)))))))))))))
private theorem lhs0_3069_eq : lhs0_3069 = Compressed.eval u0_3069 := by rfl
private theorem rhs0_3069_eq : rhs0_3069 = Compressed.eval v0_3069 := by rfl
private def fastSlice0_3069 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3069 ((100 * b.val + x.val) % 4060) =
      rhs0_3069 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3069 (b : Fin 41) :
    Compressed.slice u0_3069 v0_3069 b = fastSlice0_3069 b := by
  simp only [Compressed.slice, fastSlice0_3069, lhs0_3069_eq, rhs0_3069_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3069 : u0_3069.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3069).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3069 : v0_3069.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3069)).map Compressed.up0 ++
      (L0Factor 0 3069).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_0 : fastSlice0_3069 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_1 : fastSlice0_3069 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_2 : fastSlice0_3069 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_3 : fastSlice0_3069 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_4 : fastSlice0_3069 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_5 : fastSlice0_3069 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_6 : fastSlice0_3069 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_7 : fastSlice0_3069 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_8 : fastSlice0_3069 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_9 : fastSlice0_3069 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_10 : fastSlice0_3069 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_11 : fastSlice0_3069 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_12 : fastSlice0_3069 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_13 : fastSlice0_3069 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_14 : fastSlice0_3069 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_15 : fastSlice0_3069 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_16 : fastSlice0_3069 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_17 : fastSlice0_3069 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_18 : fastSlice0_3069 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_19 : fastSlice0_3069 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_20 : fastSlice0_3069 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_21 : fastSlice0_3069 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_22 : fastSlice0_3069 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_23 : fastSlice0_3069 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_24 : fastSlice0_3069 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_25 : fastSlice0_3069 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_26 : fastSlice0_3069 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_27 : fastSlice0_3069 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_28 : fastSlice0_3069 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_29 : fastSlice0_3069 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_30 : fastSlice0_3069 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_31 : fastSlice0_3069 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_32 : fastSlice0_3069 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_33 : fastSlice0_3069 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_34 : fastSlice0_3069 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_35 : fastSlice0_3069 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_36 : fastSlice0_3069 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_37 : fastSlice0_3069 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_38 : fastSlice0_3069 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_39 : fastSlice0_3069 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3069_40 : fastSlice0_3069 40 = true := by
  decide +kernel

public theorem point0_3069 : stepCheck 0 3069 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3069 u0_3069 v0_3069
    left0_3069 right0_3069
  intro b
  rw [sliceEq0_3069]
  fin_cases b
  · exact slice0_3069_0
  · exact slice0_3069_1
  · exact slice0_3069_2
  · exact slice0_3069_3
  · exact slice0_3069_4
  · exact slice0_3069_5
  · exact slice0_3069_6
  · exact slice0_3069_7
  · exact slice0_3069_8
  · exact slice0_3069_9
  · exact slice0_3069_10
  · exact slice0_3069_11
  · exact slice0_3069_12
  · exact slice0_3069_13
  · exact slice0_3069_14
  · exact slice0_3069_15
  · exact slice0_3069_16
  · exact slice0_3069_17
  · exact slice0_3069_18
  · exact slice0_3069_19
  · exact slice0_3069_20
  · exact slice0_3069_21
  · exact slice0_3069_22
  · exact slice0_3069_23
  · exact slice0_3069_24
  · exact slice0_3069_25
  · exact slice0_3069_26
  · exact slice0_3069_27
  · exact slice0_3069_28
  · exact slice0_3069_29
  · exact slice0_3069_30
  · exact slice0_3069_31
  · exact slice0_3069_32
  · exact slice0_3069_33
  · exact slice0_3069_34
  · exact slice0_3069_35
  · exact slice0_3069_36
  · exact slice0_3069_37
  · exact slice0_3069_38
  · exact slice0_3069_39
  · exact slice0_3069_40

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
