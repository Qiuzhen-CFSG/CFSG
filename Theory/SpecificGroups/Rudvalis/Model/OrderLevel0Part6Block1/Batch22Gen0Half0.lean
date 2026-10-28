module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 22, generator 0, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point0_3200 : stepCheck 0 3200 := by
  left
  decide +kernel

private def u0_3201 : List (Fin 96) := [67, 82, 21, 60]
private def v0_3201 : List (Fin 96) := [21, 12, 46, 58, 11, 10, 11, 5, 44, 42, 40, 83, 41, 32, 52, 56]
private def lhs0_3201 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map60 (x))))
private def rhs0_3201 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map44 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map41 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map52 (Part6Nat.force Compressed.map56 (x))))))))))))))))
private theorem lhs0_3201_eq : lhs0_3201 = Compressed.eval u0_3201 := by rfl
private theorem rhs0_3201_eq : rhs0_3201 = Compressed.eval v0_3201 := by rfl
private def fastSlice0_3201 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3201 ((100 * b.val + x.val) % 4060) =
      rhs0_3201 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3201 (b : Fin 41) :
    Compressed.slice u0_3201 v0_3201 b = fastSlice0_3201 b := by
  simp only [Compressed.slice, fastSlice0_3201, lhs0_3201_eq, rhs0_3201_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3201 : u0_3201.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3201).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3201 : v0_3201.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3201)).map Compressed.up0 ++
      (L0Factor 0 3201).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_0 : fastSlice0_3201 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_1 : fastSlice0_3201 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_2 : fastSlice0_3201 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_3 : fastSlice0_3201 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_4 : fastSlice0_3201 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_5 : fastSlice0_3201 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_6 : fastSlice0_3201 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_7 : fastSlice0_3201 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_8 : fastSlice0_3201 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_9 : fastSlice0_3201 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_10 : fastSlice0_3201 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_11 : fastSlice0_3201 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_12 : fastSlice0_3201 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_13 : fastSlice0_3201 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_14 : fastSlice0_3201 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_15 : fastSlice0_3201 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_16 : fastSlice0_3201 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_17 : fastSlice0_3201 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_18 : fastSlice0_3201 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_19 : fastSlice0_3201 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_20 : fastSlice0_3201 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_21 : fastSlice0_3201 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_22 : fastSlice0_3201 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_23 : fastSlice0_3201 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_24 : fastSlice0_3201 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_25 : fastSlice0_3201 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_26 : fastSlice0_3201 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_27 : fastSlice0_3201 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_28 : fastSlice0_3201 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_29 : fastSlice0_3201 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_30 : fastSlice0_3201 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_31 : fastSlice0_3201 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_32 : fastSlice0_3201 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_33 : fastSlice0_3201 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_34 : fastSlice0_3201 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_35 : fastSlice0_3201 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_36 : fastSlice0_3201 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_37 : fastSlice0_3201 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_38 : fastSlice0_3201 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_39 : fastSlice0_3201 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3201_40 : fastSlice0_3201 40 = true := by
  decide +kernel

public theorem point0_3201 : stepCheck 0 3201 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3201 u0_3201 v0_3201
    left0_3201 right0_3201
  intro b
  rw [sliceEq0_3201]
  fin_cases b
  · exact slice0_3201_0
  · exact slice0_3201_1
  · exact slice0_3201_2
  · exact slice0_3201_3
  · exact slice0_3201_4
  · exact slice0_3201_5
  · exact slice0_3201_6
  · exact slice0_3201_7
  · exact slice0_3201_8
  · exact slice0_3201_9
  · exact slice0_3201_10
  · exact slice0_3201_11
  · exact slice0_3201_12
  · exact slice0_3201_13
  · exact slice0_3201_14
  · exact slice0_3201_15
  · exact slice0_3201_16
  · exact slice0_3201_17
  · exact slice0_3201_18
  · exact slice0_3201_19
  · exact slice0_3201_20
  · exact slice0_3201_21
  · exact slice0_3201_22
  · exact slice0_3201_23
  · exact slice0_3201_24
  · exact slice0_3201_25
  · exact slice0_3201_26
  · exact slice0_3201_27
  · exact slice0_3201_28
  · exact slice0_3201_29
  · exact slice0_3201_30
  · exact slice0_3201_31
  · exact slice0_3201_32
  · exact slice0_3201_33
  · exact slice0_3201_34
  · exact slice0_3201_35
  · exact slice0_3201_36
  · exact slice0_3201_37
  · exact slice0_3201_38
  · exact slice0_3201_39
  · exact slice0_3201_40

set_option maxHeartbeats 1600000 in
public theorem point0_3202 : stepCheck 0 3202 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3203 : stepCheck 0 3203 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3204 : stepCheck 0 3204 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3205 : stepCheck 0 3205 := by
  left
  decide +kernel

private def u0_3206 : List (Fin 96) := [0, 50, 24, 64, 60]
private def v0_3206 : List (Fin 96) := [19, 21, 19, 50, 36, 8, 5, 5, 27, 31, 25, 27, 42, 17, 31]
private def lhs0_3206 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map60 (x)))))
private def rhs0_3206 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map17 (Part6Nat.force Compressed.map31 (x)))))))))))))))
private theorem lhs0_3206_eq : lhs0_3206 = Compressed.eval u0_3206 := by rfl
private theorem rhs0_3206_eq : rhs0_3206 = Compressed.eval v0_3206 := by rfl
private def fastSlice0_3206 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3206 ((100 * b.val + x.val) % 4060) =
      rhs0_3206 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3206 (b : Fin 41) :
    Compressed.slice u0_3206 v0_3206 b = fastSlice0_3206 b := by
  simp only [Compressed.slice, fastSlice0_3206, lhs0_3206_eq, rhs0_3206_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3206 : u0_3206.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3206).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3206 : v0_3206.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3206)).map Compressed.up0 ++
      (L0Factor 0 3206).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_0 : fastSlice0_3206 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_1 : fastSlice0_3206 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_2 : fastSlice0_3206 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_3 : fastSlice0_3206 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_4 : fastSlice0_3206 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_5 : fastSlice0_3206 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_6 : fastSlice0_3206 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_7 : fastSlice0_3206 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_8 : fastSlice0_3206 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_9 : fastSlice0_3206 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_10 : fastSlice0_3206 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_11 : fastSlice0_3206 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_12 : fastSlice0_3206 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_13 : fastSlice0_3206 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_14 : fastSlice0_3206 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_15 : fastSlice0_3206 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_16 : fastSlice0_3206 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_17 : fastSlice0_3206 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_18 : fastSlice0_3206 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_19 : fastSlice0_3206 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_20 : fastSlice0_3206 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_21 : fastSlice0_3206 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_22 : fastSlice0_3206 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_23 : fastSlice0_3206 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_24 : fastSlice0_3206 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_25 : fastSlice0_3206 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_26 : fastSlice0_3206 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_27 : fastSlice0_3206 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_28 : fastSlice0_3206 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_29 : fastSlice0_3206 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_30 : fastSlice0_3206 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_31 : fastSlice0_3206 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_32 : fastSlice0_3206 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_33 : fastSlice0_3206 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_34 : fastSlice0_3206 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_35 : fastSlice0_3206 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_36 : fastSlice0_3206 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_37 : fastSlice0_3206 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_38 : fastSlice0_3206 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_39 : fastSlice0_3206 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3206_40 : fastSlice0_3206 40 = true := by
  decide +kernel

public theorem point0_3206 : stepCheck 0 3206 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3206 u0_3206 v0_3206
    left0_3206 right0_3206
  intro b
  rw [sliceEq0_3206]
  fin_cases b
  · exact slice0_3206_0
  · exact slice0_3206_1
  · exact slice0_3206_2
  · exact slice0_3206_3
  · exact slice0_3206_4
  · exact slice0_3206_5
  · exact slice0_3206_6
  · exact slice0_3206_7
  · exact slice0_3206_8
  · exact slice0_3206_9
  · exact slice0_3206_10
  · exact slice0_3206_11
  · exact slice0_3206_12
  · exact slice0_3206_13
  · exact slice0_3206_14
  · exact slice0_3206_15
  · exact slice0_3206_16
  · exact slice0_3206_17
  · exact slice0_3206_18
  · exact slice0_3206_19
  · exact slice0_3206_20
  · exact slice0_3206_21
  · exact slice0_3206_22
  · exact slice0_3206_23
  · exact slice0_3206_24
  · exact slice0_3206_25
  · exact slice0_3206_26
  · exact slice0_3206_27
  · exact slice0_3206_28
  · exact slice0_3206_29
  · exact slice0_3206_30
  · exact slice0_3206_31
  · exact slice0_3206_32
  · exact slice0_3206_33
  · exact slice0_3206_34
  · exact slice0_3206_35
  · exact slice0_3206_36
  · exact slice0_3206_37
  · exact slice0_3206_38
  · exact slice0_3206_39
  · exact slice0_3206_40

private def u0_3207 : List (Fin 96) := [87, 24, 64, 60]
private def v0_3207 : List (Fin 96) := [50, 63, 46, 3, 79, 17, 4, 45, 71, 49, 86]
private def lhs0_3207 (x : Nat) : Nat := Part6Nat.force Compressed.map87 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map60 (x))))
private def rhs0_3207 (x : Nat) : Nat := Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map17 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map49 (Part6Nat.force Compressed.map86 (x)))))))))))
private theorem lhs0_3207_eq : lhs0_3207 = Compressed.eval u0_3207 := by rfl
private theorem rhs0_3207_eq : rhs0_3207 = Compressed.eval v0_3207 := by rfl
private def fastSlice0_3207 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3207 ((100 * b.val + x.val) % 4060) =
      rhs0_3207 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3207 (b : Fin 41) :
    Compressed.slice u0_3207 v0_3207 b = fastSlice0_3207 b := by
  simp only [Compressed.slice, fastSlice0_3207, lhs0_3207_eq, rhs0_3207_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3207 : u0_3207.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3207).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3207 : v0_3207.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3207)).map Compressed.up0 ++
      (L0Factor 0 3207).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_0 : fastSlice0_3207 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_1 : fastSlice0_3207 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_2 : fastSlice0_3207 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_3 : fastSlice0_3207 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_4 : fastSlice0_3207 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_5 : fastSlice0_3207 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_6 : fastSlice0_3207 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_7 : fastSlice0_3207 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_8 : fastSlice0_3207 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_9 : fastSlice0_3207 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_10 : fastSlice0_3207 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_11 : fastSlice0_3207 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_12 : fastSlice0_3207 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_13 : fastSlice0_3207 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_14 : fastSlice0_3207 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_15 : fastSlice0_3207 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_16 : fastSlice0_3207 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_17 : fastSlice0_3207 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_18 : fastSlice0_3207 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_19 : fastSlice0_3207 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_20 : fastSlice0_3207 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_21 : fastSlice0_3207 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_22 : fastSlice0_3207 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_23 : fastSlice0_3207 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_24 : fastSlice0_3207 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_25 : fastSlice0_3207 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_26 : fastSlice0_3207 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_27 : fastSlice0_3207 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_28 : fastSlice0_3207 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_29 : fastSlice0_3207 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_30 : fastSlice0_3207 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_31 : fastSlice0_3207 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_32 : fastSlice0_3207 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_33 : fastSlice0_3207 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_34 : fastSlice0_3207 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_35 : fastSlice0_3207 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_36 : fastSlice0_3207 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_37 : fastSlice0_3207 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_38 : fastSlice0_3207 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_39 : fastSlice0_3207 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3207_40 : fastSlice0_3207 40 = true := by
  decide +kernel

public theorem point0_3207 : stepCheck 0 3207 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3207 u0_3207 v0_3207
    left0_3207 right0_3207
  intro b
  rw [sliceEq0_3207]
  fin_cases b
  · exact slice0_3207_0
  · exact slice0_3207_1
  · exact slice0_3207_2
  · exact slice0_3207_3
  · exact slice0_3207_4
  · exact slice0_3207_5
  · exact slice0_3207_6
  · exact slice0_3207_7
  · exact slice0_3207_8
  · exact slice0_3207_9
  · exact slice0_3207_10
  · exact slice0_3207_11
  · exact slice0_3207_12
  · exact slice0_3207_13
  · exact slice0_3207_14
  · exact slice0_3207_15
  · exact slice0_3207_16
  · exact slice0_3207_17
  · exact slice0_3207_18
  · exact slice0_3207_19
  · exact slice0_3207_20
  · exact slice0_3207_21
  · exact slice0_3207_22
  · exact slice0_3207_23
  · exact slice0_3207_24
  · exact slice0_3207_25
  · exact slice0_3207_26
  · exact slice0_3207_27
  · exact slice0_3207_28
  · exact slice0_3207_29
  · exact slice0_3207_30
  · exact slice0_3207_31
  · exact slice0_3207_32
  · exact slice0_3207_33
  · exact slice0_3207_34
  · exact slice0_3207_35
  · exact slice0_3207_36
  · exact slice0_3207_37
  · exact slice0_3207_38
  · exact slice0_3207_39
  · exact slice0_3207_40

set_option maxHeartbeats 1600000 in
public theorem point0_3208 : stepCheck 0 3208 := by
  left
  decide +kernel

private def u0_3209 : List (Fin 96) := [0, 69, 64, 60]
private def v0_3209 : List (Fin 96) := [21, 19, 66, 3, 6, 8, 36, 29, 59, 32, 59, 62]
private def lhs0_3209 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map60 (x))))
private def rhs0_3209 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map62 (x))))))))))))
private theorem lhs0_3209_eq : lhs0_3209 = Compressed.eval u0_3209 := by rfl
private theorem rhs0_3209_eq : rhs0_3209 = Compressed.eval v0_3209 := by rfl
private def fastSlice0_3209 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3209 ((100 * b.val + x.val) % 4060) =
      rhs0_3209 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3209 (b : Fin 41) :
    Compressed.slice u0_3209 v0_3209 b = fastSlice0_3209 b := by
  simp only [Compressed.slice, fastSlice0_3209, lhs0_3209_eq, rhs0_3209_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3209 : u0_3209.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3209).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3209 : v0_3209.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3209)).map Compressed.up0 ++
      (L0Factor 0 3209).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_0 : fastSlice0_3209 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_1 : fastSlice0_3209 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_2 : fastSlice0_3209 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_3 : fastSlice0_3209 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_4 : fastSlice0_3209 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_5 : fastSlice0_3209 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_6 : fastSlice0_3209 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_7 : fastSlice0_3209 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_8 : fastSlice0_3209 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_9 : fastSlice0_3209 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_10 : fastSlice0_3209 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_11 : fastSlice0_3209 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_12 : fastSlice0_3209 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_13 : fastSlice0_3209 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_14 : fastSlice0_3209 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_15 : fastSlice0_3209 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_16 : fastSlice0_3209 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_17 : fastSlice0_3209 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_18 : fastSlice0_3209 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_19 : fastSlice0_3209 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_20 : fastSlice0_3209 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_21 : fastSlice0_3209 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_22 : fastSlice0_3209 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_23 : fastSlice0_3209 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_24 : fastSlice0_3209 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_25 : fastSlice0_3209 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_26 : fastSlice0_3209 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_27 : fastSlice0_3209 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_28 : fastSlice0_3209 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_29 : fastSlice0_3209 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_30 : fastSlice0_3209 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_31 : fastSlice0_3209 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_32 : fastSlice0_3209 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_33 : fastSlice0_3209 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_34 : fastSlice0_3209 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_35 : fastSlice0_3209 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_36 : fastSlice0_3209 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_37 : fastSlice0_3209 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_38 : fastSlice0_3209 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_39 : fastSlice0_3209 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3209_40 : fastSlice0_3209 40 = true := by
  decide +kernel

public theorem point0_3209 : stepCheck 0 3209 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3209 u0_3209 v0_3209
    left0_3209 right0_3209
  intro b
  rw [sliceEq0_3209]
  fin_cases b
  · exact slice0_3209_0
  · exact slice0_3209_1
  · exact slice0_3209_2
  · exact slice0_3209_3
  · exact slice0_3209_4
  · exact slice0_3209_5
  · exact slice0_3209_6
  · exact slice0_3209_7
  · exact slice0_3209_8
  · exact slice0_3209_9
  · exact slice0_3209_10
  · exact slice0_3209_11
  · exact slice0_3209_12
  · exact slice0_3209_13
  · exact slice0_3209_14
  · exact slice0_3209_15
  · exact slice0_3209_16
  · exact slice0_3209_17
  · exact slice0_3209_18
  · exact slice0_3209_19
  · exact slice0_3209_20
  · exact slice0_3209_21
  · exact slice0_3209_22
  · exact slice0_3209_23
  · exact slice0_3209_24
  · exact slice0_3209_25
  · exact slice0_3209_26
  · exact slice0_3209_27
  · exact slice0_3209_28
  · exact slice0_3209_29
  · exact slice0_3209_30
  · exact slice0_3209_31
  · exact slice0_3209_32
  · exact slice0_3209_33
  · exact slice0_3209_34
  · exact slice0_3209_35
  · exact slice0_3209_36
  · exact slice0_3209_37
  · exact slice0_3209_38
  · exact slice0_3209_39
  · exact slice0_3209_40

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
