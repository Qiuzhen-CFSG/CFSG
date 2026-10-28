module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 22, generator 0, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point0_3210 : stepCheck 0 3210 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3211 : stepCheck 0 3211 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3212 : stepCheck 0 3212 := by
  left
  decide +kernel

private def u0_3213 : List (Fin 96) := [0, 24, 64, 21, 60]
private def v0_3213 : List (Fin 96) := [14, 69, 46, 24, 4, 4, 36, 10, 25, 29, 31, 71, 7]
private def lhs0_3213 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map60 (x)))))
private def rhs0_3213 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map7 (x)))))))))))))
private theorem lhs0_3213_eq : lhs0_3213 = Compressed.eval u0_3213 := by rfl
private theorem rhs0_3213_eq : rhs0_3213 = Compressed.eval v0_3213 := by rfl
private def fastSlice0_3213 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3213 ((100 * b.val + x.val) % 4060) =
      rhs0_3213 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3213 (b : Fin 41) :
    Compressed.slice u0_3213 v0_3213 b = fastSlice0_3213 b := by
  simp only [Compressed.slice, fastSlice0_3213, lhs0_3213_eq, rhs0_3213_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3213 : u0_3213.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3213).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3213 : v0_3213.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3213)).map Compressed.up0 ++
      (L0Factor 0 3213).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_0 : fastSlice0_3213 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_1 : fastSlice0_3213 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_2 : fastSlice0_3213 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_3 : fastSlice0_3213 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_4 : fastSlice0_3213 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_5 : fastSlice0_3213 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_6 : fastSlice0_3213 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_7 : fastSlice0_3213 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_8 : fastSlice0_3213 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_9 : fastSlice0_3213 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_10 : fastSlice0_3213 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_11 : fastSlice0_3213 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_12 : fastSlice0_3213 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_13 : fastSlice0_3213 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_14 : fastSlice0_3213 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_15 : fastSlice0_3213 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_16 : fastSlice0_3213 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_17 : fastSlice0_3213 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_18 : fastSlice0_3213 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_19 : fastSlice0_3213 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_20 : fastSlice0_3213 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_21 : fastSlice0_3213 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_22 : fastSlice0_3213 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_23 : fastSlice0_3213 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_24 : fastSlice0_3213 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_25 : fastSlice0_3213 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_26 : fastSlice0_3213 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_27 : fastSlice0_3213 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_28 : fastSlice0_3213 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_29 : fastSlice0_3213 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_30 : fastSlice0_3213 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_31 : fastSlice0_3213 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_32 : fastSlice0_3213 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_33 : fastSlice0_3213 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_34 : fastSlice0_3213 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_35 : fastSlice0_3213 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_36 : fastSlice0_3213 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_37 : fastSlice0_3213 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_38 : fastSlice0_3213 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_39 : fastSlice0_3213 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3213_40 : fastSlice0_3213 40 = true := by
  decide +kernel

public theorem point0_3213 : stepCheck 0 3213 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3213 u0_3213 v0_3213
    left0_3213 right0_3213
  intro b
  rw [sliceEq0_3213]
  fin_cases b
  · exact slice0_3213_0
  · exact slice0_3213_1
  · exact slice0_3213_2
  · exact slice0_3213_3
  · exact slice0_3213_4
  · exact slice0_3213_5
  · exact slice0_3213_6
  · exact slice0_3213_7
  · exact slice0_3213_8
  · exact slice0_3213_9
  · exact slice0_3213_10
  · exact slice0_3213_11
  · exact slice0_3213_12
  · exact slice0_3213_13
  · exact slice0_3213_14
  · exact slice0_3213_15
  · exact slice0_3213_16
  · exact slice0_3213_17
  · exact slice0_3213_18
  · exact slice0_3213_19
  · exact slice0_3213_20
  · exact slice0_3213_21
  · exact slice0_3213_22
  · exact slice0_3213_23
  · exact slice0_3213_24
  · exact slice0_3213_25
  · exact slice0_3213_26
  · exact slice0_3213_27
  · exact slice0_3213_28
  · exact slice0_3213_29
  · exact slice0_3213_30
  · exact slice0_3213_31
  · exact slice0_3213_32
  · exact slice0_3213_33
  · exact slice0_3213_34
  · exact slice0_3213_35
  · exact slice0_3213_36
  · exact slice0_3213_37
  · exact slice0_3213_38
  · exact slice0_3213_39
  · exact slice0_3213_40

private def u0_3214 : List (Fin 96) := [0, 66, 65, 3]
private def v0_3214 : List (Fin 96) := [14, 66, 50, 12, 3, 79, 13, 6, 15, 18, 37, 45, 57]
private def lhs0_3214 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map3 (x))))
private def rhs0_3214 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map15 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map57 (x)))))))))))))
private theorem lhs0_3214_eq : lhs0_3214 = Compressed.eval u0_3214 := by rfl
private theorem rhs0_3214_eq : rhs0_3214 = Compressed.eval v0_3214 := by rfl
private def fastSlice0_3214 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3214 ((100 * b.val + x.val) % 4060) =
      rhs0_3214 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3214 (b : Fin 41) :
    Compressed.slice u0_3214 v0_3214 b = fastSlice0_3214 b := by
  simp only [Compressed.slice, fastSlice0_3214, lhs0_3214_eq, rhs0_3214_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3214 : u0_3214.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3214).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3214 : v0_3214.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3214)).map Compressed.up0 ++
      (L0Factor 0 3214).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_0 : fastSlice0_3214 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_1 : fastSlice0_3214 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_2 : fastSlice0_3214 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_3 : fastSlice0_3214 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_4 : fastSlice0_3214 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_5 : fastSlice0_3214 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_6 : fastSlice0_3214 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_7 : fastSlice0_3214 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_8 : fastSlice0_3214 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_9 : fastSlice0_3214 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_10 : fastSlice0_3214 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_11 : fastSlice0_3214 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_12 : fastSlice0_3214 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_13 : fastSlice0_3214 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_14 : fastSlice0_3214 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_15 : fastSlice0_3214 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_16 : fastSlice0_3214 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_17 : fastSlice0_3214 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_18 : fastSlice0_3214 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_19 : fastSlice0_3214 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_20 : fastSlice0_3214 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_21 : fastSlice0_3214 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_22 : fastSlice0_3214 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_23 : fastSlice0_3214 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_24 : fastSlice0_3214 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_25 : fastSlice0_3214 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_26 : fastSlice0_3214 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_27 : fastSlice0_3214 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_28 : fastSlice0_3214 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_29 : fastSlice0_3214 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_30 : fastSlice0_3214 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_31 : fastSlice0_3214 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_32 : fastSlice0_3214 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_33 : fastSlice0_3214 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_34 : fastSlice0_3214 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_35 : fastSlice0_3214 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_36 : fastSlice0_3214 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_37 : fastSlice0_3214 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_38 : fastSlice0_3214 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_39 : fastSlice0_3214 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3214_40 : fastSlice0_3214 40 = true := by
  decide +kernel

public theorem point0_3214 : stepCheck 0 3214 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3214 u0_3214 v0_3214
    left0_3214 right0_3214
  intro b
  rw [sliceEq0_3214]
  fin_cases b
  · exact slice0_3214_0
  · exact slice0_3214_1
  · exact slice0_3214_2
  · exact slice0_3214_3
  · exact slice0_3214_4
  · exact slice0_3214_5
  · exact slice0_3214_6
  · exact slice0_3214_7
  · exact slice0_3214_8
  · exact slice0_3214_9
  · exact slice0_3214_10
  · exact slice0_3214_11
  · exact slice0_3214_12
  · exact slice0_3214_13
  · exact slice0_3214_14
  · exact slice0_3214_15
  · exact slice0_3214_16
  · exact slice0_3214_17
  · exact slice0_3214_18
  · exact slice0_3214_19
  · exact slice0_3214_20
  · exact slice0_3214_21
  · exact slice0_3214_22
  · exact slice0_3214_23
  · exact slice0_3214_24
  · exact slice0_3214_25
  · exact slice0_3214_26
  · exact slice0_3214_27
  · exact slice0_3214_28
  · exact slice0_3214_29
  · exact slice0_3214_30
  · exact slice0_3214_31
  · exact slice0_3214_32
  · exact slice0_3214_33
  · exact slice0_3214_34
  · exact slice0_3214_35
  · exact slice0_3214_36
  · exact slice0_3214_37
  · exact slice0_3214_38
  · exact slice0_3214_39
  · exact slice0_3214_40

set_option maxHeartbeats 1600000 in
public theorem point0_3215 : stepCheck 0 3215 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3216 : stepCheck 0 3216 := by
  left
  decide +kernel

private def u0_3217 : List (Fin 96) := [0, 12, 46, 65, 3]
private def v0_3217 : List (Fin 96) := [24, 51, 50, 19, 4, 79, 11, 80, 74, 83, 83, 41, 32, 52]
private def lhs0_3217 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map3 (x)))))
private def rhs0_3217 (x : Nat) : Nat := Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map41 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map52 (x))))))))))))))
private theorem lhs0_3217_eq : lhs0_3217 = Compressed.eval u0_3217 := by rfl
private theorem rhs0_3217_eq : rhs0_3217 = Compressed.eval v0_3217 := by rfl
private def fastSlice0_3217 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3217 ((100 * b.val + x.val) % 4060) =
      rhs0_3217 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3217 (b : Fin 41) :
    Compressed.slice u0_3217 v0_3217 b = fastSlice0_3217 b := by
  simp only [Compressed.slice, fastSlice0_3217, lhs0_3217_eq, rhs0_3217_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3217 : u0_3217.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3217).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3217 : v0_3217.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3217)).map Compressed.up0 ++
      (L0Factor 0 3217).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_0 : fastSlice0_3217 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_1 : fastSlice0_3217 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_2 : fastSlice0_3217 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_3 : fastSlice0_3217 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_4 : fastSlice0_3217 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_5 : fastSlice0_3217 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_6 : fastSlice0_3217 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_7 : fastSlice0_3217 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_8 : fastSlice0_3217 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_9 : fastSlice0_3217 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_10 : fastSlice0_3217 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_11 : fastSlice0_3217 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_12 : fastSlice0_3217 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_13 : fastSlice0_3217 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_14 : fastSlice0_3217 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_15 : fastSlice0_3217 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_16 : fastSlice0_3217 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_17 : fastSlice0_3217 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_18 : fastSlice0_3217 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_19 : fastSlice0_3217 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_20 : fastSlice0_3217 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_21 : fastSlice0_3217 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_22 : fastSlice0_3217 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_23 : fastSlice0_3217 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_24 : fastSlice0_3217 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_25 : fastSlice0_3217 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_26 : fastSlice0_3217 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_27 : fastSlice0_3217 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_28 : fastSlice0_3217 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_29 : fastSlice0_3217 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_30 : fastSlice0_3217 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_31 : fastSlice0_3217 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_32 : fastSlice0_3217 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_33 : fastSlice0_3217 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_34 : fastSlice0_3217 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_35 : fastSlice0_3217 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_36 : fastSlice0_3217 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_37 : fastSlice0_3217 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_38 : fastSlice0_3217 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_39 : fastSlice0_3217 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3217_40 : fastSlice0_3217 40 = true := by
  decide +kernel

public theorem point0_3217 : stepCheck 0 3217 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3217 u0_3217 v0_3217
    left0_3217 right0_3217
  intro b
  rw [sliceEq0_3217]
  fin_cases b
  · exact slice0_3217_0
  · exact slice0_3217_1
  · exact slice0_3217_2
  · exact slice0_3217_3
  · exact slice0_3217_4
  · exact slice0_3217_5
  · exact slice0_3217_6
  · exact slice0_3217_7
  · exact slice0_3217_8
  · exact slice0_3217_9
  · exact slice0_3217_10
  · exact slice0_3217_11
  · exact slice0_3217_12
  · exact slice0_3217_13
  · exact slice0_3217_14
  · exact slice0_3217_15
  · exact slice0_3217_16
  · exact slice0_3217_17
  · exact slice0_3217_18
  · exact slice0_3217_19
  · exact slice0_3217_20
  · exact slice0_3217_21
  · exact slice0_3217_22
  · exact slice0_3217_23
  · exact slice0_3217_24
  · exact slice0_3217_25
  · exact slice0_3217_26
  · exact slice0_3217_27
  · exact slice0_3217_28
  · exact slice0_3217_29
  · exact slice0_3217_30
  · exact slice0_3217_31
  · exact slice0_3217_32
  · exact slice0_3217_33
  · exact slice0_3217_34
  · exact slice0_3217_35
  · exact slice0_3217_36
  · exact slice0_3217_37
  · exact slice0_3217_38
  · exact slice0_3217_39
  · exact slice0_3217_40

set_option maxHeartbeats 1600000 in
public theorem point0_3218 : stepCheck 0 3218 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3219 : stepCheck 0 3219 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
