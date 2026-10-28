module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 23, generator 0, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point0_3350 : stepCheck 0 3350 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3351 : stepCheck 0 3351 := by
  left
  decide +kernel

private def u0_3352 : List (Fin 96) := [67, 50, 24, 76]
private def v0_3352 : List (Fin 96) := [78, 46, 78, 4, 20, 4, 5, 13, 17, 32, 23, 71, 88]
private def lhs0_3352 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map76 (x))))
private def rhs0_3352 (x : Nat) : Nat := Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map20 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map17 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map88 (x)))))))))))))
private theorem lhs0_3352_eq : lhs0_3352 = Compressed.eval u0_3352 := by rfl
private theorem rhs0_3352_eq : rhs0_3352 = Compressed.eval v0_3352 := by rfl
private def fastSlice0_3352 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3352 ((100 * b.val + x.val) % 4060) =
      rhs0_3352 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3352 (b : Fin 41) :
    Compressed.slice u0_3352 v0_3352 b = fastSlice0_3352 b := by
  simp only [Compressed.slice, fastSlice0_3352, lhs0_3352_eq, rhs0_3352_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3352 : u0_3352.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3352).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3352 : v0_3352.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3352)).map Compressed.up0 ++
      (L0Factor 0 3352).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_0 : fastSlice0_3352 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_1 : fastSlice0_3352 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_2 : fastSlice0_3352 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_3 : fastSlice0_3352 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_4 : fastSlice0_3352 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_5 : fastSlice0_3352 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_6 : fastSlice0_3352 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_7 : fastSlice0_3352 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_8 : fastSlice0_3352 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_9 : fastSlice0_3352 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_10 : fastSlice0_3352 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_11 : fastSlice0_3352 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_12 : fastSlice0_3352 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_13 : fastSlice0_3352 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_14 : fastSlice0_3352 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_15 : fastSlice0_3352 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_16 : fastSlice0_3352 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_17 : fastSlice0_3352 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_18 : fastSlice0_3352 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_19 : fastSlice0_3352 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_20 : fastSlice0_3352 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_21 : fastSlice0_3352 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_22 : fastSlice0_3352 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_23 : fastSlice0_3352 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_24 : fastSlice0_3352 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_25 : fastSlice0_3352 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_26 : fastSlice0_3352 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_27 : fastSlice0_3352 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_28 : fastSlice0_3352 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_29 : fastSlice0_3352 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_30 : fastSlice0_3352 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_31 : fastSlice0_3352 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_32 : fastSlice0_3352 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_33 : fastSlice0_3352 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_34 : fastSlice0_3352 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_35 : fastSlice0_3352 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_36 : fastSlice0_3352 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_37 : fastSlice0_3352 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_38 : fastSlice0_3352 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_39 : fastSlice0_3352 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3352_40 : fastSlice0_3352 40 = true := by
  decide +kernel

public theorem point0_3352 : stepCheck 0 3352 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3352 u0_3352 v0_3352
    left0_3352 right0_3352
  intro b
  rw [sliceEq0_3352]
  fin_cases b
  · exact slice0_3352_0
  · exact slice0_3352_1
  · exact slice0_3352_2
  · exact slice0_3352_3
  · exact slice0_3352_4
  · exact slice0_3352_5
  · exact slice0_3352_6
  · exact slice0_3352_7
  · exact slice0_3352_8
  · exact slice0_3352_9
  · exact slice0_3352_10
  · exact slice0_3352_11
  · exact slice0_3352_12
  · exact slice0_3352_13
  · exact slice0_3352_14
  · exact slice0_3352_15
  · exact slice0_3352_16
  · exact slice0_3352_17
  · exact slice0_3352_18
  · exact slice0_3352_19
  · exact slice0_3352_20
  · exact slice0_3352_21
  · exact slice0_3352_22
  · exact slice0_3352_23
  · exact slice0_3352_24
  · exact slice0_3352_25
  · exact slice0_3352_26
  · exact slice0_3352_27
  · exact slice0_3352_28
  · exact slice0_3352_29
  · exact slice0_3352_30
  · exact slice0_3352_31
  · exact slice0_3352_32
  · exact slice0_3352_33
  · exact slice0_3352_34
  · exact slice0_3352_35
  · exact slice0_3352_36
  · exact slice0_3352_37
  · exact slice0_3352_38
  · exact slice0_3352_39
  · exact slice0_3352_40

set_option maxHeartbeats 1600000 in
public theorem point0_3353 : stepCheck 0 3353 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3354 : stepCheck 0 3354 := by
  left
  decide +kernel

private def u0_3355 : List (Fin 96) := [0, 46, 65, 19]
private def v0_3355 : List (Fin 96) := [21, 65, 19, 9, 4, 36, 11, 25, 74, 48, 59, 62]
private def lhs0_3355 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map19 (x))))
private def rhs0_3355 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map48 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map62 (x))))))))))))
private theorem lhs0_3355_eq : lhs0_3355 = Compressed.eval u0_3355 := by rfl
private theorem rhs0_3355_eq : rhs0_3355 = Compressed.eval v0_3355 := by rfl
private def fastSlice0_3355 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3355 ((100 * b.val + x.val) % 4060) =
      rhs0_3355 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3355 (b : Fin 41) :
    Compressed.slice u0_3355 v0_3355 b = fastSlice0_3355 b := by
  simp only [Compressed.slice, fastSlice0_3355, lhs0_3355_eq, rhs0_3355_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3355 : u0_3355.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3355).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3355 : v0_3355.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3355)).map Compressed.up0 ++
      (L0Factor 0 3355).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_0 : fastSlice0_3355 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_1 : fastSlice0_3355 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_2 : fastSlice0_3355 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_3 : fastSlice0_3355 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_4 : fastSlice0_3355 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_5 : fastSlice0_3355 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_6 : fastSlice0_3355 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_7 : fastSlice0_3355 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_8 : fastSlice0_3355 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_9 : fastSlice0_3355 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_10 : fastSlice0_3355 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_11 : fastSlice0_3355 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_12 : fastSlice0_3355 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_13 : fastSlice0_3355 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_14 : fastSlice0_3355 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_15 : fastSlice0_3355 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_16 : fastSlice0_3355 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_17 : fastSlice0_3355 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_18 : fastSlice0_3355 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_19 : fastSlice0_3355 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_20 : fastSlice0_3355 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_21 : fastSlice0_3355 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_22 : fastSlice0_3355 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_23 : fastSlice0_3355 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_24 : fastSlice0_3355 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_25 : fastSlice0_3355 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_26 : fastSlice0_3355 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_27 : fastSlice0_3355 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_28 : fastSlice0_3355 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_29 : fastSlice0_3355 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_30 : fastSlice0_3355 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_31 : fastSlice0_3355 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_32 : fastSlice0_3355 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_33 : fastSlice0_3355 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_34 : fastSlice0_3355 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_35 : fastSlice0_3355 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_36 : fastSlice0_3355 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_37 : fastSlice0_3355 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_38 : fastSlice0_3355 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_39 : fastSlice0_3355 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3355_40 : fastSlice0_3355 40 = true := by
  decide +kernel

public theorem point0_3355 : stepCheck 0 3355 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3355 u0_3355 v0_3355
    left0_3355 right0_3355
  intro b
  rw [sliceEq0_3355]
  fin_cases b
  · exact slice0_3355_0
  · exact slice0_3355_1
  · exact slice0_3355_2
  · exact slice0_3355_3
  · exact slice0_3355_4
  · exact slice0_3355_5
  · exact slice0_3355_6
  · exact slice0_3355_7
  · exact slice0_3355_8
  · exact slice0_3355_9
  · exact slice0_3355_10
  · exact slice0_3355_11
  · exact slice0_3355_12
  · exact slice0_3355_13
  · exact slice0_3355_14
  · exact slice0_3355_15
  · exact slice0_3355_16
  · exact slice0_3355_17
  · exact slice0_3355_18
  · exact slice0_3355_19
  · exact slice0_3355_20
  · exact slice0_3355_21
  · exact slice0_3355_22
  · exact slice0_3355_23
  · exact slice0_3355_24
  · exact slice0_3355_25
  · exact slice0_3355_26
  · exact slice0_3355_27
  · exact slice0_3355_28
  · exact slice0_3355_29
  · exact slice0_3355_30
  · exact slice0_3355_31
  · exact slice0_3355_32
  · exact slice0_3355_33
  · exact slice0_3355_34
  · exact slice0_3355_35
  · exact slice0_3355_36
  · exact slice0_3355_37
  · exact slice0_3355_38
  · exact slice0_3355_39
  · exact slice0_3355_40

set_option maxHeartbeats 1600000 in
public theorem point0_3356 : stepCheck 0 3356 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3357 : stepCheck 0 3357 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3358 : stepCheck 0 3358 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3359 : stepCheck 0 3359 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
