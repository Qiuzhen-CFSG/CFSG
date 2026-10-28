module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 17, generator 0, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u0_2510 : List (Fin 96) := [67, 66, 19, 60]
private def v0_2510 : List (Fin 96) := [14, 64, 95, 9, 10, 36, 4, 53, 80, 74, 37, 55, 42, 86]
private def lhs0_2510 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map60 (x))))
private def rhs0_2510 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map95 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map53 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map55 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map86 (x))))))))))))))
private theorem lhs0_2510_eq : lhs0_2510 = Compressed.eval u0_2510 := by rfl
private theorem rhs0_2510_eq : rhs0_2510 = Compressed.eval v0_2510 := by rfl
private def fastSlice0_2510 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2510 ((100 * b.val + x.val) % 4060) =
      rhs0_2510 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2510 (b : Fin 41) :
    Compressed.slice u0_2510 v0_2510 b = fastSlice0_2510 b := by
  simp only [Compressed.slice, fastSlice0_2510, lhs0_2510_eq, rhs0_2510_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2510 : u0_2510.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2510).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2510 : v0_2510.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2510)).map Compressed.up0 ++
      (L0Factor 0 2510).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_0 : fastSlice0_2510 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_1 : fastSlice0_2510 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_2 : fastSlice0_2510 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_3 : fastSlice0_2510 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_4 : fastSlice0_2510 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_5 : fastSlice0_2510 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_6 : fastSlice0_2510 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_7 : fastSlice0_2510 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_8 : fastSlice0_2510 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_9 : fastSlice0_2510 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_10 : fastSlice0_2510 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_11 : fastSlice0_2510 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_12 : fastSlice0_2510 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_13 : fastSlice0_2510 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_14 : fastSlice0_2510 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_15 : fastSlice0_2510 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_16 : fastSlice0_2510 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_17 : fastSlice0_2510 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_18 : fastSlice0_2510 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_19 : fastSlice0_2510 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_20 : fastSlice0_2510 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_21 : fastSlice0_2510 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_22 : fastSlice0_2510 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_23 : fastSlice0_2510 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_24 : fastSlice0_2510 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_25 : fastSlice0_2510 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_26 : fastSlice0_2510 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_27 : fastSlice0_2510 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_28 : fastSlice0_2510 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_29 : fastSlice0_2510 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_30 : fastSlice0_2510 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_31 : fastSlice0_2510 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_32 : fastSlice0_2510 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_33 : fastSlice0_2510 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_34 : fastSlice0_2510 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_35 : fastSlice0_2510 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_36 : fastSlice0_2510 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_37 : fastSlice0_2510 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_38 : fastSlice0_2510 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_39 : fastSlice0_2510 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2510_40 : fastSlice0_2510 40 = true := by
  decide +kernel

public theorem point0_2510 : stepCheck 0 2510 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2510 u0_2510 v0_2510
    left0_2510 right0_2510
  intro b
  rw [sliceEq0_2510]
  fin_cases b
  · exact slice0_2510_0
  · exact slice0_2510_1
  · exact slice0_2510_2
  · exact slice0_2510_3
  · exact slice0_2510_4
  · exact slice0_2510_5
  · exact slice0_2510_6
  · exact slice0_2510_7
  · exact slice0_2510_8
  · exact slice0_2510_9
  · exact slice0_2510_10
  · exact slice0_2510_11
  · exact slice0_2510_12
  · exact slice0_2510_13
  · exact slice0_2510_14
  · exact slice0_2510_15
  · exact slice0_2510_16
  · exact slice0_2510_17
  · exact slice0_2510_18
  · exact slice0_2510_19
  · exact slice0_2510_20
  · exact slice0_2510_21
  · exact slice0_2510_22
  · exact slice0_2510_23
  · exact slice0_2510_24
  · exact slice0_2510_25
  · exact slice0_2510_26
  · exact slice0_2510_27
  · exact slice0_2510_28
  · exact slice0_2510_29
  · exact slice0_2510_30
  · exact slice0_2510_31
  · exact slice0_2510_32
  · exact slice0_2510_33
  · exact slice0_2510_34
  · exact slice0_2510_35
  · exact slice0_2510_36
  · exact slice0_2510_37
  · exact slice0_2510_38
  · exact slice0_2510_39
  · exact slice0_2510_40

set_option maxHeartbeats 1600000 in
public theorem point0_2511 : stepCheck 0 2511 := by
  left
  decide +kernel

private def u0_2512 : List (Fin 96) := [0, 50, 92, 60]
private def v0_2512 : List (Fin 96) := [77, 82, 3, 11, 36, 4, 27, 31, 74, 91, 7]
private def lhs0_2512 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map92 (Part6Nat.force Compressed.map60 (x))))
private def rhs0_2512 (x : Nat) : Nat := Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map91 (Part6Nat.force Compressed.map7 (x)))))))))))
private theorem lhs0_2512_eq : lhs0_2512 = Compressed.eval u0_2512 := by rfl
private theorem rhs0_2512_eq : rhs0_2512 = Compressed.eval v0_2512 := by rfl
private def fastSlice0_2512 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2512 ((100 * b.val + x.val) % 4060) =
      rhs0_2512 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2512 (b : Fin 41) :
    Compressed.slice u0_2512 v0_2512 b = fastSlice0_2512 b := by
  simp only [Compressed.slice, fastSlice0_2512, lhs0_2512_eq, rhs0_2512_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2512 : u0_2512.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2512).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2512 : v0_2512.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2512)).map Compressed.up0 ++
      (L0Factor 0 2512).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_0 : fastSlice0_2512 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_1 : fastSlice0_2512 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_2 : fastSlice0_2512 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_3 : fastSlice0_2512 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_4 : fastSlice0_2512 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_5 : fastSlice0_2512 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_6 : fastSlice0_2512 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_7 : fastSlice0_2512 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_8 : fastSlice0_2512 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_9 : fastSlice0_2512 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_10 : fastSlice0_2512 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_11 : fastSlice0_2512 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_12 : fastSlice0_2512 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_13 : fastSlice0_2512 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_14 : fastSlice0_2512 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_15 : fastSlice0_2512 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_16 : fastSlice0_2512 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_17 : fastSlice0_2512 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_18 : fastSlice0_2512 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_19 : fastSlice0_2512 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_20 : fastSlice0_2512 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_21 : fastSlice0_2512 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_22 : fastSlice0_2512 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_23 : fastSlice0_2512 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_24 : fastSlice0_2512 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_25 : fastSlice0_2512 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_26 : fastSlice0_2512 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_27 : fastSlice0_2512 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_28 : fastSlice0_2512 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_29 : fastSlice0_2512 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_30 : fastSlice0_2512 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_31 : fastSlice0_2512 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_32 : fastSlice0_2512 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_33 : fastSlice0_2512 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_34 : fastSlice0_2512 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_35 : fastSlice0_2512 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_36 : fastSlice0_2512 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_37 : fastSlice0_2512 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_38 : fastSlice0_2512 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_39 : fastSlice0_2512 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2512_40 : fastSlice0_2512 40 = true := by
  decide +kernel

public theorem point0_2512 : stepCheck 0 2512 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2512 u0_2512 v0_2512
    left0_2512 right0_2512
  intro b
  rw [sliceEq0_2512]
  fin_cases b
  · exact slice0_2512_0
  · exact slice0_2512_1
  · exact slice0_2512_2
  · exact slice0_2512_3
  · exact slice0_2512_4
  · exact slice0_2512_5
  · exact slice0_2512_6
  · exact slice0_2512_7
  · exact slice0_2512_8
  · exact slice0_2512_9
  · exact slice0_2512_10
  · exact slice0_2512_11
  · exact slice0_2512_12
  · exact slice0_2512_13
  · exact slice0_2512_14
  · exact slice0_2512_15
  · exact slice0_2512_16
  · exact slice0_2512_17
  · exact slice0_2512_18
  · exact slice0_2512_19
  · exact slice0_2512_20
  · exact slice0_2512_21
  · exact slice0_2512_22
  · exact slice0_2512_23
  · exact slice0_2512_24
  · exact slice0_2512_25
  · exact slice0_2512_26
  · exact slice0_2512_27
  · exact slice0_2512_28
  · exact slice0_2512_29
  · exact slice0_2512_30
  · exact slice0_2512_31
  · exact slice0_2512_32
  · exact slice0_2512_33
  · exact slice0_2512_34
  · exact slice0_2512_35
  · exact slice0_2512_36
  · exact slice0_2512_37
  · exact slice0_2512_38
  · exact slice0_2512_39
  · exact slice0_2512_40

set_option maxHeartbeats 1600000 in
public theorem point0_2513 : stepCheck 0 2513 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2514 : stepCheck 0 2514 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2515 : stepCheck 0 2515 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2516 : stepCheck 0 2516 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2517 : stepCheck 0 2517 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2518 : stepCheck 0 2518 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2519 : stepCheck 0 2519 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
