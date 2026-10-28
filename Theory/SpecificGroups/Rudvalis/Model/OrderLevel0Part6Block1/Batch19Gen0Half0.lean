module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 19, generator 0, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point0_2780 : stepCheck 0 2780 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2781 : stepCheck 0 2781 := by
  left
  decide +kernel

private def u0_2782 : List (Fin 96) := [67, 78, 76]
private def v0_2782 : List (Fin 96) := [82, 50, 50, 6, 8, 16, 4, 8, 40, 23, 29, 59, 85, 31, 56, 56]
private def lhs0_2782 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map76 (x)))
private def rhs0_2782 (x : Nat) : Nat := Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map85 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map56 (Part6Nat.force Compressed.map56 (x))))))))))))))))
private theorem lhs0_2782_eq : lhs0_2782 = Compressed.eval u0_2782 := by rfl
private theorem rhs0_2782_eq : rhs0_2782 = Compressed.eval v0_2782 := by rfl
private def fastSlice0_2782 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2782 ((100 * b.val + x.val) % 4060) =
      rhs0_2782 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2782 (b : Fin 41) :
    Compressed.slice u0_2782 v0_2782 b = fastSlice0_2782 b := by
  simp only [Compressed.slice, fastSlice0_2782, lhs0_2782_eq, rhs0_2782_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2782 : u0_2782.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2782).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2782 : v0_2782.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2782)).map Compressed.up0 ++
      (L0Factor 0 2782).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_0 : fastSlice0_2782 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_1 : fastSlice0_2782 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_2 : fastSlice0_2782 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_3 : fastSlice0_2782 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_4 : fastSlice0_2782 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_5 : fastSlice0_2782 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_6 : fastSlice0_2782 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_7 : fastSlice0_2782 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_8 : fastSlice0_2782 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_9 : fastSlice0_2782 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_10 : fastSlice0_2782 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_11 : fastSlice0_2782 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_12 : fastSlice0_2782 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_13 : fastSlice0_2782 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_14 : fastSlice0_2782 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_15 : fastSlice0_2782 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_16 : fastSlice0_2782 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_17 : fastSlice0_2782 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_18 : fastSlice0_2782 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_19 : fastSlice0_2782 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_20 : fastSlice0_2782 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_21 : fastSlice0_2782 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_22 : fastSlice0_2782 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_23 : fastSlice0_2782 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_24 : fastSlice0_2782 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_25 : fastSlice0_2782 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_26 : fastSlice0_2782 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_27 : fastSlice0_2782 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_28 : fastSlice0_2782 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_29 : fastSlice0_2782 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_30 : fastSlice0_2782 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_31 : fastSlice0_2782 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_32 : fastSlice0_2782 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_33 : fastSlice0_2782 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_34 : fastSlice0_2782 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_35 : fastSlice0_2782 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_36 : fastSlice0_2782 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_37 : fastSlice0_2782 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_38 : fastSlice0_2782 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_39 : fastSlice0_2782 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2782_40 : fastSlice0_2782 40 = true := by
  decide +kernel

public theorem point0_2782 : stepCheck 0 2782 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2782 u0_2782 v0_2782
    left0_2782 right0_2782
  intro b
  rw [sliceEq0_2782]
  fin_cases b
  · exact slice0_2782_0
  · exact slice0_2782_1
  · exact slice0_2782_2
  · exact slice0_2782_3
  · exact slice0_2782_4
  · exact slice0_2782_5
  · exact slice0_2782_6
  · exact slice0_2782_7
  · exact slice0_2782_8
  · exact slice0_2782_9
  · exact slice0_2782_10
  · exact slice0_2782_11
  · exact slice0_2782_12
  · exact slice0_2782_13
  · exact slice0_2782_14
  · exact slice0_2782_15
  · exact slice0_2782_16
  · exact slice0_2782_17
  · exact slice0_2782_18
  · exact slice0_2782_19
  · exact slice0_2782_20
  · exact slice0_2782_21
  · exact slice0_2782_22
  · exact slice0_2782_23
  · exact slice0_2782_24
  · exact slice0_2782_25
  · exact slice0_2782_26
  · exact slice0_2782_27
  · exact slice0_2782_28
  · exact slice0_2782_29
  · exact slice0_2782_30
  · exact slice0_2782_31
  · exact slice0_2782_32
  · exact slice0_2782_33
  · exact slice0_2782_34
  · exact slice0_2782_35
  · exact slice0_2782_36
  · exact slice0_2782_37
  · exact slice0_2782_38
  · exact slice0_2782_39
  · exact slice0_2782_40

set_option maxHeartbeats 1600000 in
public theorem point0_2783 : stepCheck 0 2783 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2784 : stepCheck 0 2784 := by
  left
  decide +kernel

private def u0_2785 : List (Fin 96) := [87, 19, 76]
private def v0_2785 : List (Fin 96) := [21, 77, 58, 3, 10, 11, 10, 35, 18, 32, 23, 29, 88]
private def lhs0_2785 (x : Nat) : Nat := Part6Nat.force Compressed.map87 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map76 (x)))
private def rhs0_2785 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map35 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map88 (x)))))))))))))
private theorem lhs0_2785_eq : lhs0_2785 = Compressed.eval u0_2785 := by rfl
private theorem rhs0_2785_eq : rhs0_2785 = Compressed.eval v0_2785 := by rfl
private def fastSlice0_2785 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2785 ((100 * b.val + x.val) % 4060) =
      rhs0_2785 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2785 (b : Fin 41) :
    Compressed.slice u0_2785 v0_2785 b = fastSlice0_2785 b := by
  simp only [Compressed.slice, fastSlice0_2785, lhs0_2785_eq, rhs0_2785_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2785 : u0_2785.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2785).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2785 : v0_2785.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2785)).map Compressed.up0 ++
      (L0Factor 0 2785).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_0 : fastSlice0_2785 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_1 : fastSlice0_2785 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_2 : fastSlice0_2785 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_3 : fastSlice0_2785 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_4 : fastSlice0_2785 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_5 : fastSlice0_2785 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_6 : fastSlice0_2785 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_7 : fastSlice0_2785 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_8 : fastSlice0_2785 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_9 : fastSlice0_2785 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_10 : fastSlice0_2785 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_11 : fastSlice0_2785 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_12 : fastSlice0_2785 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_13 : fastSlice0_2785 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_14 : fastSlice0_2785 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_15 : fastSlice0_2785 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_16 : fastSlice0_2785 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_17 : fastSlice0_2785 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_18 : fastSlice0_2785 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_19 : fastSlice0_2785 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_20 : fastSlice0_2785 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_21 : fastSlice0_2785 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_22 : fastSlice0_2785 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_23 : fastSlice0_2785 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_24 : fastSlice0_2785 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_25 : fastSlice0_2785 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_26 : fastSlice0_2785 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_27 : fastSlice0_2785 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_28 : fastSlice0_2785 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_29 : fastSlice0_2785 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_30 : fastSlice0_2785 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_31 : fastSlice0_2785 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_32 : fastSlice0_2785 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_33 : fastSlice0_2785 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_34 : fastSlice0_2785 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_35 : fastSlice0_2785 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_36 : fastSlice0_2785 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_37 : fastSlice0_2785 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_38 : fastSlice0_2785 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_39 : fastSlice0_2785 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2785_40 : fastSlice0_2785 40 = true := by
  decide +kernel

public theorem point0_2785 : stepCheck 0 2785 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2785 u0_2785 v0_2785
    left0_2785 right0_2785
  intro b
  rw [sliceEq0_2785]
  fin_cases b
  · exact slice0_2785_0
  · exact slice0_2785_1
  · exact slice0_2785_2
  · exact slice0_2785_3
  · exact slice0_2785_4
  · exact slice0_2785_5
  · exact slice0_2785_6
  · exact slice0_2785_7
  · exact slice0_2785_8
  · exact slice0_2785_9
  · exact slice0_2785_10
  · exact slice0_2785_11
  · exact slice0_2785_12
  · exact slice0_2785_13
  · exact slice0_2785_14
  · exact slice0_2785_15
  · exact slice0_2785_16
  · exact slice0_2785_17
  · exact slice0_2785_18
  · exact slice0_2785_19
  · exact slice0_2785_20
  · exact slice0_2785_21
  · exact slice0_2785_22
  · exact slice0_2785_23
  · exact slice0_2785_24
  · exact slice0_2785_25
  · exact slice0_2785_26
  · exact slice0_2785_27
  · exact slice0_2785_28
  · exact slice0_2785_29
  · exact slice0_2785_30
  · exact slice0_2785_31
  · exact slice0_2785_32
  · exact slice0_2785_33
  · exact slice0_2785_34
  · exact slice0_2785_35
  · exact slice0_2785_36
  · exact slice0_2785_37
  · exact slice0_2785_38
  · exact slice0_2785_39
  · exact slice0_2785_40

set_option maxHeartbeats 1600000 in
public theorem point0_2786 : stepCheck 0 2786 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2787 : stepCheck 0 2787 := by
  left
  decide +kernel

private def u0_2788 : List (Fin 96) := [0, 51, 12, 76]
private def v0_2788 : List (Fin 96) := [58, 64, 50, 4, 10, 30, 4, 94, 29, 37, 25, 29, 42, 86]
private def lhs0_2788 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map76 (x))))
private def rhs0_2788 (x : Nat) : Nat := Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map30 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map94 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map86 (x))))))))))))))
private theorem lhs0_2788_eq : lhs0_2788 = Compressed.eval u0_2788 := by rfl
private theorem rhs0_2788_eq : rhs0_2788 = Compressed.eval v0_2788 := by rfl
private def fastSlice0_2788 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2788 ((100 * b.val + x.val) % 4060) =
      rhs0_2788 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2788 (b : Fin 41) :
    Compressed.slice u0_2788 v0_2788 b = fastSlice0_2788 b := by
  simp only [Compressed.slice, fastSlice0_2788, lhs0_2788_eq, rhs0_2788_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2788 : u0_2788.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2788).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2788 : v0_2788.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2788)).map Compressed.up0 ++
      (L0Factor 0 2788).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_0 : fastSlice0_2788 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_1 : fastSlice0_2788 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_2 : fastSlice0_2788 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_3 : fastSlice0_2788 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_4 : fastSlice0_2788 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_5 : fastSlice0_2788 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_6 : fastSlice0_2788 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_7 : fastSlice0_2788 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_8 : fastSlice0_2788 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_9 : fastSlice0_2788 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_10 : fastSlice0_2788 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_11 : fastSlice0_2788 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_12 : fastSlice0_2788 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_13 : fastSlice0_2788 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_14 : fastSlice0_2788 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_15 : fastSlice0_2788 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_16 : fastSlice0_2788 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_17 : fastSlice0_2788 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_18 : fastSlice0_2788 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_19 : fastSlice0_2788 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_20 : fastSlice0_2788 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_21 : fastSlice0_2788 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_22 : fastSlice0_2788 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_23 : fastSlice0_2788 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_24 : fastSlice0_2788 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_25 : fastSlice0_2788 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_26 : fastSlice0_2788 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_27 : fastSlice0_2788 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_28 : fastSlice0_2788 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_29 : fastSlice0_2788 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_30 : fastSlice0_2788 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_31 : fastSlice0_2788 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_32 : fastSlice0_2788 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_33 : fastSlice0_2788 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_34 : fastSlice0_2788 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_35 : fastSlice0_2788 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_36 : fastSlice0_2788 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_37 : fastSlice0_2788 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_38 : fastSlice0_2788 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_39 : fastSlice0_2788 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2788_40 : fastSlice0_2788 40 = true := by
  decide +kernel

public theorem point0_2788 : stepCheck 0 2788 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2788 u0_2788 v0_2788
    left0_2788 right0_2788
  intro b
  rw [sliceEq0_2788]
  fin_cases b
  · exact slice0_2788_0
  · exact slice0_2788_1
  · exact slice0_2788_2
  · exact slice0_2788_3
  · exact slice0_2788_4
  · exact slice0_2788_5
  · exact slice0_2788_6
  · exact slice0_2788_7
  · exact slice0_2788_8
  · exact slice0_2788_9
  · exact slice0_2788_10
  · exact slice0_2788_11
  · exact slice0_2788_12
  · exact slice0_2788_13
  · exact slice0_2788_14
  · exact slice0_2788_15
  · exact slice0_2788_16
  · exact slice0_2788_17
  · exact slice0_2788_18
  · exact slice0_2788_19
  · exact slice0_2788_20
  · exact slice0_2788_21
  · exact slice0_2788_22
  · exact slice0_2788_23
  · exact slice0_2788_24
  · exact slice0_2788_25
  · exact slice0_2788_26
  · exact slice0_2788_27
  · exact slice0_2788_28
  · exact slice0_2788_29
  · exact slice0_2788_30
  · exact slice0_2788_31
  · exact slice0_2788_32
  · exact slice0_2788_33
  · exact slice0_2788_34
  · exact slice0_2788_35
  · exact slice0_2788_36
  · exact slice0_2788_37
  · exact slice0_2788_38
  · exact slice0_2788_39
  · exact slice0_2788_40

set_option maxHeartbeats 1600000 in
public theorem point0_2789 : stepCheck 0 2789 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
