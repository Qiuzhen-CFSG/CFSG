module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 18, generator 0, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point0_2640 : stepCheck 0 2640 := by
  left
  decide +kernel

private def u0_2641 : List (Fin 96) := [0, 50, 77, 95]
private def v0_2641 : List (Fin 96) := [21, 63, 33, 11, 11, 16, 27, 18, 32, 81]
private def lhs0_2641 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map95 (x))))
private def rhs0_2641 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map81 (x))))))))))
private theorem lhs0_2641_eq : lhs0_2641 = Compressed.eval u0_2641 := by rfl
private theorem rhs0_2641_eq : rhs0_2641 = Compressed.eval v0_2641 := by rfl
private def fastSlice0_2641 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2641 ((100 * b.val + x.val) % 4060) =
      rhs0_2641 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2641 (b : Fin 41) :
    Compressed.slice u0_2641 v0_2641 b = fastSlice0_2641 b := by
  simp only [Compressed.slice, fastSlice0_2641, lhs0_2641_eq, rhs0_2641_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2641 : u0_2641.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2641).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2641 : v0_2641.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2641)).map Compressed.up0 ++
      (L0Factor 0 2641).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_0 : fastSlice0_2641 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_1 : fastSlice0_2641 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_2 : fastSlice0_2641 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_3 : fastSlice0_2641 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_4 : fastSlice0_2641 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_5 : fastSlice0_2641 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_6 : fastSlice0_2641 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_7 : fastSlice0_2641 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_8 : fastSlice0_2641 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_9 : fastSlice0_2641 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_10 : fastSlice0_2641 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_11 : fastSlice0_2641 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_12 : fastSlice0_2641 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_13 : fastSlice0_2641 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_14 : fastSlice0_2641 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_15 : fastSlice0_2641 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_16 : fastSlice0_2641 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_17 : fastSlice0_2641 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_18 : fastSlice0_2641 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_19 : fastSlice0_2641 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_20 : fastSlice0_2641 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_21 : fastSlice0_2641 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_22 : fastSlice0_2641 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_23 : fastSlice0_2641 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_24 : fastSlice0_2641 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_25 : fastSlice0_2641 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_26 : fastSlice0_2641 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_27 : fastSlice0_2641 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_28 : fastSlice0_2641 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_29 : fastSlice0_2641 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_30 : fastSlice0_2641 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_31 : fastSlice0_2641 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_32 : fastSlice0_2641 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_33 : fastSlice0_2641 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_34 : fastSlice0_2641 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_35 : fastSlice0_2641 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_36 : fastSlice0_2641 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_37 : fastSlice0_2641 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_38 : fastSlice0_2641 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_39 : fastSlice0_2641 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2641_40 : fastSlice0_2641 40 = true := by
  decide +kernel

public theorem point0_2641 : stepCheck 0 2641 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2641 u0_2641 v0_2641
    left0_2641 right0_2641
  intro b
  rw [sliceEq0_2641]
  fin_cases b
  · exact slice0_2641_0
  · exact slice0_2641_1
  · exact slice0_2641_2
  · exact slice0_2641_3
  · exact slice0_2641_4
  · exact slice0_2641_5
  · exact slice0_2641_6
  · exact slice0_2641_7
  · exact slice0_2641_8
  · exact slice0_2641_9
  · exact slice0_2641_10
  · exact slice0_2641_11
  · exact slice0_2641_12
  · exact slice0_2641_13
  · exact slice0_2641_14
  · exact slice0_2641_15
  · exact slice0_2641_16
  · exact slice0_2641_17
  · exact slice0_2641_18
  · exact slice0_2641_19
  · exact slice0_2641_20
  · exact slice0_2641_21
  · exact slice0_2641_22
  · exact slice0_2641_23
  · exact slice0_2641_24
  · exact slice0_2641_25
  · exact slice0_2641_26
  · exact slice0_2641_27
  · exact slice0_2641_28
  · exact slice0_2641_29
  · exact slice0_2641_30
  · exact slice0_2641_31
  · exact slice0_2641_32
  · exact slice0_2641_33
  · exact slice0_2641_34
  · exact slice0_2641_35
  · exact slice0_2641_36
  · exact slice0_2641_37
  · exact slice0_2641_38
  · exact slice0_2641_39
  · exact slice0_2641_40

private def u0_2642 : List (Fin 96) := [87, 77, 95]
private def v0_2642 : List (Fin 96) := [14, 46, 24, 46, 4, 79, 10, 91, 59, 48, 81]
private def lhs0_2642 (x : Nat) : Nat := Part6Nat.force Compressed.map87 (Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map95 (x)))
private def rhs0_2642 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map91 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map48 (Part6Nat.force Compressed.map81 (x)))))))))))
private theorem lhs0_2642_eq : lhs0_2642 = Compressed.eval u0_2642 := by rfl
private theorem rhs0_2642_eq : rhs0_2642 = Compressed.eval v0_2642 := by rfl
private def fastSlice0_2642 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2642 ((100 * b.val + x.val) % 4060) =
      rhs0_2642 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2642 (b : Fin 41) :
    Compressed.slice u0_2642 v0_2642 b = fastSlice0_2642 b := by
  simp only [Compressed.slice, fastSlice0_2642, lhs0_2642_eq, rhs0_2642_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2642 : u0_2642.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2642).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2642 : v0_2642.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2642)).map Compressed.up0 ++
      (L0Factor 0 2642).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_0 : fastSlice0_2642 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_1 : fastSlice0_2642 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_2 : fastSlice0_2642 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_3 : fastSlice0_2642 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_4 : fastSlice0_2642 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_5 : fastSlice0_2642 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_6 : fastSlice0_2642 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_7 : fastSlice0_2642 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_8 : fastSlice0_2642 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_9 : fastSlice0_2642 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_10 : fastSlice0_2642 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_11 : fastSlice0_2642 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_12 : fastSlice0_2642 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_13 : fastSlice0_2642 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_14 : fastSlice0_2642 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_15 : fastSlice0_2642 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_16 : fastSlice0_2642 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_17 : fastSlice0_2642 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_18 : fastSlice0_2642 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_19 : fastSlice0_2642 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_20 : fastSlice0_2642 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_21 : fastSlice0_2642 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_22 : fastSlice0_2642 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_23 : fastSlice0_2642 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_24 : fastSlice0_2642 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_25 : fastSlice0_2642 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_26 : fastSlice0_2642 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_27 : fastSlice0_2642 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_28 : fastSlice0_2642 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_29 : fastSlice0_2642 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_30 : fastSlice0_2642 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_31 : fastSlice0_2642 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_32 : fastSlice0_2642 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_33 : fastSlice0_2642 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_34 : fastSlice0_2642 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_35 : fastSlice0_2642 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_36 : fastSlice0_2642 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_37 : fastSlice0_2642 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_38 : fastSlice0_2642 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_39 : fastSlice0_2642 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2642_40 : fastSlice0_2642 40 = true := by
  decide +kernel

public theorem point0_2642 : stepCheck 0 2642 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2642 u0_2642 v0_2642
    left0_2642 right0_2642
  intro b
  rw [sliceEq0_2642]
  fin_cases b
  · exact slice0_2642_0
  · exact slice0_2642_1
  · exact slice0_2642_2
  · exact slice0_2642_3
  · exact slice0_2642_4
  · exact slice0_2642_5
  · exact slice0_2642_6
  · exact slice0_2642_7
  · exact slice0_2642_8
  · exact slice0_2642_9
  · exact slice0_2642_10
  · exact slice0_2642_11
  · exact slice0_2642_12
  · exact slice0_2642_13
  · exact slice0_2642_14
  · exact slice0_2642_15
  · exact slice0_2642_16
  · exact slice0_2642_17
  · exact slice0_2642_18
  · exact slice0_2642_19
  · exact slice0_2642_20
  · exact slice0_2642_21
  · exact slice0_2642_22
  · exact slice0_2642_23
  · exact slice0_2642_24
  · exact slice0_2642_25
  · exact slice0_2642_26
  · exact slice0_2642_27
  · exact slice0_2642_28
  · exact slice0_2642_29
  · exact slice0_2642_30
  · exact slice0_2642_31
  · exact slice0_2642_32
  · exact slice0_2642_33
  · exact slice0_2642_34
  · exact slice0_2642_35
  · exact slice0_2642_36
  · exact slice0_2642_37
  · exact slice0_2642_38
  · exact slice0_2642_39
  · exact slice0_2642_40

set_option maxHeartbeats 1600000 in
public theorem point0_2643 : stepCheck 0 2643 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2644 : stepCheck 0 2644 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2645 : stepCheck 0 2645 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2646 : stepCheck 0 2646 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2647 : stepCheck 0 2647 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2648 : stepCheck 0 2648 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2649 : stepCheck 0 2649 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
