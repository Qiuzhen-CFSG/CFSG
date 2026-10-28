module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 21, generator 0, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point0_3070 : stepCheck 0 3070 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3071 : stepCheck 0 3071 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3072 : stepCheck 0 3072 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3073 : stepCheck 0 3073 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3074 : stepCheck 0 3074 := by
  left
  decide +kernel

private def u0_3075 : List (Fin 96) := [87, 66, 46]
private def v0_3075 : List (Fin 96) := [19, 46, 50, 19, 6, 10, 36, 94, 71, 81, 56]
private def lhs0_3075 (x : Nat) : Nat := Part6Nat.force Compressed.map87 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map46 (x)))
private def rhs0_3075 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map94 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map81 (Part6Nat.force Compressed.map56 (x)))))))))))
private theorem lhs0_3075_eq : lhs0_3075 = Compressed.eval u0_3075 := by rfl
private theorem rhs0_3075_eq : rhs0_3075 = Compressed.eval v0_3075 := by rfl
private def fastSlice0_3075 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3075 ((100 * b.val + x.val) % 4060) =
      rhs0_3075 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3075 (b : Fin 41) :
    Compressed.slice u0_3075 v0_3075 b = fastSlice0_3075 b := by
  simp only [Compressed.slice, fastSlice0_3075, lhs0_3075_eq, rhs0_3075_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3075 : u0_3075.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3075).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3075 : v0_3075.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3075)).map Compressed.up0 ++
      (L0Factor 0 3075).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_0 : fastSlice0_3075 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_1 : fastSlice0_3075 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_2 : fastSlice0_3075 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_3 : fastSlice0_3075 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_4 : fastSlice0_3075 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_5 : fastSlice0_3075 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_6 : fastSlice0_3075 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_7 : fastSlice0_3075 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_8 : fastSlice0_3075 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_9 : fastSlice0_3075 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_10 : fastSlice0_3075 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_11 : fastSlice0_3075 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_12 : fastSlice0_3075 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_13 : fastSlice0_3075 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_14 : fastSlice0_3075 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_15 : fastSlice0_3075 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_16 : fastSlice0_3075 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_17 : fastSlice0_3075 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_18 : fastSlice0_3075 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_19 : fastSlice0_3075 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_20 : fastSlice0_3075 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_21 : fastSlice0_3075 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_22 : fastSlice0_3075 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_23 : fastSlice0_3075 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_24 : fastSlice0_3075 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_25 : fastSlice0_3075 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_26 : fastSlice0_3075 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_27 : fastSlice0_3075 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_28 : fastSlice0_3075 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_29 : fastSlice0_3075 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_30 : fastSlice0_3075 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_31 : fastSlice0_3075 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_32 : fastSlice0_3075 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_33 : fastSlice0_3075 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_34 : fastSlice0_3075 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_35 : fastSlice0_3075 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_36 : fastSlice0_3075 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_37 : fastSlice0_3075 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_38 : fastSlice0_3075 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_39 : fastSlice0_3075 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3075_40 : fastSlice0_3075 40 = true := by
  decide +kernel

public theorem point0_3075 : stepCheck 0 3075 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3075 u0_3075 v0_3075
    left0_3075 right0_3075
  intro b
  rw [sliceEq0_3075]
  fin_cases b
  · exact slice0_3075_0
  · exact slice0_3075_1
  · exact slice0_3075_2
  · exact slice0_3075_3
  · exact slice0_3075_4
  · exact slice0_3075_5
  · exact slice0_3075_6
  · exact slice0_3075_7
  · exact slice0_3075_8
  · exact slice0_3075_9
  · exact slice0_3075_10
  · exact slice0_3075_11
  · exact slice0_3075_12
  · exact slice0_3075_13
  · exact slice0_3075_14
  · exact slice0_3075_15
  · exact slice0_3075_16
  · exact slice0_3075_17
  · exact slice0_3075_18
  · exact slice0_3075_19
  · exact slice0_3075_20
  · exact slice0_3075_21
  · exact slice0_3075_22
  · exact slice0_3075_23
  · exact slice0_3075_24
  · exact slice0_3075_25
  · exact slice0_3075_26
  · exact slice0_3075_27
  · exact slice0_3075_28
  · exact slice0_3075_29
  · exact slice0_3075_30
  · exact slice0_3075_31
  · exact slice0_3075_32
  · exact slice0_3075_33
  · exact slice0_3075_34
  · exact slice0_3075_35
  · exact slice0_3075_36
  · exact slice0_3075_37
  · exact slice0_3075_38
  · exact slice0_3075_39
  · exact slice0_3075_40

private def u0_3076 : List (Fin 96) := [67, 50, 33, 46]
private def v0_3076 : List (Fin 96) := [19, 50, 92, 11, 10, 11, 74, 18, 37]
private def lhs0_3076 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map46 (x))))
private def rhs0_3076 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map92 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map37 (x)))))))))
private theorem lhs0_3076_eq : lhs0_3076 = Compressed.eval u0_3076 := by rfl
private theorem rhs0_3076_eq : rhs0_3076 = Compressed.eval v0_3076 := by rfl
private def fastSlice0_3076 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_3076 ((100 * b.val + x.val) % 4060) =
      rhs0_3076 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_3076 (b : Fin 41) :
    Compressed.slice u0_3076 v0_3076 b = fastSlice0_3076 b := by
  simp only [Compressed.slice, fastSlice0_3076, lhs0_3076_eq, rhs0_3076_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_3076 : u0_3076.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3076).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_3076 : v0_3076.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3076)).map Compressed.up0 ++
      (L0Factor 0 3076).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_0 : fastSlice0_3076 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_1 : fastSlice0_3076 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_2 : fastSlice0_3076 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_3 : fastSlice0_3076 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_4 : fastSlice0_3076 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_5 : fastSlice0_3076 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_6 : fastSlice0_3076 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_7 : fastSlice0_3076 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_8 : fastSlice0_3076 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_9 : fastSlice0_3076 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_10 : fastSlice0_3076 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_11 : fastSlice0_3076 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_12 : fastSlice0_3076 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_13 : fastSlice0_3076 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_14 : fastSlice0_3076 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_15 : fastSlice0_3076 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_16 : fastSlice0_3076 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_17 : fastSlice0_3076 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_18 : fastSlice0_3076 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_19 : fastSlice0_3076 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_20 : fastSlice0_3076 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_21 : fastSlice0_3076 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_22 : fastSlice0_3076 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_23 : fastSlice0_3076 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_24 : fastSlice0_3076 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_25 : fastSlice0_3076 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_26 : fastSlice0_3076 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_27 : fastSlice0_3076 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_28 : fastSlice0_3076 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_29 : fastSlice0_3076 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_30 : fastSlice0_3076 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_31 : fastSlice0_3076 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_32 : fastSlice0_3076 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_33 : fastSlice0_3076 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_34 : fastSlice0_3076 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_35 : fastSlice0_3076 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_36 : fastSlice0_3076 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_37 : fastSlice0_3076 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_38 : fastSlice0_3076 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_39 : fastSlice0_3076 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_3076_40 : fastSlice0_3076 40 = true := by
  decide +kernel

public theorem point0_3076 : stepCheck 0 3076 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3076 u0_3076 v0_3076
    left0_3076 right0_3076
  intro b
  rw [sliceEq0_3076]
  fin_cases b
  · exact slice0_3076_0
  · exact slice0_3076_1
  · exact slice0_3076_2
  · exact slice0_3076_3
  · exact slice0_3076_4
  · exact slice0_3076_5
  · exact slice0_3076_6
  · exact slice0_3076_7
  · exact slice0_3076_8
  · exact slice0_3076_9
  · exact slice0_3076_10
  · exact slice0_3076_11
  · exact slice0_3076_12
  · exact slice0_3076_13
  · exact slice0_3076_14
  · exact slice0_3076_15
  · exact slice0_3076_16
  · exact slice0_3076_17
  · exact slice0_3076_18
  · exact slice0_3076_19
  · exact slice0_3076_20
  · exact slice0_3076_21
  · exact slice0_3076_22
  · exact slice0_3076_23
  · exact slice0_3076_24
  · exact slice0_3076_25
  · exact slice0_3076_26
  · exact slice0_3076_27
  · exact slice0_3076_28
  · exact slice0_3076_29
  · exact slice0_3076_30
  · exact slice0_3076_31
  · exact slice0_3076_32
  · exact slice0_3076_33
  · exact slice0_3076_34
  · exact slice0_3076_35
  · exact slice0_3076_36
  · exact slice0_3076_37
  · exact slice0_3076_38
  · exact slice0_3076_39
  · exact slice0_3076_40

set_option maxHeartbeats 1600000 in
public theorem point0_3077 : stepCheck 0 3077 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3078 : stepCheck 0 3078 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_3079 : stepCheck 0 3079 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
