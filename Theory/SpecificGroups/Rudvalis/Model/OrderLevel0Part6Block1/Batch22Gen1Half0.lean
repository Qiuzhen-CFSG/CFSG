module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 22, generator 1, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u1_3200 : List (Fin 96) := [75, 33, 21, 60]
private def v1_3200 : List (Fin 96) := [67, 63, 33, 60, 11, 4, 10, 10, 5, 27, 59, 59, 81]
private def lhs1_3200 (x : Nat) : Nat := Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map60 (x))))
private def rhs1_3200 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map81 (x)))))))))))))
private theorem lhs1_3200_eq : lhs1_3200 = Compressed.eval u1_3200 := by rfl
private theorem rhs1_3200_eq : rhs1_3200 = Compressed.eval v1_3200 := by rfl
private def fastSlice1_3200 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3200 ((100 * b.val + x.val) % 4060) =
      rhs1_3200 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3200 (b : Fin 41) :
    Compressed.slice u1_3200 v1_3200 b = fastSlice1_3200 b := by
  simp only [Compressed.slice, fastSlice1_3200, lhs1_3200_eq, rhs1_3200_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3200 : u1_3200.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3200).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3200 : v1_3200.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3200)).map Compressed.up0 ++
      (L0Factor 1 3200).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_0 : fastSlice1_3200 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_1 : fastSlice1_3200 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_2 : fastSlice1_3200 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_3 : fastSlice1_3200 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_4 : fastSlice1_3200 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_5 : fastSlice1_3200 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_6 : fastSlice1_3200 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_7 : fastSlice1_3200 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_8 : fastSlice1_3200 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_9 : fastSlice1_3200 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_10 : fastSlice1_3200 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_11 : fastSlice1_3200 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_12 : fastSlice1_3200 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_13 : fastSlice1_3200 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_14 : fastSlice1_3200 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_15 : fastSlice1_3200 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_16 : fastSlice1_3200 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_17 : fastSlice1_3200 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_18 : fastSlice1_3200 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_19 : fastSlice1_3200 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_20 : fastSlice1_3200 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_21 : fastSlice1_3200 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_22 : fastSlice1_3200 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_23 : fastSlice1_3200 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_24 : fastSlice1_3200 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_25 : fastSlice1_3200 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_26 : fastSlice1_3200 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_27 : fastSlice1_3200 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_28 : fastSlice1_3200 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_29 : fastSlice1_3200 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_30 : fastSlice1_3200 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_31 : fastSlice1_3200 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_32 : fastSlice1_3200 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_33 : fastSlice1_3200 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_34 : fastSlice1_3200 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_35 : fastSlice1_3200 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_36 : fastSlice1_3200 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_37 : fastSlice1_3200 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_38 : fastSlice1_3200 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_39 : fastSlice1_3200 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3200_40 : fastSlice1_3200 40 = true := by
  decide +kernel

public theorem point1_3200 : stepCheck 1 3200 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3200 u1_3200 v1_3200
    left1_3200 right1_3200
  intro b
  rw [sliceEq1_3200]
  fin_cases b
  · exact slice1_3200_0
  · exact slice1_3200_1
  · exact slice1_3200_2
  · exact slice1_3200_3
  · exact slice1_3200_4
  · exact slice1_3200_5
  · exact slice1_3200_6
  · exact slice1_3200_7
  · exact slice1_3200_8
  · exact slice1_3200_9
  · exact slice1_3200_10
  · exact slice1_3200_11
  · exact slice1_3200_12
  · exact slice1_3200_13
  · exact slice1_3200_14
  · exact slice1_3200_15
  · exact slice1_3200_16
  · exact slice1_3200_17
  · exact slice1_3200_18
  · exact slice1_3200_19
  · exact slice1_3200_20
  · exact slice1_3200_21
  · exact slice1_3200_22
  · exact slice1_3200_23
  · exact slice1_3200_24
  · exact slice1_3200_25
  · exact slice1_3200_26
  · exact slice1_3200_27
  · exact slice1_3200_28
  · exact slice1_3200_29
  · exact slice1_3200_30
  · exact slice1_3200_31
  · exact slice1_3200_32
  · exact slice1_3200_33
  · exact slice1_3200_34
  · exact slice1_3200_35
  · exact slice1_3200_36
  · exact slice1_3200_37
  · exact slice1_3200_38
  · exact slice1_3200_39
  · exact slice1_3200_40

set_option maxHeartbeats 1600000 in
public theorem point1_3201 : stepCheck 1 3201 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3202 : stepCheck 1 3202 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3203 : stepCheck 1 3203 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3204 : stepCheck 1 3204 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3205 : stepCheck 1 3205 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3206 : stepCheck 1 3206 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3207 : stepCheck 1 3207 := by
  left
  decide +kernel

private def u1_3208 : List (Fin 96) := [19, 50, 64, 60]
private def v1_3208 : List (Fin 96) := [14, 19, 21, 58, 3, 6, 36, 36, 31, 71, 7]
private def lhs1_3208 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map60 (x))))
private def rhs1_3208 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map7 (x)))))))))))
private theorem lhs1_3208_eq : lhs1_3208 = Compressed.eval u1_3208 := by rfl
private theorem rhs1_3208_eq : rhs1_3208 = Compressed.eval v1_3208 := by rfl
private def fastSlice1_3208 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3208 ((100 * b.val + x.val) % 4060) =
      rhs1_3208 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3208 (b : Fin 41) :
    Compressed.slice u1_3208 v1_3208 b = fastSlice1_3208 b := by
  simp only [Compressed.slice, fastSlice1_3208, lhs1_3208_eq, rhs1_3208_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3208 : u1_3208.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3208).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3208 : v1_3208.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3208)).map Compressed.up0 ++
      (L0Factor 1 3208).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_0 : fastSlice1_3208 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_1 : fastSlice1_3208 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_2 : fastSlice1_3208 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_3 : fastSlice1_3208 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_4 : fastSlice1_3208 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_5 : fastSlice1_3208 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_6 : fastSlice1_3208 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_7 : fastSlice1_3208 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_8 : fastSlice1_3208 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_9 : fastSlice1_3208 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_10 : fastSlice1_3208 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_11 : fastSlice1_3208 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_12 : fastSlice1_3208 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_13 : fastSlice1_3208 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_14 : fastSlice1_3208 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_15 : fastSlice1_3208 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_16 : fastSlice1_3208 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_17 : fastSlice1_3208 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_18 : fastSlice1_3208 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_19 : fastSlice1_3208 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_20 : fastSlice1_3208 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_21 : fastSlice1_3208 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_22 : fastSlice1_3208 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_23 : fastSlice1_3208 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_24 : fastSlice1_3208 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_25 : fastSlice1_3208 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_26 : fastSlice1_3208 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_27 : fastSlice1_3208 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_28 : fastSlice1_3208 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_29 : fastSlice1_3208 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_30 : fastSlice1_3208 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_31 : fastSlice1_3208 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_32 : fastSlice1_3208 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_33 : fastSlice1_3208 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_34 : fastSlice1_3208 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_35 : fastSlice1_3208 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_36 : fastSlice1_3208 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_37 : fastSlice1_3208 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_38 : fastSlice1_3208 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_39 : fastSlice1_3208 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3208_40 : fastSlice1_3208 40 = true := by
  decide +kernel

public theorem point1_3208 : stepCheck 1 3208 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3208 u1_3208 v1_3208
    left1_3208 right1_3208
  intro b
  rw [sliceEq1_3208]
  fin_cases b
  · exact slice1_3208_0
  · exact slice1_3208_1
  · exact slice1_3208_2
  · exact slice1_3208_3
  · exact slice1_3208_4
  · exact slice1_3208_5
  · exact slice1_3208_6
  · exact slice1_3208_7
  · exact slice1_3208_8
  · exact slice1_3208_9
  · exact slice1_3208_10
  · exact slice1_3208_11
  · exact slice1_3208_12
  · exact slice1_3208_13
  · exact slice1_3208_14
  · exact slice1_3208_15
  · exact slice1_3208_16
  · exact slice1_3208_17
  · exact slice1_3208_18
  · exact slice1_3208_19
  · exact slice1_3208_20
  · exact slice1_3208_21
  · exact slice1_3208_22
  · exact slice1_3208_23
  · exact slice1_3208_24
  · exact slice1_3208_25
  · exact slice1_3208_26
  · exact slice1_3208_27
  · exact slice1_3208_28
  · exact slice1_3208_29
  · exact slice1_3208_30
  · exact slice1_3208_31
  · exact slice1_3208_32
  · exact slice1_3208_33
  · exact slice1_3208_34
  · exact slice1_3208_35
  · exact slice1_3208_36
  · exact slice1_3208_37
  · exact slice1_3208_38
  · exact slice1_3208_39
  · exact slice1_3208_40

set_option maxHeartbeats 1600000 in
public theorem point1_3209 : stepCheck 1 3209 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
