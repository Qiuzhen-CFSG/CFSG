module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 23, generator 1, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point1_3340 : stepCheck 1 3340 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3341 : stepCheck 1 3341 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3342 : stepCheck 1 3342 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3343 : stepCheck 1 3343 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3344 : stepCheck 1 3344 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3345 : stepCheck 1 3345 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3346 : stepCheck 1 3346 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3347 : stepCheck 1 3347 := by
  left
  decide +kernel

private def u1_3348 : List (Fin 96) := [63, 21, 63, 3]
private def v1_3348 : List (Fin 96) := [14, 33, 46, 12, 60, 11, 4, 8, 5, 80, 45, 29, 23, 27, 42, 47]
private def lhs1_3348 (x : Nat) : Nat := Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map3 (x))))
private def rhs1_3348 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map47 (x))))))))))))))))
private theorem lhs1_3348_eq : lhs1_3348 = Compressed.eval u1_3348 := by rfl
private theorem rhs1_3348_eq : rhs1_3348 = Compressed.eval v1_3348 := by rfl
private def fastSlice1_3348 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3348 ((100 * b.val + x.val) % 4060) =
      rhs1_3348 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3348 (b : Fin 41) :
    Compressed.slice u1_3348 v1_3348 b = fastSlice1_3348 b := by
  simp only [Compressed.slice, fastSlice1_3348, lhs1_3348_eq, rhs1_3348_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3348 : u1_3348.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3348).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3348 : v1_3348.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3348)).map Compressed.up0 ++
      (L0Factor 1 3348).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_0 : fastSlice1_3348 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_1 : fastSlice1_3348 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_2 : fastSlice1_3348 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_3 : fastSlice1_3348 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_4 : fastSlice1_3348 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_5 : fastSlice1_3348 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_6 : fastSlice1_3348 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_7 : fastSlice1_3348 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_8 : fastSlice1_3348 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_9 : fastSlice1_3348 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_10 : fastSlice1_3348 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_11 : fastSlice1_3348 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_12 : fastSlice1_3348 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_13 : fastSlice1_3348 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_14 : fastSlice1_3348 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_15 : fastSlice1_3348 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_16 : fastSlice1_3348 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_17 : fastSlice1_3348 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_18 : fastSlice1_3348 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_19 : fastSlice1_3348 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_20 : fastSlice1_3348 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_21 : fastSlice1_3348 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_22 : fastSlice1_3348 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_23 : fastSlice1_3348 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_24 : fastSlice1_3348 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_25 : fastSlice1_3348 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_26 : fastSlice1_3348 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_27 : fastSlice1_3348 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_28 : fastSlice1_3348 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_29 : fastSlice1_3348 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_30 : fastSlice1_3348 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_31 : fastSlice1_3348 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_32 : fastSlice1_3348 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_33 : fastSlice1_3348 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_34 : fastSlice1_3348 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_35 : fastSlice1_3348 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_36 : fastSlice1_3348 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_37 : fastSlice1_3348 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_38 : fastSlice1_3348 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_39 : fastSlice1_3348 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3348_40 : fastSlice1_3348 40 = true := by
  decide +kernel

public theorem point1_3348 : stepCheck 1 3348 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3348 u1_3348 v1_3348
    left1_3348 right1_3348
  intro b
  rw [sliceEq1_3348]
  fin_cases b
  · exact slice1_3348_0
  · exact slice1_3348_1
  · exact slice1_3348_2
  · exact slice1_3348_3
  · exact slice1_3348_4
  · exact slice1_3348_5
  · exact slice1_3348_6
  · exact slice1_3348_7
  · exact slice1_3348_8
  · exact slice1_3348_9
  · exact slice1_3348_10
  · exact slice1_3348_11
  · exact slice1_3348_12
  · exact slice1_3348_13
  · exact slice1_3348_14
  · exact slice1_3348_15
  · exact slice1_3348_16
  · exact slice1_3348_17
  · exact slice1_3348_18
  · exact slice1_3348_19
  · exact slice1_3348_20
  · exact slice1_3348_21
  · exact slice1_3348_22
  · exact slice1_3348_23
  · exact slice1_3348_24
  · exact slice1_3348_25
  · exact slice1_3348_26
  · exact slice1_3348_27
  · exact slice1_3348_28
  · exact slice1_3348_29
  · exact slice1_3348_30
  · exact slice1_3348_31
  · exact slice1_3348_32
  · exact slice1_3348_33
  · exact slice1_3348_34
  · exact slice1_3348_35
  · exact slice1_3348_36
  · exact slice1_3348_37
  · exact slice1_3348_38
  · exact slice1_3348_39
  · exact slice1_3348_40

private def u1_3349 : List (Fin 96) := [77, 19, 76]
private def v1_3349 : List (Fin 96) := [14, 82, 21, 12, 6, 16, 16, 5, 27, 31, 71, 42, 8, 6, 73]
private def lhs1_3349 (x : Nat) : Nat := Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map76 (x)))
private def rhs1_3349 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map73 (x)))))))))))))))
private theorem lhs1_3349_eq : lhs1_3349 = Compressed.eval u1_3349 := by rfl
private theorem rhs1_3349_eq : rhs1_3349 = Compressed.eval v1_3349 := by rfl
private def fastSlice1_3349 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3349 ((100 * b.val + x.val) % 4060) =
      rhs1_3349 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3349 (b : Fin 41) :
    Compressed.slice u1_3349 v1_3349 b = fastSlice1_3349 b := by
  simp only [Compressed.slice, fastSlice1_3349, lhs1_3349_eq, rhs1_3349_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3349 : u1_3349.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3349).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3349 : v1_3349.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3349)).map Compressed.up0 ++
      (L0Factor 1 3349).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_0 : fastSlice1_3349 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_1 : fastSlice1_3349 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_2 : fastSlice1_3349 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_3 : fastSlice1_3349 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_4 : fastSlice1_3349 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_5 : fastSlice1_3349 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_6 : fastSlice1_3349 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_7 : fastSlice1_3349 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_8 : fastSlice1_3349 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_9 : fastSlice1_3349 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_10 : fastSlice1_3349 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_11 : fastSlice1_3349 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_12 : fastSlice1_3349 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_13 : fastSlice1_3349 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_14 : fastSlice1_3349 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_15 : fastSlice1_3349 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_16 : fastSlice1_3349 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_17 : fastSlice1_3349 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_18 : fastSlice1_3349 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_19 : fastSlice1_3349 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_20 : fastSlice1_3349 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_21 : fastSlice1_3349 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_22 : fastSlice1_3349 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_23 : fastSlice1_3349 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_24 : fastSlice1_3349 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_25 : fastSlice1_3349 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_26 : fastSlice1_3349 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_27 : fastSlice1_3349 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_28 : fastSlice1_3349 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_29 : fastSlice1_3349 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_30 : fastSlice1_3349 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_31 : fastSlice1_3349 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_32 : fastSlice1_3349 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_33 : fastSlice1_3349 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_34 : fastSlice1_3349 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_35 : fastSlice1_3349 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_36 : fastSlice1_3349 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_37 : fastSlice1_3349 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_38 : fastSlice1_3349 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_39 : fastSlice1_3349 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3349_40 : fastSlice1_3349 40 = true := by
  decide +kernel

public theorem point1_3349 : stepCheck 1 3349 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3349 u1_3349 v1_3349
    left1_3349 right1_3349
  intro b
  rw [sliceEq1_3349]
  fin_cases b
  · exact slice1_3349_0
  · exact slice1_3349_1
  · exact slice1_3349_2
  · exact slice1_3349_3
  · exact slice1_3349_4
  · exact slice1_3349_5
  · exact slice1_3349_6
  · exact slice1_3349_7
  · exact slice1_3349_8
  · exact slice1_3349_9
  · exact slice1_3349_10
  · exact slice1_3349_11
  · exact slice1_3349_12
  · exact slice1_3349_13
  · exact slice1_3349_14
  · exact slice1_3349_15
  · exact slice1_3349_16
  · exact slice1_3349_17
  · exact slice1_3349_18
  · exact slice1_3349_19
  · exact slice1_3349_20
  · exact slice1_3349_21
  · exact slice1_3349_22
  · exact slice1_3349_23
  · exact slice1_3349_24
  · exact slice1_3349_25
  · exact slice1_3349_26
  · exact slice1_3349_27
  · exact slice1_3349_28
  · exact slice1_3349_29
  · exact slice1_3349_30
  · exact slice1_3349_31
  · exact slice1_3349_32
  · exact slice1_3349_33
  · exact slice1_3349_34
  · exact slice1_3349_35
  · exact slice1_3349_36
  · exact slice1_3349_37
  · exact slice1_3349_38
  · exact slice1_3349_39
  · exact slice1_3349_40

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
