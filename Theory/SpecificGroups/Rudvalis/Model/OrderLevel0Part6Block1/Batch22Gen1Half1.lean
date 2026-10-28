module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 22, generator 1, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u1_3210 : List (Fin 96) := [19, 21, 64, 60]
private def v1_3210 : List (Fin 96) := [21, 21, 82, 4, 4, 44, 30, 85, 48, 70, 61]
private def lhs1_3210 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map60 (x))))
private def rhs1_3210 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map44 (Part6Nat.force Compressed.map30 (Part6Nat.force Compressed.map85 (Part6Nat.force Compressed.map48 (Part6Nat.force Compressed.map70 (Part6Nat.force Compressed.map61 (x)))))))))))
private theorem lhs1_3210_eq : lhs1_3210 = Compressed.eval u1_3210 := by rfl
private theorem rhs1_3210_eq : rhs1_3210 = Compressed.eval v1_3210 := by rfl
private def fastSlice1_3210 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3210 ((100 * b.val + x.val) % 4060) =
      rhs1_3210 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3210 (b : Fin 41) :
    Compressed.slice u1_3210 v1_3210 b = fastSlice1_3210 b := by
  simp only [Compressed.slice, fastSlice1_3210, lhs1_3210_eq, rhs1_3210_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3210 : u1_3210.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3210).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3210 : v1_3210.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3210)).map Compressed.up0 ++
      (L0Factor 1 3210).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_0 : fastSlice1_3210 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_1 : fastSlice1_3210 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_2 : fastSlice1_3210 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_3 : fastSlice1_3210 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_4 : fastSlice1_3210 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_5 : fastSlice1_3210 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_6 : fastSlice1_3210 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_7 : fastSlice1_3210 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_8 : fastSlice1_3210 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_9 : fastSlice1_3210 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_10 : fastSlice1_3210 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_11 : fastSlice1_3210 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_12 : fastSlice1_3210 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_13 : fastSlice1_3210 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_14 : fastSlice1_3210 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_15 : fastSlice1_3210 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_16 : fastSlice1_3210 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_17 : fastSlice1_3210 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_18 : fastSlice1_3210 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_19 : fastSlice1_3210 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_20 : fastSlice1_3210 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_21 : fastSlice1_3210 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_22 : fastSlice1_3210 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_23 : fastSlice1_3210 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_24 : fastSlice1_3210 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_25 : fastSlice1_3210 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_26 : fastSlice1_3210 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_27 : fastSlice1_3210 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_28 : fastSlice1_3210 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_29 : fastSlice1_3210 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_30 : fastSlice1_3210 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_31 : fastSlice1_3210 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_32 : fastSlice1_3210 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_33 : fastSlice1_3210 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_34 : fastSlice1_3210 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_35 : fastSlice1_3210 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_36 : fastSlice1_3210 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_37 : fastSlice1_3210 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_38 : fastSlice1_3210 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_39 : fastSlice1_3210 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3210_40 : fastSlice1_3210 40 = true := by
  decide +kernel

public theorem point1_3210 : stepCheck 1 3210 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3210 u1_3210 v1_3210
    left1_3210 right1_3210
  intro b
  rw [sliceEq1_3210]
  fin_cases b
  · exact slice1_3210_0
  · exact slice1_3210_1
  · exact slice1_3210_2
  · exact slice1_3210_3
  · exact slice1_3210_4
  · exact slice1_3210_5
  · exact slice1_3210_6
  · exact slice1_3210_7
  · exact slice1_3210_8
  · exact slice1_3210_9
  · exact slice1_3210_10
  · exact slice1_3210_11
  · exact slice1_3210_12
  · exact slice1_3210_13
  · exact slice1_3210_14
  · exact slice1_3210_15
  · exact slice1_3210_16
  · exact slice1_3210_17
  · exact slice1_3210_18
  · exact slice1_3210_19
  · exact slice1_3210_20
  · exact slice1_3210_21
  · exact slice1_3210_22
  · exact slice1_3210_23
  · exact slice1_3210_24
  · exact slice1_3210_25
  · exact slice1_3210_26
  · exact slice1_3210_27
  · exact slice1_3210_28
  · exact slice1_3210_29
  · exact slice1_3210_30
  · exact slice1_3210_31
  · exact slice1_3210_32
  · exact slice1_3210_33
  · exact slice1_3210_34
  · exact slice1_3210_35
  · exact slice1_3210_36
  · exact slice1_3210_37
  · exact slice1_3210_38
  · exact slice1_3210_39
  · exact slice1_3210_40

private def u1_3211 : List (Fin 96) := [12, 51, 64, 60]
private def v1_3211 : List (Fin 96) := [0, 46, 50, 69, 4, 8, 5, 8, 80, 74, 37, 25, 74, 85, 31, 56]
private def lhs1_3211 (x : Nat) : Nat := Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map60 (x))))
private def rhs1_3211 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map85 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map56 (x))))))))))))))))
private theorem lhs1_3211_eq : lhs1_3211 = Compressed.eval u1_3211 := by rfl
private theorem rhs1_3211_eq : rhs1_3211 = Compressed.eval v1_3211 := by rfl
private def fastSlice1_3211 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3211 ((100 * b.val + x.val) % 4060) =
      rhs1_3211 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3211 (b : Fin 41) :
    Compressed.slice u1_3211 v1_3211 b = fastSlice1_3211 b := by
  simp only [Compressed.slice, fastSlice1_3211, lhs1_3211_eq, rhs1_3211_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3211 : u1_3211.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3211).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3211 : v1_3211.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3211)).map Compressed.up0 ++
      (L0Factor 1 3211).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_0 : fastSlice1_3211 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_1 : fastSlice1_3211 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_2 : fastSlice1_3211 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_3 : fastSlice1_3211 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_4 : fastSlice1_3211 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_5 : fastSlice1_3211 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_6 : fastSlice1_3211 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_7 : fastSlice1_3211 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_8 : fastSlice1_3211 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_9 : fastSlice1_3211 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_10 : fastSlice1_3211 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_11 : fastSlice1_3211 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_12 : fastSlice1_3211 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_13 : fastSlice1_3211 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_14 : fastSlice1_3211 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_15 : fastSlice1_3211 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_16 : fastSlice1_3211 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_17 : fastSlice1_3211 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_18 : fastSlice1_3211 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_19 : fastSlice1_3211 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_20 : fastSlice1_3211 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_21 : fastSlice1_3211 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_22 : fastSlice1_3211 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_23 : fastSlice1_3211 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_24 : fastSlice1_3211 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_25 : fastSlice1_3211 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_26 : fastSlice1_3211 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_27 : fastSlice1_3211 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_28 : fastSlice1_3211 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_29 : fastSlice1_3211 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_30 : fastSlice1_3211 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_31 : fastSlice1_3211 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_32 : fastSlice1_3211 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_33 : fastSlice1_3211 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_34 : fastSlice1_3211 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_35 : fastSlice1_3211 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_36 : fastSlice1_3211 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_37 : fastSlice1_3211 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_38 : fastSlice1_3211 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_39 : fastSlice1_3211 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3211_40 : fastSlice1_3211 40 = true := by
  decide +kernel

public theorem point1_3211 : stepCheck 1 3211 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3211 u1_3211 v1_3211
    left1_3211 right1_3211
  intro b
  rw [sliceEq1_3211]
  fin_cases b
  · exact slice1_3211_0
  · exact slice1_3211_1
  · exact slice1_3211_2
  · exact slice1_3211_3
  · exact slice1_3211_4
  · exact slice1_3211_5
  · exact slice1_3211_6
  · exact slice1_3211_7
  · exact slice1_3211_8
  · exact slice1_3211_9
  · exact slice1_3211_10
  · exact slice1_3211_11
  · exact slice1_3211_12
  · exact slice1_3211_13
  · exact slice1_3211_14
  · exact slice1_3211_15
  · exact slice1_3211_16
  · exact slice1_3211_17
  · exact slice1_3211_18
  · exact slice1_3211_19
  · exact slice1_3211_20
  · exact slice1_3211_21
  · exact slice1_3211_22
  · exact slice1_3211_23
  · exact slice1_3211_24
  · exact slice1_3211_25
  · exact slice1_3211_26
  · exact slice1_3211_27
  · exact slice1_3211_28
  · exact slice1_3211_29
  · exact slice1_3211_30
  · exact slice1_3211_31
  · exact slice1_3211_32
  · exact slice1_3211_33
  · exact slice1_3211_34
  · exact slice1_3211_35
  · exact slice1_3211_36
  · exact slice1_3211_37
  · exact slice1_3211_38
  · exact slice1_3211_39
  · exact slice1_3211_40

set_option maxHeartbeats 1600000 in
public theorem point1_3212 : stepCheck 1 3212 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3213 : stepCheck 1 3213 := by
  left
  decide +kernel

private def u1_3214 : List (Fin 96) := [82, 65, 3]
private def v1_3214 : List (Fin 96) := [0, 50, 19, 69, 79, 13, 6, 15, 18, 37, 45, 57]
private def lhs1_3214 (x : Nat) : Nat := Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map3 (x)))
private def rhs1_3214 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map15 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map57 (x))))))))))))
private theorem lhs1_3214_eq : lhs1_3214 = Compressed.eval u1_3214 := by rfl
private theorem rhs1_3214_eq : rhs1_3214 = Compressed.eval v1_3214 := by rfl
private def fastSlice1_3214 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3214 ((100 * b.val + x.val) % 4060) =
      rhs1_3214 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3214 (b : Fin 41) :
    Compressed.slice u1_3214 v1_3214 b = fastSlice1_3214 b := by
  simp only [Compressed.slice, fastSlice1_3214, lhs1_3214_eq, rhs1_3214_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3214 : u1_3214.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3214).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3214 : v1_3214.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3214)).map Compressed.up0 ++
      (L0Factor 1 3214).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_0 : fastSlice1_3214 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_1 : fastSlice1_3214 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_2 : fastSlice1_3214 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_3 : fastSlice1_3214 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_4 : fastSlice1_3214 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_5 : fastSlice1_3214 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_6 : fastSlice1_3214 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_7 : fastSlice1_3214 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_8 : fastSlice1_3214 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_9 : fastSlice1_3214 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_10 : fastSlice1_3214 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_11 : fastSlice1_3214 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_12 : fastSlice1_3214 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_13 : fastSlice1_3214 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_14 : fastSlice1_3214 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_15 : fastSlice1_3214 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_16 : fastSlice1_3214 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_17 : fastSlice1_3214 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_18 : fastSlice1_3214 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_19 : fastSlice1_3214 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_20 : fastSlice1_3214 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_21 : fastSlice1_3214 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_22 : fastSlice1_3214 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_23 : fastSlice1_3214 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_24 : fastSlice1_3214 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_25 : fastSlice1_3214 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_26 : fastSlice1_3214 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_27 : fastSlice1_3214 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_28 : fastSlice1_3214 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_29 : fastSlice1_3214 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_30 : fastSlice1_3214 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_31 : fastSlice1_3214 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_32 : fastSlice1_3214 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_33 : fastSlice1_3214 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_34 : fastSlice1_3214 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_35 : fastSlice1_3214 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_36 : fastSlice1_3214 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_37 : fastSlice1_3214 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_38 : fastSlice1_3214 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_39 : fastSlice1_3214 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3214_40 : fastSlice1_3214 40 = true := by
  decide +kernel

public theorem point1_3214 : stepCheck 1 3214 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3214 u1_3214 v1_3214
    left1_3214 right1_3214
  intro b
  rw [sliceEq1_3214]
  fin_cases b
  · exact slice1_3214_0
  · exact slice1_3214_1
  · exact slice1_3214_2
  · exact slice1_3214_3
  · exact slice1_3214_4
  · exact slice1_3214_5
  · exact slice1_3214_6
  · exact slice1_3214_7
  · exact slice1_3214_8
  · exact slice1_3214_9
  · exact slice1_3214_10
  · exact slice1_3214_11
  · exact slice1_3214_12
  · exact slice1_3214_13
  · exact slice1_3214_14
  · exact slice1_3214_15
  · exact slice1_3214_16
  · exact slice1_3214_17
  · exact slice1_3214_18
  · exact slice1_3214_19
  · exact slice1_3214_20
  · exact slice1_3214_21
  · exact slice1_3214_22
  · exact slice1_3214_23
  · exact slice1_3214_24
  · exact slice1_3214_25
  · exact slice1_3214_26
  · exact slice1_3214_27
  · exact slice1_3214_28
  · exact slice1_3214_29
  · exact slice1_3214_30
  · exact slice1_3214_31
  · exact slice1_3214_32
  · exact slice1_3214_33
  · exact slice1_3214_34
  · exact slice1_3214_35
  · exact slice1_3214_36
  · exact slice1_3214_37
  · exact slice1_3214_38
  · exact slice1_3214_39
  · exact slice1_3214_40

set_option maxHeartbeats 1600000 in
public theorem point1_3215 : stepCheck 1 3215 := by
  left
  decide +kernel

private def u1_3216 : List (Fin 96) := [58, 33, 78, 3]
private def v1_3216 : List (Fin 96) := [90, 51, 78, 68, 9, 10, 42, 40, 23, 57]
private def lhs1_3216 (x : Nat) : Nat := Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map3 (x))))
private def rhs1_3216 (x : Nat) : Nat := Part6Nat.force Compressed.map90 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map68 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map57 (x))))))))))
private theorem lhs1_3216_eq : lhs1_3216 = Compressed.eval u1_3216 := by rfl
private theorem rhs1_3216_eq : rhs1_3216 = Compressed.eval v1_3216 := by rfl
private def fastSlice1_3216 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3216 ((100 * b.val + x.val) % 4060) =
      rhs1_3216 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3216 (b : Fin 41) :
    Compressed.slice u1_3216 v1_3216 b = fastSlice1_3216 b := by
  simp only [Compressed.slice, fastSlice1_3216, lhs1_3216_eq, rhs1_3216_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3216 : u1_3216.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3216).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3216 : v1_3216.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3216)).map Compressed.up0 ++
      (L0Factor 1 3216).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_0 : fastSlice1_3216 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_1 : fastSlice1_3216 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_2 : fastSlice1_3216 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_3 : fastSlice1_3216 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_4 : fastSlice1_3216 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_5 : fastSlice1_3216 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_6 : fastSlice1_3216 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_7 : fastSlice1_3216 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_8 : fastSlice1_3216 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_9 : fastSlice1_3216 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_10 : fastSlice1_3216 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_11 : fastSlice1_3216 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_12 : fastSlice1_3216 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_13 : fastSlice1_3216 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_14 : fastSlice1_3216 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_15 : fastSlice1_3216 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_16 : fastSlice1_3216 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_17 : fastSlice1_3216 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_18 : fastSlice1_3216 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_19 : fastSlice1_3216 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_20 : fastSlice1_3216 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_21 : fastSlice1_3216 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_22 : fastSlice1_3216 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_23 : fastSlice1_3216 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_24 : fastSlice1_3216 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_25 : fastSlice1_3216 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_26 : fastSlice1_3216 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_27 : fastSlice1_3216 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_28 : fastSlice1_3216 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_29 : fastSlice1_3216 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_30 : fastSlice1_3216 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_31 : fastSlice1_3216 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_32 : fastSlice1_3216 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_33 : fastSlice1_3216 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_34 : fastSlice1_3216 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_35 : fastSlice1_3216 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_36 : fastSlice1_3216 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_37 : fastSlice1_3216 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_38 : fastSlice1_3216 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_39 : fastSlice1_3216 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3216_40 : fastSlice1_3216 40 = true := by
  decide +kernel

public theorem point1_3216 : stepCheck 1 3216 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3216 u1_3216 v1_3216
    left1_3216 right1_3216
  intro b
  rw [sliceEq1_3216]
  fin_cases b
  · exact slice1_3216_0
  · exact slice1_3216_1
  · exact slice1_3216_2
  · exact slice1_3216_3
  · exact slice1_3216_4
  · exact slice1_3216_5
  · exact slice1_3216_6
  · exact slice1_3216_7
  · exact slice1_3216_8
  · exact slice1_3216_9
  · exact slice1_3216_10
  · exact slice1_3216_11
  · exact slice1_3216_12
  · exact slice1_3216_13
  · exact slice1_3216_14
  · exact slice1_3216_15
  · exact slice1_3216_16
  · exact slice1_3216_17
  · exact slice1_3216_18
  · exact slice1_3216_19
  · exact slice1_3216_20
  · exact slice1_3216_21
  · exact slice1_3216_22
  · exact slice1_3216_23
  · exact slice1_3216_24
  · exact slice1_3216_25
  · exact slice1_3216_26
  · exact slice1_3216_27
  · exact slice1_3216_28
  · exact slice1_3216_29
  · exact slice1_3216_30
  · exact slice1_3216_31
  · exact slice1_3216_32
  · exact slice1_3216_33
  · exact slice1_3216_34
  · exact slice1_3216_35
  · exact slice1_3216_36
  · exact slice1_3216_37
  · exact slice1_3216_38
  · exact slice1_3216_39
  · exact slice1_3216_40

private def u1_3217 : List (Fin 96) := [24, 46, 65, 3]
private def v1_3217 : List (Fin 96) := [0, 69, 46, 19, 9, 8, 36, 93, 83, 37, 25]
private def lhs1_3217 (x : Nat) : Nat := Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map3 (x))))
private def rhs1_3217 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map93 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map25 (x)))))))))))
private theorem lhs1_3217_eq : lhs1_3217 = Compressed.eval u1_3217 := by rfl
private theorem rhs1_3217_eq : rhs1_3217 = Compressed.eval v1_3217 := by rfl
private def fastSlice1_3217 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3217 ((100 * b.val + x.val) % 4060) =
      rhs1_3217 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3217 (b : Fin 41) :
    Compressed.slice u1_3217 v1_3217 b = fastSlice1_3217 b := by
  simp only [Compressed.slice, fastSlice1_3217, lhs1_3217_eq, rhs1_3217_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3217 : u1_3217.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3217).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3217 : v1_3217.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3217)).map Compressed.up0 ++
      (L0Factor 1 3217).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_0 : fastSlice1_3217 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_1 : fastSlice1_3217 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_2 : fastSlice1_3217 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_3 : fastSlice1_3217 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_4 : fastSlice1_3217 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_5 : fastSlice1_3217 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_6 : fastSlice1_3217 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_7 : fastSlice1_3217 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_8 : fastSlice1_3217 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_9 : fastSlice1_3217 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_10 : fastSlice1_3217 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_11 : fastSlice1_3217 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_12 : fastSlice1_3217 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_13 : fastSlice1_3217 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_14 : fastSlice1_3217 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_15 : fastSlice1_3217 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_16 : fastSlice1_3217 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_17 : fastSlice1_3217 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_18 : fastSlice1_3217 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_19 : fastSlice1_3217 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_20 : fastSlice1_3217 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_21 : fastSlice1_3217 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_22 : fastSlice1_3217 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_23 : fastSlice1_3217 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_24 : fastSlice1_3217 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_25 : fastSlice1_3217 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_26 : fastSlice1_3217 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_27 : fastSlice1_3217 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_28 : fastSlice1_3217 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_29 : fastSlice1_3217 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_30 : fastSlice1_3217 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_31 : fastSlice1_3217 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_32 : fastSlice1_3217 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_33 : fastSlice1_3217 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_34 : fastSlice1_3217 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_35 : fastSlice1_3217 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_36 : fastSlice1_3217 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_37 : fastSlice1_3217 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_38 : fastSlice1_3217 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_39 : fastSlice1_3217 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3217_40 : fastSlice1_3217 40 = true := by
  decide +kernel

public theorem point1_3217 : stepCheck 1 3217 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3217 u1_3217 v1_3217
    left1_3217 right1_3217
  intro b
  rw [sliceEq1_3217]
  fin_cases b
  · exact slice1_3217_0
  · exact slice1_3217_1
  · exact slice1_3217_2
  · exact slice1_3217_3
  · exact slice1_3217_4
  · exact slice1_3217_5
  · exact slice1_3217_6
  · exact slice1_3217_7
  · exact slice1_3217_8
  · exact slice1_3217_9
  · exact slice1_3217_10
  · exact slice1_3217_11
  · exact slice1_3217_12
  · exact slice1_3217_13
  · exact slice1_3217_14
  · exact slice1_3217_15
  · exact slice1_3217_16
  · exact slice1_3217_17
  · exact slice1_3217_18
  · exact slice1_3217_19
  · exact slice1_3217_20
  · exact slice1_3217_21
  · exact slice1_3217_22
  · exact slice1_3217_23
  · exact slice1_3217_24
  · exact slice1_3217_25
  · exact slice1_3217_26
  · exact slice1_3217_27
  · exact slice1_3217_28
  · exact slice1_3217_29
  · exact slice1_3217_30
  · exact slice1_3217_31
  · exact slice1_3217_32
  · exact slice1_3217_33
  · exact slice1_3217_34
  · exact slice1_3217_35
  · exact slice1_3217_36
  · exact slice1_3217_37
  · exact slice1_3217_38
  · exact slice1_3217_39
  · exact slice1_3217_40

set_option maxHeartbeats 1600000 in
public theorem point1_3218 : stepCheck 1 3218 := by
  left
  decide +kernel

private def u1_3219 : List (Fin 96) := [19, 21, 65, 3]
private def v1_3219 : List (Fin 96) := [0, 75, 69, 24, 10, 93, 84, 83, 88]
private def lhs1_3219 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map3 (x))))
private def rhs1_3219 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map93 (Part6Nat.force Compressed.map84 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map88 (x)))))))))
private theorem lhs1_3219_eq : lhs1_3219 = Compressed.eval u1_3219 := by rfl
private theorem rhs1_3219_eq : rhs1_3219 = Compressed.eval v1_3219 := by rfl
private def fastSlice1_3219 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3219 ((100 * b.val + x.val) % 4060) =
      rhs1_3219 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3219 (b : Fin 41) :
    Compressed.slice u1_3219 v1_3219 b = fastSlice1_3219 b := by
  simp only [Compressed.slice, fastSlice1_3219, lhs1_3219_eq, rhs1_3219_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3219 : u1_3219.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3219).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3219 : v1_3219.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3219)).map Compressed.up0 ++
      (L0Factor 1 3219).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_0 : fastSlice1_3219 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_1 : fastSlice1_3219 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_2 : fastSlice1_3219 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_3 : fastSlice1_3219 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_4 : fastSlice1_3219 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_5 : fastSlice1_3219 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_6 : fastSlice1_3219 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_7 : fastSlice1_3219 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_8 : fastSlice1_3219 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_9 : fastSlice1_3219 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_10 : fastSlice1_3219 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_11 : fastSlice1_3219 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_12 : fastSlice1_3219 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_13 : fastSlice1_3219 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_14 : fastSlice1_3219 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_15 : fastSlice1_3219 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_16 : fastSlice1_3219 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_17 : fastSlice1_3219 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_18 : fastSlice1_3219 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_19 : fastSlice1_3219 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_20 : fastSlice1_3219 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_21 : fastSlice1_3219 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_22 : fastSlice1_3219 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_23 : fastSlice1_3219 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_24 : fastSlice1_3219 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_25 : fastSlice1_3219 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_26 : fastSlice1_3219 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_27 : fastSlice1_3219 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_28 : fastSlice1_3219 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_29 : fastSlice1_3219 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_30 : fastSlice1_3219 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_31 : fastSlice1_3219 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_32 : fastSlice1_3219 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_33 : fastSlice1_3219 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_34 : fastSlice1_3219 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_35 : fastSlice1_3219 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_36 : fastSlice1_3219 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_37 : fastSlice1_3219 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_38 : fastSlice1_3219 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_39 : fastSlice1_3219 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3219_40 : fastSlice1_3219 40 = true := by
  decide +kernel

public theorem point1_3219 : stepCheck 1 3219 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3219 u1_3219 v1_3219
    left1_3219 right1_3219
  intro b
  rw [sliceEq1_3219]
  fin_cases b
  · exact slice1_3219_0
  · exact slice1_3219_1
  · exact slice1_3219_2
  · exact slice1_3219_3
  · exact slice1_3219_4
  · exact slice1_3219_5
  · exact slice1_3219_6
  · exact slice1_3219_7
  · exact slice1_3219_8
  · exact slice1_3219_9
  · exact slice1_3219_10
  · exact slice1_3219_11
  · exact slice1_3219_12
  · exact slice1_3219_13
  · exact slice1_3219_14
  · exact slice1_3219_15
  · exact slice1_3219_16
  · exact slice1_3219_17
  · exact slice1_3219_18
  · exact slice1_3219_19
  · exact slice1_3219_20
  · exact slice1_3219_21
  · exact slice1_3219_22
  · exact slice1_3219_23
  · exact slice1_3219_24
  · exact slice1_3219_25
  · exact slice1_3219_26
  · exact slice1_3219_27
  · exact slice1_3219_28
  · exact slice1_3219_29
  · exact slice1_3219_30
  · exact slice1_3219_31
  · exact slice1_3219_32
  · exact slice1_3219_33
  · exact slice1_3219_34
  · exact slice1_3219_35
  · exact slice1_3219_36
  · exact slice1_3219_37
  · exact slice1_3219_38
  · exact slice1_3219_39
  · exact slice1_3219_40

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
