module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 20, generator 1, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point1_2920 : stepCheck 1 2920 := by
  left
  decide +kernel

private def u1_2921 : List (Fin 96) := [82, 64, 12]
private def v1_2921 : List (Fin 96) := [0, 51, 69, 3, 79, 4, 10, 93, 83, 23, 8, 40, 23, 57]
private def lhs1_2921 (x : Nat) : Nat := Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map12 (x)))
private def rhs1_2921 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map93 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map57 (x))))))))))))))
private theorem lhs1_2921_eq : lhs1_2921 = Compressed.eval u1_2921 := by rfl
private theorem rhs1_2921_eq : rhs1_2921 = Compressed.eval v1_2921 := by rfl
private def fastSlice1_2921 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2921 ((100 * b.val + x.val) % 4060) =
      rhs1_2921 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2921 (b : Fin 41) :
    Compressed.slice u1_2921 v1_2921 b = fastSlice1_2921 b := by
  simp only [Compressed.slice, fastSlice1_2921, lhs1_2921_eq, rhs1_2921_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2921 : u1_2921.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2921).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2921 : v1_2921.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2921)).map Compressed.up0 ++
      (L0Factor 1 2921).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_0 : fastSlice1_2921 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_1 : fastSlice1_2921 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_2 : fastSlice1_2921 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_3 : fastSlice1_2921 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_4 : fastSlice1_2921 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_5 : fastSlice1_2921 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_6 : fastSlice1_2921 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_7 : fastSlice1_2921 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_8 : fastSlice1_2921 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_9 : fastSlice1_2921 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_10 : fastSlice1_2921 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_11 : fastSlice1_2921 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_12 : fastSlice1_2921 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_13 : fastSlice1_2921 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_14 : fastSlice1_2921 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_15 : fastSlice1_2921 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_16 : fastSlice1_2921 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_17 : fastSlice1_2921 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_18 : fastSlice1_2921 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_19 : fastSlice1_2921 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_20 : fastSlice1_2921 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_21 : fastSlice1_2921 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_22 : fastSlice1_2921 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_23 : fastSlice1_2921 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_24 : fastSlice1_2921 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_25 : fastSlice1_2921 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_26 : fastSlice1_2921 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_27 : fastSlice1_2921 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_28 : fastSlice1_2921 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_29 : fastSlice1_2921 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_30 : fastSlice1_2921 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_31 : fastSlice1_2921 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_32 : fastSlice1_2921 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_33 : fastSlice1_2921 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_34 : fastSlice1_2921 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_35 : fastSlice1_2921 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_36 : fastSlice1_2921 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_37 : fastSlice1_2921 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_38 : fastSlice1_2921 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_39 : fastSlice1_2921 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2921_40 : fastSlice1_2921 40 = true := by
  decide +kernel

public theorem point1_2921 : stepCheck 1 2921 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2921 u1_2921 v1_2921
    left1_2921 right1_2921
  intro b
  rw [sliceEq1_2921]
  fin_cases b
  · exact slice1_2921_0
  · exact slice1_2921_1
  · exact slice1_2921_2
  · exact slice1_2921_3
  · exact slice1_2921_4
  · exact slice1_2921_5
  · exact slice1_2921_6
  · exact slice1_2921_7
  · exact slice1_2921_8
  · exact slice1_2921_9
  · exact slice1_2921_10
  · exact slice1_2921_11
  · exact slice1_2921_12
  · exact slice1_2921_13
  · exact slice1_2921_14
  · exact slice1_2921_15
  · exact slice1_2921_16
  · exact slice1_2921_17
  · exact slice1_2921_18
  · exact slice1_2921_19
  · exact slice1_2921_20
  · exact slice1_2921_21
  · exact slice1_2921_22
  · exact slice1_2921_23
  · exact slice1_2921_24
  · exact slice1_2921_25
  · exact slice1_2921_26
  · exact slice1_2921_27
  · exact slice1_2921_28
  · exact slice1_2921_29
  · exact slice1_2921_30
  · exact slice1_2921_31
  · exact slice1_2921_32
  · exact slice1_2921_33
  · exact slice1_2921_34
  · exact slice1_2921_35
  · exact slice1_2921_36
  · exact slice1_2921_37
  · exact slice1_2921_38
  · exact slice1_2921_39
  · exact slice1_2921_40

set_option maxHeartbeats 1600000 in
public theorem point1_2922 : stepCheck 1 2922 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2923 : stepCheck 1 2923 := by
  left
  decide +kernel

private def u1_2924 : List (Fin 96) := [63, 58, 21, 12]
private def v1_2924 : List (Fin 96) := [21, 75, 24, 60, 6, 8, 11, 17, 31, 29, 59, 62]
private def lhs1_2924 (x : Nat) : Nat := Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map12 (x))))
private def rhs1_2924 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map17 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map62 (x))))))))))))
private theorem lhs1_2924_eq : lhs1_2924 = Compressed.eval u1_2924 := by rfl
private theorem rhs1_2924_eq : rhs1_2924 = Compressed.eval v1_2924 := by rfl
private def fastSlice1_2924 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2924 ((100 * b.val + x.val) % 4060) =
      rhs1_2924 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2924 (b : Fin 41) :
    Compressed.slice u1_2924 v1_2924 b = fastSlice1_2924 b := by
  simp only [Compressed.slice, fastSlice1_2924, lhs1_2924_eq, rhs1_2924_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2924 : u1_2924.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2924).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2924 : v1_2924.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2924)).map Compressed.up0 ++
      (L0Factor 1 2924).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_0 : fastSlice1_2924 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_1 : fastSlice1_2924 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_2 : fastSlice1_2924 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_3 : fastSlice1_2924 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_4 : fastSlice1_2924 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_5 : fastSlice1_2924 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_6 : fastSlice1_2924 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_7 : fastSlice1_2924 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_8 : fastSlice1_2924 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_9 : fastSlice1_2924 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_10 : fastSlice1_2924 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_11 : fastSlice1_2924 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_12 : fastSlice1_2924 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_13 : fastSlice1_2924 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_14 : fastSlice1_2924 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_15 : fastSlice1_2924 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_16 : fastSlice1_2924 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_17 : fastSlice1_2924 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_18 : fastSlice1_2924 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_19 : fastSlice1_2924 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_20 : fastSlice1_2924 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_21 : fastSlice1_2924 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_22 : fastSlice1_2924 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_23 : fastSlice1_2924 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_24 : fastSlice1_2924 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_25 : fastSlice1_2924 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_26 : fastSlice1_2924 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_27 : fastSlice1_2924 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_28 : fastSlice1_2924 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_29 : fastSlice1_2924 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_30 : fastSlice1_2924 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_31 : fastSlice1_2924 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_32 : fastSlice1_2924 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_33 : fastSlice1_2924 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_34 : fastSlice1_2924 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_35 : fastSlice1_2924 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_36 : fastSlice1_2924 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_37 : fastSlice1_2924 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_38 : fastSlice1_2924 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_39 : fastSlice1_2924 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2924_40 : fastSlice1_2924 40 = true := by
  decide +kernel

public theorem point1_2924 : stepCheck 1 2924 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2924 u1_2924 v1_2924
    left1_2924 right1_2924
  intro b
  rw [sliceEq1_2924]
  fin_cases b
  · exact slice1_2924_0
  · exact slice1_2924_1
  · exact slice1_2924_2
  · exact slice1_2924_3
  · exact slice1_2924_4
  · exact slice1_2924_5
  · exact slice1_2924_6
  · exact slice1_2924_7
  · exact slice1_2924_8
  · exact slice1_2924_9
  · exact slice1_2924_10
  · exact slice1_2924_11
  · exact slice1_2924_12
  · exact slice1_2924_13
  · exact slice1_2924_14
  · exact slice1_2924_15
  · exact slice1_2924_16
  · exact slice1_2924_17
  · exact slice1_2924_18
  · exact slice1_2924_19
  · exact slice1_2924_20
  · exact slice1_2924_21
  · exact slice1_2924_22
  · exact slice1_2924_23
  · exact slice1_2924_24
  · exact slice1_2924_25
  · exact slice1_2924_26
  · exact slice1_2924_27
  · exact slice1_2924_28
  · exact slice1_2924_29
  · exact slice1_2924_30
  · exact slice1_2924_31
  · exact slice1_2924_32
  · exact slice1_2924_33
  · exact slice1_2924_34
  · exact slice1_2924_35
  · exact slice1_2924_36
  · exact slice1_2924_37
  · exact slice1_2924_38
  · exact slice1_2924_39
  · exact slice1_2924_40

private def u1_2925 : List (Fin 96) := [19, 50, 64, 12]
private def v1_2925 : List (Fin 96) := [67, 77, 69, 84, 8, 94, 29, 83, 59, 62, 56, 56]
private def lhs1_2925 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map12 (x))))
private def rhs1_2925 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map84 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map94 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map62 (Part6Nat.force Compressed.map56 (Part6Nat.force Compressed.map56 (x))))))))))))
private theorem lhs1_2925_eq : lhs1_2925 = Compressed.eval u1_2925 := by rfl
private theorem rhs1_2925_eq : rhs1_2925 = Compressed.eval v1_2925 := by rfl
private def fastSlice1_2925 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2925 ((100 * b.val + x.val) % 4060) =
      rhs1_2925 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2925 (b : Fin 41) :
    Compressed.slice u1_2925 v1_2925 b = fastSlice1_2925 b := by
  simp only [Compressed.slice, fastSlice1_2925, lhs1_2925_eq, rhs1_2925_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2925 : u1_2925.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2925).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2925 : v1_2925.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2925)).map Compressed.up0 ++
      (L0Factor 1 2925).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_0 : fastSlice1_2925 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_1 : fastSlice1_2925 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_2 : fastSlice1_2925 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_3 : fastSlice1_2925 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_4 : fastSlice1_2925 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_5 : fastSlice1_2925 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_6 : fastSlice1_2925 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_7 : fastSlice1_2925 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_8 : fastSlice1_2925 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_9 : fastSlice1_2925 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_10 : fastSlice1_2925 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_11 : fastSlice1_2925 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_12 : fastSlice1_2925 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_13 : fastSlice1_2925 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_14 : fastSlice1_2925 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_15 : fastSlice1_2925 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_16 : fastSlice1_2925 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_17 : fastSlice1_2925 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_18 : fastSlice1_2925 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_19 : fastSlice1_2925 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_20 : fastSlice1_2925 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_21 : fastSlice1_2925 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_22 : fastSlice1_2925 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_23 : fastSlice1_2925 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_24 : fastSlice1_2925 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_25 : fastSlice1_2925 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_26 : fastSlice1_2925 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_27 : fastSlice1_2925 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_28 : fastSlice1_2925 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_29 : fastSlice1_2925 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_30 : fastSlice1_2925 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_31 : fastSlice1_2925 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_32 : fastSlice1_2925 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_33 : fastSlice1_2925 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_34 : fastSlice1_2925 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_35 : fastSlice1_2925 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_36 : fastSlice1_2925 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_37 : fastSlice1_2925 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_38 : fastSlice1_2925 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_39 : fastSlice1_2925 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2925_40 : fastSlice1_2925 40 = true := by
  decide +kernel

public theorem point1_2925 : stepCheck 1 2925 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2925 u1_2925 v1_2925
    left1_2925 right1_2925
  intro b
  rw [sliceEq1_2925]
  fin_cases b
  · exact slice1_2925_0
  · exact slice1_2925_1
  · exact slice1_2925_2
  · exact slice1_2925_3
  · exact slice1_2925_4
  · exact slice1_2925_5
  · exact slice1_2925_6
  · exact slice1_2925_7
  · exact slice1_2925_8
  · exact slice1_2925_9
  · exact slice1_2925_10
  · exact slice1_2925_11
  · exact slice1_2925_12
  · exact slice1_2925_13
  · exact slice1_2925_14
  · exact slice1_2925_15
  · exact slice1_2925_16
  · exact slice1_2925_17
  · exact slice1_2925_18
  · exact slice1_2925_19
  · exact slice1_2925_20
  · exact slice1_2925_21
  · exact slice1_2925_22
  · exact slice1_2925_23
  · exact slice1_2925_24
  · exact slice1_2925_25
  · exact slice1_2925_26
  · exact slice1_2925_27
  · exact slice1_2925_28
  · exact slice1_2925_29
  · exact slice1_2925_30
  · exact slice1_2925_31
  · exact slice1_2925_32
  · exact slice1_2925_33
  · exact slice1_2925_34
  · exact slice1_2925_35
  · exact slice1_2925_36
  · exact slice1_2925_37
  · exact slice1_2925_38
  · exact slice1_2925_39
  · exact slice1_2925_40

set_option maxHeartbeats 1600000 in
public theorem point1_2926 : stepCheck 1 2926 := by
  left
  decide +kernel

private def u1_2927 : List (Fin 96) := [50, 33, 51, 12]
private def v1_2927 : List (Fin 96) := [67, 77, 33, 12, 9, 4, 16, 18, 59, 18, 32, 88]
private def lhs1_2927 (x : Nat) : Nat := Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map12 (x))))
private def rhs1_2927 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map88 (x))))))))))))
private theorem lhs1_2927_eq : lhs1_2927 = Compressed.eval u1_2927 := by rfl
private theorem rhs1_2927_eq : rhs1_2927 = Compressed.eval v1_2927 := by rfl
private def fastSlice1_2927 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2927 ((100 * b.val + x.val) % 4060) =
      rhs1_2927 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2927 (b : Fin 41) :
    Compressed.slice u1_2927 v1_2927 b = fastSlice1_2927 b := by
  simp only [Compressed.slice, fastSlice1_2927, lhs1_2927_eq, rhs1_2927_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2927 : u1_2927.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2927).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2927 : v1_2927.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2927)).map Compressed.up0 ++
      (L0Factor 1 2927).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_0 : fastSlice1_2927 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_1 : fastSlice1_2927 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_2 : fastSlice1_2927 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_3 : fastSlice1_2927 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_4 : fastSlice1_2927 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_5 : fastSlice1_2927 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_6 : fastSlice1_2927 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_7 : fastSlice1_2927 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_8 : fastSlice1_2927 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_9 : fastSlice1_2927 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_10 : fastSlice1_2927 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_11 : fastSlice1_2927 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_12 : fastSlice1_2927 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_13 : fastSlice1_2927 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_14 : fastSlice1_2927 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_15 : fastSlice1_2927 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_16 : fastSlice1_2927 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_17 : fastSlice1_2927 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_18 : fastSlice1_2927 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_19 : fastSlice1_2927 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_20 : fastSlice1_2927 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_21 : fastSlice1_2927 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_22 : fastSlice1_2927 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_23 : fastSlice1_2927 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_24 : fastSlice1_2927 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_25 : fastSlice1_2927 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_26 : fastSlice1_2927 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_27 : fastSlice1_2927 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_28 : fastSlice1_2927 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_29 : fastSlice1_2927 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_30 : fastSlice1_2927 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_31 : fastSlice1_2927 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_32 : fastSlice1_2927 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_33 : fastSlice1_2927 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_34 : fastSlice1_2927 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_35 : fastSlice1_2927 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_36 : fastSlice1_2927 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_37 : fastSlice1_2927 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_38 : fastSlice1_2927 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_39 : fastSlice1_2927 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2927_40 : fastSlice1_2927 40 = true := by
  decide +kernel

public theorem point1_2927 : stepCheck 1 2927 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2927 u1_2927 v1_2927
    left1_2927 right1_2927
  intro b
  rw [sliceEq1_2927]
  fin_cases b
  · exact slice1_2927_0
  · exact slice1_2927_1
  · exact slice1_2927_2
  · exact slice1_2927_3
  · exact slice1_2927_4
  · exact slice1_2927_5
  · exact slice1_2927_6
  · exact slice1_2927_7
  · exact slice1_2927_8
  · exact slice1_2927_9
  · exact slice1_2927_10
  · exact slice1_2927_11
  · exact slice1_2927_12
  · exact slice1_2927_13
  · exact slice1_2927_14
  · exact slice1_2927_15
  · exact slice1_2927_16
  · exact slice1_2927_17
  · exact slice1_2927_18
  · exact slice1_2927_19
  · exact slice1_2927_20
  · exact slice1_2927_21
  · exact slice1_2927_22
  · exact slice1_2927_23
  · exact slice1_2927_24
  · exact slice1_2927_25
  · exact slice1_2927_26
  · exact slice1_2927_27
  · exact slice1_2927_28
  · exact slice1_2927_29
  · exact slice1_2927_30
  · exact slice1_2927_31
  · exact slice1_2927_32
  · exact slice1_2927_33
  · exact slice1_2927_34
  · exact slice1_2927_35
  · exact slice1_2927_36
  · exact slice1_2927_37
  · exact slice1_2927_38
  · exact slice1_2927_39
  · exact slice1_2927_40

private def u1_2928 : List (Fin 96) := [19, 58, 51, 12]
private def v1_2928 : List (Fin 96) := [0, 77, 64, 12, 79, 79, 13, 22, 40, 85, 42, 8, 6, 73]
private def lhs1_2928 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map12 (x))))
private def rhs1_2928 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map85 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map73 (x))))))))))))))
private theorem lhs1_2928_eq : lhs1_2928 = Compressed.eval u1_2928 := by rfl
private theorem rhs1_2928_eq : rhs1_2928 = Compressed.eval v1_2928 := by rfl
private def fastSlice1_2928 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2928 ((100 * b.val + x.val) % 4060) =
      rhs1_2928 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2928 (b : Fin 41) :
    Compressed.slice u1_2928 v1_2928 b = fastSlice1_2928 b := by
  simp only [Compressed.slice, fastSlice1_2928, lhs1_2928_eq, rhs1_2928_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2928 : u1_2928.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2928).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2928 : v1_2928.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2928)).map Compressed.up0 ++
      (L0Factor 1 2928).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_0 : fastSlice1_2928 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_1 : fastSlice1_2928 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_2 : fastSlice1_2928 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_3 : fastSlice1_2928 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_4 : fastSlice1_2928 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_5 : fastSlice1_2928 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_6 : fastSlice1_2928 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_7 : fastSlice1_2928 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_8 : fastSlice1_2928 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_9 : fastSlice1_2928 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_10 : fastSlice1_2928 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_11 : fastSlice1_2928 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_12 : fastSlice1_2928 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_13 : fastSlice1_2928 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_14 : fastSlice1_2928 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_15 : fastSlice1_2928 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_16 : fastSlice1_2928 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_17 : fastSlice1_2928 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_18 : fastSlice1_2928 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_19 : fastSlice1_2928 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_20 : fastSlice1_2928 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_21 : fastSlice1_2928 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_22 : fastSlice1_2928 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_23 : fastSlice1_2928 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_24 : fastSlice1_2928 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_25 : fastSlice1_2928 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_26 : fastSlice1_2928 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_27 : fastSlice1_2928 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_28 : fastSlice1_2928 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_29 : fastSlice1_2928 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_30 : fastSlice1_2928 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_31 : fastSlice1_2928 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_32 : fastSlice1_2928 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_33 : fastSlice1_2928 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_34 : fastSlice1_2928 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_35 : fastSlice1_2928 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_36 : fastSlice1_2928 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_37 : fastSlice1_2928 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_38 : fastSlice1_2928 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_39 : fastSlice1_2928 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2928_40 : fastSlice1_2928 40 = true := by
  decide +kernel

public theorem point1_2928 : stepCheck 1 2928 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2928 u1_2928 v1_2928
    left1_2928 right1_2928
  intro b
  rw [sliceEq1_2928]
  fin_cases b
  · exact slice1_2928_0
  · exact slice1_2928_1
  · exact slice1_2928_2
  · exact slice1_2928_3
  · exact slice1_2928_4
  · exact slice1_2928_5
  · exact slice1_2928_6
  · exact slice1_2928_7
  · exact slice1_2928_8
  · exact slice1_2928_9
  · exact slice1_2928_10
  · exact slice1_2928_11
  · exact slice1_2928_12
  · exact slice1_2928_13
  · exact slice1_2928_14
  · exact slice1_2928_15
  · exact slice1_2928_16
  · exact slice1_2928_17
  · exact slice1_2928_18
  · exact slice1_2928_19
  · exact slice1_2928_20
  · exact slice1_2928_21
  · exact slice1_2928_22
  · exact slice1_2928_23
  · exact slice1_2928_24
  · exact slice1_2928_25
  · exact slice1_2928_26
  · exact slice1_2928_27
  · exact slice1_2928_28
  · exact slice1_2928_29
  · exact slice1_2928_30
  · exact slice1_2928_31
  · exact slice1_2928_32
  · exact slice1_2928_33
  · exact slice1_2928_34
  · exact slice1_2928_35
  · exact slice1_2928_36
  · exact slice1_2928_37
  · exact slice1_2928_38
  · exact slice1_2928_39
  · exact slice1_2928_40

private def u1_2929 : List (Fin 96) := [33, 66, 58]
private def v1_2929 : List (Fin 96) := [0, 75, 82, 12, 4, 20, 8, 5, 44, 37, 45, 10, 39, 18, 7]
private def lhs1_2929 (x : Nat) : Nat := Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map58 (x)))
private def rhs1_2929 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map82 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map20 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map44 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map39 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map7 (x)))))))))))))))
private theorem lhs1_2929_eq : lhs1_2929 = Compressed.eval u1_2929 := by rfl
private theorem rhs1_2929_eq : rhs1_2929 = Compressed.eval v1_2929 := by rfl
private def fastSlice1_2929 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2929 ((100 * b.val + x.val) % 4060) =
      rhs1_2929 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2929 (b : Fin 41) :
    Compressed.slice u1_2929 v1_2929 b = fastSlice1_2929 b := by
  simp only [Compressed.slice, fastSlice1_2929, lhs1_2929_eq, rhs1_2929_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2929 : u1_2929.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2929).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2929 : v1_2929.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2929)).map Compressed.up0 ++
      (L0Factor 1 2929).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_0 : fastSlice1_2929 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_1 : fastSlice1_2929 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_2 : fastSlice1_2929 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_3 : fastSlice1_2929 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_4 : fastSlice1_2929 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_5 : fastSlice1_2929 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_6 : fastSlice1_2929 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_7 : fastSlice1_2929 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_8 : fastSlice1_2929 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_9 : fastSlice1_2929 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_10 : fastSlice1_2929 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_11 : fastSlice1_2929 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_12 : fastSlice1_2929 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_13 : fastSlice1_2929 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_14 : fastSlice1_2929 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_15 : fastSlice1_2929 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_16 : fastSlice1_2929 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_17 : fastSlice1_2929 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_18 : fastSlice1_2929 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_19 : fastSlice1_2929 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_20 : fastSlice1_2929 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_21 : fastSlice1_2929 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_22 : fastSlice1_2929 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_23 : fastSlice1_2929 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_24 : fastSlice1_2929 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_25 : fastSlice1_2929 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_26 : fastSlice1_2929 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_27 : fastSlice1_2929 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_28 : fastSlice1_2929 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_29 : fastSlice1_2929 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_30 : fastSlice1_2929 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_31 : fastSlice1_2929 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_32 : fastSlice1_2929 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_33 : fastSlice1_2929 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_34 : fastSlice1_2929 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_35 : fastSlice1_2929 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_36 : fastSlice1_2929 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_37 : fastSlice1_2929 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_38 : fastSlice1_2929 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_39 : fastSlice1_2929 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2929_40 : fastSlice1_2929 40 = true := by
  decide +kernel

public theorem point1_2929 : stepCheck 1 2929 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2929 u1_2929 v1_2929
    left1_2929 right1_2929
  intro b
  rw [sliceEq1_2929]
  fin_cases b
  · exact slice1_2929_0
  · exact slice1_2929_1
  · exact slice1_2929_2
  · exact slice1_2929_3
  · exact slice1_2929_4
  · exact slice1_2929_5
  · exact slice1_2929_6
  · exact slice1_2929_7
  · exact slice1_2929_8
  · exact slice1_2929_9
  · exact slice1_2929_10
  · exact slice1_2929_11
  · exact slice1_2929_12
  · exact slice1_2929_13
  · exact slice1_2929_14
  · exact slice1_2929_15
  · exact slice1_2929_16
  · exact slice1_2929_17
  · exact slice1_2929_18
  · exact slice1_2929_19
  · exact slice1_2929_20
  · exact slice1_2929_21
  · exact slice1_2929_22
  · exact slice1_2929_23
  · exact slice1_2929_24
  · exact slice1_2929_25
  · exact slice1_2929_26
  · exact slice1_2929_27
  · exact slice1_2929_28
  · exact slice1_2929_29
  · exact slice1_2929_30
  · exact slice1_2929_31
  · exact slice1_2929_32
  · exact slice1_2929_33
  · exact slice1_2929_34
  · exact slice1_2929_35
  · exact slice1_2929_36
  · exact slice1_2929_37
  · exact slice1_2929_38
  · exact slice1_2929_39
  · exact slice1_2929_40

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
