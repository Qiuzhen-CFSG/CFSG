module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 20, generator 0, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point0_2920 : stepCheck 0 2920 := by
  left
  decide +kernel

private def u0_2921 : List (Fin 96) := [0, 66, 64, 12]
private def v0_2921 : List (Fin 96) := [12, 46, 92, 6, 10, 18, 18, 18, 37, 25, 29, 49, 86]
private def lhs0_2921 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map12 (x))))
private def rhs0_2921 (x : Nat) : Nat := Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map92 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map49 (Part6Nat.force Compressed.map86 (x)))))))))))))
private theorem lhs0_2921_eq : lhs0_2921 = Compressed.eval u0_2921 := by rfl
private theorem rhs0_2921_eq : rhs0_2921 = Compressed.eval v0_2921 := by rfl
private def fastSlice0_2921 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2921 ((100 * b.val + x.val) % 4060) =
      rhs0_2921 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2921 (b : Fin 41) :
    Compressed.slice u0_2921 v0_2921 b = fastSlice0_2921 b := by
  simp only [Compressed.slice, fastSlice0_2921, lhs0_2921_eq, rhs0_2921_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2921 : u0_2921.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2921).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2921 : v0_2921.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2921)).map Compressed.up0 ++
      (L0Factor 0 2921).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_0 : fastSlice0_2921 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_1 : fastSlice0_2921 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_2 : fastSlice0_2921 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_3 : fastSlice0_2921 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_4 : fastSlice0_2921 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_5 : fastSlice0_2921 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_6 : fastSlice0_2921 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_7 : fastSlice0_2921 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_8 : fastSlice0_2921 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_9 : fastSlice0_2921 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_10 : fastSlice0_2921 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_11 : fastSlice0_2921 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_12 : fastSlice0_2921 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_13 : fastSlice0_2921 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_14 : fastSlice0_2921 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_15 : fastSlice0_2921 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_16 : fastSlice0_2921 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_17 : fastSlice0_2921 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_18 : fastSlice0_2921 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_19 : fastSlice0_2921 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_20 : fastSlice0_2921 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_21 : fastSlice0_2921 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_22 : fastSlice0_2921 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_23 : fastSlice0_2921 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_24 : fastSlice0_2921 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_25 : fastSlice0_2921 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_26 : fastSlice0_2921 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_27 : fastSlice0_2921 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_28 : fastSlice0_2921 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_29 : fastSlice0_2921 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_30 : fastSlice0_2921 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_31 : fastSlice0_2921 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_32 : fastSlice0_2921 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_33 : fastSlice0_2921 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_34 : fastSlice0_2921 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_35 : fastSlice0_2921 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_36 : fastSlice0_2921 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_37 : fastSlice0_2921 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_38 : fastSlice0_2921 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_39 : fastSlice0_2921 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2921_40 : fastSlice0_2921 40 = true := by
  decide +kernel

public theorem point0_2921 : stepCheck 0 2921 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2921 u0_2921 v0_2921
    left0_2921 right0_2921
  intro b
  rw [sliceEq0_2921]
  fin_cases b
  · exact slice0_2921_0
  · exact slice0_2921_1
  · exact slice0_2921_2
  · exact slice0_2921_3
  · exact slice0_2921_4
  · exact slice0_2921_5
  · exact slice0_2921_6
  · exact slice0_2921_7
  · exact slice0_2921_8
  · exact slice0_2921_9
  · exact slice0_2921_10
  · exact slice0_2921_11
  · exact slice0_2921_12
  · exact slice0_2921_13
  · exact slice0_2921_14
  · exact slice0_2921_15
  · exact slice0_2921_16
  · exact slice0_2921_17
  · exact slice0_2921_18
  · exact slice0_2921_19
  · exact slice0_2921_20
  · exact slice0_2921_21
  · exact slice0_2921_22
  · exact slice0_2921_23
  · exact slice0_2921_24
  · exact slice0_2921_25
  · exact slice0_2921_26
  · exact slice0_2921_27
  · exact slice0_2921_28
  · exact slice0_2921_29
  · exact slice0_2921_30
  · exact slice0_2921_31
  · exact slice0_2921_32
  · exact slice0_2921_33
  · exact slice0_2921_34
  · exact slice0_2921_35
  · exact slice0_2921_36
  · exact slice0_2921_37
  · exact slice0_2921_38
  · exact slice0_2921_39
  · exact slice0_2921_40

set_option maxHeartbeats 1600000 in
public theorem point0_2922 : stepCheck 0 2922 := by
  left
  decide +kernel

private def u0_2923 : List (Fin 96) := [0, 46, 58, 21, 12]
private def v0_2923 : List (Fin 96) := [92, 66, 13, 5, 30, 48, 22, 40, 42, 86]
private def lhs0_2923 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map12 (x)))))
private def rhs0_2923 (x : Nat) : Nat := Part6Nat.force Compressed.map92 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map13 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map30 (Part6Nat.force Compressed.map48 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map86 (x))))))))))
private theorem lhs0_2923_eq : lhs0_2923 = Compressed.eval u0_2923 := by rfl
private theorem rhs0_2923_eq : rhs0_2923 = Compressed.eval v0_2923 := by rfl
private def fastSlice0_2923 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2923 ((100 * b.val + x.val) % 4060) =
      rhs0_2923 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2923 (b : Fin 41) :
    Compressed.slice u0_2923 v0_2923 b = fastSlice0_2923 b := by
  simp only [Compressed.slice, fastSlice0_2923, lhs0_2923_eq, rhs0_2923_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2923 : u0_2923.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2923).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2923 : v0_2923.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2923)).map Compressed.up0 ++
      (L0Factor 0 2923).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_0 : fastSlice0_2923 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_1 : fastSlice0_2923 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_2 : fastSlice0_2923 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_3 : fastSlice0_2923 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_4 : fastSlice0_2923 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_5 : fastSlice0_2923 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_6 : fastSlice0_2923 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_7 : fastSlice0_2923 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_8 : fastSlice0_2923 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_9 : fastSlice0_2923 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_10 : fastSlice0_2923 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_11 : fastSlice0_2923 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_12 : fastSlice0_2923 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_13 : fastSlice0_2923 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_14 : fastSlice0_2923 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_15 : fastSlice0_2923 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_16 : fastSlice0_2923 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_17 : fastSlice0_2923 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_18 : fastSlice0_2923 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_19 : fastSlice0_2923 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_20 : fastSlice0_2923 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_21 : fastSlice0_2923 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_22 : fastSlice0_2923 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_23 : fastSlice0_2923 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_24 : fastSlice0_2923 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_25 : fastSlice0_2923 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_26 : fastSlice0_2923 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_27 : fastSlice0_2923 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_28 : fastSlice0_2923 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_29 : fastSlice0_2923 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_30 : fastSlice0_2923 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_31 : fastSlice0_2923 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_32 : fastSlice0_2923 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_33 : fastSlice0_2923 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_34 : fastSlice0_2923 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_35 : fastSlice0_2923 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_36 : fastSlice0_2923 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_37 : fastSlice0_2923 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_38 : fastSlice0_2923 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_39 : fastSlice0_2923 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2923_40 : fastSlice0_2923 40 = true := by
  decide +kernel

public theorem point0_2923 : stepCheck 0 2923 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2923 u0_2923 v0_2923
    left0_2923 right0_2923
  intro b
  rw [sliceEq0_2923]
  fin_cases b
  · exact slice0_2923_0
  · exact slice0_2923_1
  · exact slice0_2923_2
  · exact slice0_2923_3
  · exact slice0_2923_4
  · exact slice0_2923_5
  · exact slice0_2923_6
  · exact slice0_2923_7
  · exact slice0_2923_8
  · exact slice0_2923_9
  · exact slice0_2923_10
  · exact slice0_2923_11
  · exact slice0_2923_12
  · exact slice0_2923_13
  · exact slice0_2923_14
  · exact slice0_2923_15
  · exact slice0_2923_16
  · exact slice0_2923_17
  · exact slice0_2923_18
  · exact slice0_2923_19
  · exact slice0_2923_20
  · exact slice0_2923_21
  · exact slice0_2923_22
  · exact slice0_2923_23
  · exact slice0_2923_24
  · exact slice0_2923_25
  · exact slice0_2923_26
  · exact slice0_2923_27
  · exact slice0_2923_28
  · exact slice0_2923_29
  · exact slice0_2923_30
  · exact slice0_2923_31
  · exact slice0_2923_32
  · exact slice0_2923_33
  · exact slice0_2923_34
  · exact slice0_2923_35
  · exact slice0_2923_36
  · exact slice0_2923_37
  · exact slice0_2923_38
  · exact slice0_2923_39
  · exact slice0_2923_40

set_option maxHeartbeats 1600000 in
public theorem point0_2924 : stepCheck 0 2924 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2925 : stepCheck 0 2925 := by
  left
  decide +kernel

private def u0_2926 : List (Fin 96) := [0, 69, 64, 12]
private def v0_2926 : List (Fin 96) := [21, 69, 58, 11, 8, 11, 4, 71, 22, 47]
private def lhs0_2926 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map12 (x))))
private def rhs0_2926 (x : Nat) : Nat := Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map71 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map47 (x))))))))))
private theorem lhs0_2926_eq : lhs0_2926 = Compressed.eval u0_2926 := by rfl
private theorem rhs0_2926_eq : rhs0_2926 = Compressed.eval v0_2926 := by rfl
private def fastSlice0_2926 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2926 ((100 * b.val + x.val) % 4060) =
      rhs0_2926 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2926 (b : Fin 41) :
    Compressed.slice u0_2926 v0_2926 b = fastSlice0_2926 b := by
  simp only [Compressed.slice, fastSlice0_2926, lhs0_2926_eq, rhs0_2926_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2926 : u0_2926.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2926).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2926 : v0_2926.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2926)).map Compressed.up0 ++
      (L0Factor 0 2926).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_0 : fastSlice0_2926 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_1 : fastSlice0_2926 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_2 : fastSlice0_2926 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_3 : fastSlice0_2926 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_4 : fastSlice0_2926 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_5 : fastSlice0_2926 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_6 : fastSlice0_2926 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_7 : fastSlice0_2926 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_8 : fastSlice0_2926 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_9 : fastSlice0_2926 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_10 : fastSlice0_2926 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_11 : fastSlice0_2926 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_12 : fastSlice0_2926 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_13 : fastSlice0_2926 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_14 : fastSlice0_2926 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_15 : fastSlice0_2926 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_16 : fastSlice0_2926 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_17 : fastSlice0_2926 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_18 : fastSlice0_2926 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_19 : fastSlice0_2926 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_20 : fastSlice0_2926 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_21 : fastSlice0_2926 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_22 : fastSlice0_2926 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_23 : fastSlice0_2926 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_24 : fastSlice0_2926 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_25 : fastSlice0_2926 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_26 : fastSlice0_2926 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_27 : fastSlice0_2926 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_28 : fastSlice0_2926 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_29 : fastSlice0_2926 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_30 : fastSlice0_2926 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_31 : fastSlice0_2926 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_32 : fastSlice0_2926 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_33 : fastSlice0_2926 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_34 : fastSlice0_2926 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_35 : fastSlice0_2926 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_36 : fastSlice0_2926 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_37 : fastSlice0_2926 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_38 : fastSlice0_2926 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_39 : fastSlice0_2926 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2926_40 : fastSlice0_2926 40 = true := by
  decide +kernel

public theorem point0_2926 : stepCheck 0 2926 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2926 u0_2926 v0_2926
    left0_2926 right0_2926
  intro b
  rw [sliceEq0_2926]
  fin_cases b
  · exact slice0_2926_0
  · exact slice0_2926_1
  · exact slice0_2926_2
  · exact slice0_2926_3
  · exact slice0_2926_4
  · exact slice0_2926_5
  · exact slice0_2926_6
  · exact slice0_2926_7
  · exact slice0_2926_8
  · exact slice0_2926_9
  · exact slice0_2926_10
  · exact slice0_2926_11
  · exact slice0_2926_12
  · exact slice0_2926_13
  · exact slice0_2926_14
  · exact slice0_2926_15
  · exact slice0_2926_16
  · exact slice0_2926_17
  · exact slice0_2926_18
  · exact slice0_2926_19
  · exact slice0_2926_20
  · exact slice0_2926_21
  · exact slice0_2926_22
  · exact slice0_2926_23
  · exact slice0_2926_24
  · exact slice0_2926_25
  · exact slice0_2926_26
  · exact slice0_2926_27
  · exact slice0_2926_28
  · exact slice0_2926_29
  · exact slice0_2926_30
  · exact slice0_2926_31
  · exact slice0_2926_32
  · exact slice0_2926_33
  · exact slice0_2926_34
  · exact slice0_2926_35
  · exact slice0_2926_36
  · exact slice0_2926_37
  · exact slice0_2926_38
  · exact slice0_2926_39
  · exact slice0_2926_40

set_option maxHeartbeats 1600000 in
public theorem point0_2927 : stepCheck 0 2927 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2928 : stepCheck 0 2928 := by
  left
  decide +kernel

private def u0_2929 : List (Fin 96) := [90, 66, 58]
private def v0_2929 : List (Fin 96) := [14, 77, 19, 50, 16, 9, 16, 9, 16, 27, 59, 91, 42, 8, 6, 73]
private def lhs0_2929 (x : Nat) : Nat := Part6Nat.force Compressed.map90 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map58 (x)))
private def rhs0_2929 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map91 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map73 (x))))))))))))))))
private theorem lhs0_2929_eq : lhs0_2929 = Compressed.eval u0_2929 := by rfl
private theorem rhs0_2929_eq : rhs0_2929 = Compressed.eval v0_2929 := by rfl
private def fastSlice0_2929 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2929 ((100 * b.val + x.val) % 4060) =
      rhs0_2929 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2929 (b : Fin 41) :
    Compressed.slice u0_2929 v0_2929 b = fastSlice0_2929 b := by
  simp only [Compressed.slice, fastSlice0_2929, lhs0_2929_eq, rhs0_2929_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2929 : u0_2929.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2929).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2929 : v0_2929.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2929)).map Compressed.up0 ++
      (L0Factor 0 2929).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_0 : fastSlice0_2929 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_1 : fastSlice0_2929 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_2 : fastSlice0_2929 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_3 : fastSlice0_2929 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_4 : fastSlice0_2929 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_5 : fastSlice0_2929 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_6 : fastSlice0_2929 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_7 : fastSlice0_2929 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_8 : fastSlice0_2929 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_9 : fastSlice0_2929 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_10 : fastSlice0_2929 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_11 : fastSlice0_2929 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_12 : fastSlice0_2929 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_13 : fastSlice0_2929 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_14 : fastSlice0_2929 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_15 : fastSlice0_2929 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_16 : fastSlice0_2929 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_17 : fastSlice0_2929 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_18 : fastSlice0_2929 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_19 : fastSlice0_2929 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_20 : fastSlice0_2929 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_21 : fastSlice0_2929 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_22 : fastSlice0_2929 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_23 : fastSlice0_2929 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_24 : fastSlice0_2929 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_25 : fastSlice0_2929 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_26 : fastSlice0_2929 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_27 : fastSlice0_2929 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_28 : fastSlice0_2929 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_29 : fastSlice0_2929 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_30 : fastSlice0_2929 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_31 : fastSlice0_2929 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_32 : fastSlice0_2929 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_33 : fastSlice0_2929 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_34 : fastSlice0_2929 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_35 : fastSlice0_2929 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_36 : fastSlice0_2929 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_37 : fastSlice0_2929 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_38 : fastSlice0_2929 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_39 : fastSlice0_2929 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2929_40 : fastSlice0_2929 40 = true := by
  decide +kernel

public theorem point0_2929 : stepCheck 0 2929 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2929 u0_2929 v0_2929
    left0_2929 right0_2929
  intro b
  rw [sliceEq0_2929]
  fin_cases b
  · exact slice0_2929_0
  · exact slice0_2929_1
  · exact slice0_2929_2
  · exact slice0_2929_3
  · exact slice0_2929_4
  · exact slice0_2929_5
  · exact slice0_2929_6
  · exact slice0_2929_7
  · exact slice0_2929_8
  · exact slice0_2929_9
  · exact slice0_2929_10
  · exact slice0_2929_11
  · exact slice0_2929_12
  · exact slice0_2929_13
  · exact slice0_2929_14
  · exact slice0_2929_15
  · exact slice0_2929_16
  · exact slice0_2929_17
  · exact slice0_2929_18
  · exact slice0_2929_19
  · exact slice0_2929_20
  · exact slice0_2929_21
  · exact slice0_2929_22
  · exact slice0_2929_23
  · exact slice0_2929_24
  · exact slice0_2929_25
  · exact slice0_2929_26
  · exact slice0_2929_27
  · exact slice0_2929_28
  · exact slice0_2929_29
  · exact slice0_2929_30
  · exact slice0_2929_31
  · exact slice0_2929_32
  · exact slice0_2929_33
  · exact slice0_2929_34
  · exact slice0_2929_35
  · exact slice0_2929_36
  · exact slice0_2929_37
  · exact slice0_2929_38
  · exact slice0_2929_39
  · exact slice0_2929_40

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
