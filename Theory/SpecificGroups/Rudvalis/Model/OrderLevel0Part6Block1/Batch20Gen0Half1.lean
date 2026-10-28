module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 20, generator 0, slots 10–19

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point0_2930 : stepCheck 0 2930 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2931 : stepCheck 0 2931 := by
  left
  decide +kernel

private def u0_2932 : List (Fin 96) := [87, 46, 19, 24]
private def v0_2932 : List (Fin 96) := [46, 66, 12, 3, 9, 79, 36, 25, 53, 80, 53, 5, 61]
private def lhs0_2932 (x : Nat) : Nat := Part6Nat.force Compressed.map87 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map24 (x))))
private def rhs0_2932 (x : Nat) : Nat := Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map53 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map53 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map61 (x)))))))))))))
private theorem lhs0_2932_eq : lhs0_2932 = Compressed.eval u0_2932 := by rfl
private theorem rhs0_2932_eq : rhs0_2932 = Compressed.eval v0_2932 := by rfl
private def fastSlice0_2932 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2932 ((100 * b.val + x.val) % 4060) =
      rhs0_2932 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2932 (b : Fin 41) :
    Compressed.slice u0_2932 v0_2932 b = fastSlice0_2932 b := by
  simp only [Compressed.slice, fastSlice0_2932, lhs0_2932_eq, rhs0_2932_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2932 : u0_2932.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2932).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2932 : v0_2932.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2932)).map Compressed.up0 ++
      (L0Factor 0 2932).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_0 : fastSlice0_2932 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_1 : fastSlice0_2932 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_2 : fastSlice0_2932 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_3 : fastSlice0_2932 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_4 : fastSlice0_2932 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_5 : fastSlice0_2932 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_6 : fastSlice0_2932 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_7 : fastSlice0_2932 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_8 : fastSlice0_2932 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_9 : fastSlice0_2932 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_10 : fastSlice0_2932 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_11 : fastSlice0_2932 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_12 : fastSlice0_2932 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_13 : fastSlice0_2932 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_14 : fastSlice0_2932 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_15 : fastSlice0_2932 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_16 : fastSlice0_2932 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_17 : fastSlice0_2932 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_18 : fastSlice0_2932 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_19 : fastSlice0_2932 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_20 : fastSlice0_2932 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_21 : fastSlice0_2932 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_22 : fastSlice0_2932 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_23 : fastSlice0_2932 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_24 : fastSlice0_2932 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_25 : fastSlice0_2932 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_26 : fastSlice0_2932 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_27 : fastSlice0_2932 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_28 : fastSlice0_2932 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_29 : fastSlice0_2932 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_30 : fastSlice0_2932 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_31 : fastSlice0_2932 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_32 : fastSlice0_2932 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_33 : fastSlice0_2932 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_34 : fastSlice0_2932 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_35 : fastSlice0_2932 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_36 : fastSlice0_2932 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_37 : fastSlice0_2932 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_38 : fastSlice0_2932 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_39 : fastSlice0_2932 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2932_40 : fastSlice0_2932 40 = true := by
  decide +kernel

public theorem point0_2932 : stepCheck 0 2932 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2932 u0_2932 v0_2932
    left0_2932 right0_2932
  intro b
  rw [sliceEq0_2932]
  fin_cases b
  · exact slice0_2932_0
  · exact slice0_2932_1
  · exact slice0_2932_2
  · exact slice0_2932_3
  · exact slice0_2932_4
  · exact slice0_2932_5
  · exact slice0_2932_6
  · exact slice0_2932_7
  · exact slice0_2932_8
  · exact slice0_2932_9
  · exact slice0_2932_10
  · exact slice0_2932_11
  · exact slice0_2932_12
  · exact slice0_2932_13
  · exact slice0_2932_14
  · exact slice0_2932_15
  · exact slice0_2932_16
  · exact slice0_2932_17
  · exact slice0_2932_18
  · exact slice0_2932_19
  · exact slice0_2932_20
  · exact slice0_2932_21
  · exact slice0_2932_22
  · exact slice0_2932_23
  · exact slice0_2932_24
  · exact slice0_2932_25
  · exact slice0_2932_26
  · exact slice0_2932_27
  · exact slice0_2932_28
  · exact slice0_2932_29
  · exact slice0_2932_30
  · exact slice0_2932_31
  · exact slice0_2932_32
  · exact slice0_2932_33
  · exact slice0_2932_34
  · exact slice0_2932_35
  · exact slice0_2932_36
  · exact slice0_2932_37
  · exact slice0_2932_38
  · exact slice0_2932_39
  · exact slice0_2932_40

private def u0_2933 : List (Fin 96) := [0, 65, 33, 24]
private def v0_2933 : List (Fin 96) := [14, 65, 14, 12, 60, 4, 79, 4, 5, 44, 85, 18, 18, 59, 85, 31]
private def lhs0_2933 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map24 (x))))
private def rhs0_2933 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map65 (Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map79 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map44 (Part6Nat.force Compressed.map85 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map85 (Part6Nat.force Compressed.map31 (x))))))))))))))))
private theorem lhs0_2933_eq : lhs0_2933 = Compressed.eval u0_2933 := by rfl
private theorem rhs0_2933_eq : rhs0_2933 = Compressed.eval v0_2933 := by rfl
private def fastSlice0_2933 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2933 ((100 * b.val + x.val) % 4060) =
      rhs0_2933 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2933 (b : Fin 41) :
    Compressed.slice u0_2933 v0_2933 b = fastSlice0_2933 b := by
  simp only [Compressed.slice, fastSlice0_2933, lhs0_2933_eq, rhs0_2933_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2933 : u0_2933.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2933).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2933 : v0_2933.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2933)).map Compressed.up0 ++
      (L0Factor 0 2933).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_0 : fastSlice0_2933 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_1 : fastSlice0_2933 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_2 : fastSlice0_2933 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_3 : fastSlice0_2933 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_4 : fastSlice0_2933 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_5 : fastSlice0_2933 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_6 : fastSlice0_2933 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_7 : fastSlice0_2933 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_8 : fastSlice0_2933 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_9 : fastSlice0_2933 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_10 : fastSlice0_2933 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_11 : fastSlice0_2933 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_12 : fastSlice0_2933 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_13 : fastSlice0_2933 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_14 : fastSlice0_2933 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_15 : fastSlice0_2933 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_16 : fastSlice0_2933 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_17 : fastSlice0_2933 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_18 : fastSlice0_2933 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_19 : fastSlice0_2933 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_20 : fastSlice0_2933 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_21 : fastSlice0_2933 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_22 : fastSlice0_2933 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_23 : fastSlice0_2933 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_24 : fastSlice0_2933 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_25 : fastSlice0_2933 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_26 : fastSlice0_2933 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_27 : fastSlice0_2933 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_28 : fastSlice0_2933 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_29 : fastSlice0_2933 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_30 : fastSlice0_2933 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_31 : fastSlice0_2933 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_32 : fastSlice0_2933 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_33 : fastSlice0_2933 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_34 : fastSlice0_2933 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_35 : fastSlice0_2933 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_36 : fastSlice0_2933 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_37 : fastSlice0_2933 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_38 : fastSlice0_2933 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_39 : fastSlice0_2933 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2933_40 : fastSlice0_2933 40 = true := by
  decide +kernel

public theorem point0_2933 : stepCheck 0 2933 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2933 u0_2933 v0_2933
    left0_2933 right0_2933
  intro b
  rw [sliceEq0_2933]
  fin_cases b
  · exact slice0_2933_0
  · exact slice0_2933_1
  · exact slice0_2933_2
  · exact slice0_2933_3
  · exact slice0_2933_4
  · exact slice0_2933_5
  · exact slice0_2933_6
  · exact slice0_2933_7
  · exact slice0_2933_8
  · exact slice0_2933_9
  · exact slice0_2933_10
  · exact slice0_2933_11
  · exact slice0_2933_12
  · exact slice0_2933_13
  · exact slice0_2933_14
  · exact slice0_2933_15
  · exact slice0_2933_16
  · exact slice0_2933_17
  · exact slice0_2933_18
  · exact slice0_2933_19
  · exact slice0_2933_20
  · exact slice0_2933_21
  · exact slice0_2933_22
  · exact slice0_2933_23
  · exact slice0_2933_24
  · exact slice0_2933_25
  · exact slice0_2933_26
  · exact slice0_2933_27
  · exact slice0_2933_28
  · exact slice0_2933_29
  · exact slice0_2933_30
  · exact slice0_2933_31
  · exact slice0_2933_32
  · exact slice0_2933_33
  · exact slice0_2933_34
  · exact slice0_2933_35
  · exact slice0_2933_36
  · exact slice0_2933_37
  · exact slice0_2933_38
  · exact slice0_2933_39
  · exact slice0_2933_40

set_option maxHeartbeats 1600000 in
public theorem point0_2934 : stepCheck 0 2934 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2935 : stepCheck 0 2935 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point0_2936 : stepCheck 0 2936 := by
  left
  decide +kernel

private def u0_2937 : List (Fin 96) := [0, 63, 66, 24]
private def v0_2937 : List (Fin 96) := [19, 63, 58, 3, 4, 30, 29, 23, 45, 56, 56]
private def lhs0_2937 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map24 (x))))
private def rhs0_2937 (x : Nat) : Nat := Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map30 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map56 (Part6Nat.force Compressed.map56 (x)))))))))))
private theorem lhs0_2937_eq : lhs0_2937 = Compressed.eval u0_2937 := by rfl
private theorem rhs0_2937_eq : rhs0_2937 = Compressed.eval v0_2937 := by rfl
private def fastSlice0_2937 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2937 ((100 * b.val + x.val) % 4060) =
      rhs0_2937 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2937 (b : Fin 41) :
    Compressed.slice u0_2937 v0_2937 b = fastSlice0_2937 b := by
  simp only [Compressed.slice, fastSlice0_2937, lhs0_2937_eq, rhs0_2937_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2937 : u0_2937.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2937).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2937 : v0_2937.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2937)).map Compressed.up0 ++
      (L0Factor 0 2937).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_0 : fastSlice0_2937 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_1 : fastSlice0_2937 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_2 : fastSlice0_2937 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_3 : fastSlice0_2937 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_4 : fastSlice0_2937 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_5 : fastSlice0_2937 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_6 : fastSlice0_2937 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_7 : fastSlice0_2937 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_8 : fastSlice0_2937 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_9 : fastSlice0_2937 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_10 : fastSlice0_2937 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_11 : fastSlice0_2937 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_12 : fastSlice0_2937 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_13 : fastSlice0_2937 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_14 : fastSlice0_2937 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_15 : fastSlice0_2937 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_16 : fastSlice0_2937 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_17 : fastSlice0_2937 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_18 : fastSlice0_2937 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_19 : fastSlice0_2937 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_20 : fastSlice0_2937 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_21 : fastSlice0_2937 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_22 : fastSlice0_2937 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_23 : fastSlice0_2937 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_24 : fastSlice0_2937 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_25 : fastSlice0_2937 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_26 : fastSlice0_2937 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_27 : fastSlice0_2937 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_28 : fastSlice0_2937 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_29 : fastSlice0_2937 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_30 : fastSlice0_2937 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_31 : fastSlice0_2937 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_32 : fastSlice0_2937 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_33 : fastSlice0_2937 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_34 : fastSlice0_2937 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_35 : fastSlice0_2937 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_36 : fastSlice0_2937 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_37 : fastSlice0_2937 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_38 : fastSlice0_2937 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_39 : fastSlice0_2937 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2937_40 : fastSlice0_2937 40 = true := by
  decide +kernel

public theorem point0_2937 : stepCheck 0 2937 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2937 u0_2937 v0_2937
    left0_2937 right0_2937
  intro b
  rw [sliceEq0_2937]
  fin_cases b
  · exact slice0_2937_0
  · exact slice0_2937_1
  · exact slice0_2937_2
  · exact slice0_2937_3
  · exact slice0_2937_4
  · exact slice0_2937_5
  · exact slice0_2937_6
  · exact slice0_2937_7
  · exact slice0_2937_8
  · exact slice0_2937_9
  · exact slice0_2937_10
  · exact slice0_2937_11
  · exact slice0_2937_12
  · exact slice0_2937_13
  · exact slice0_2937_14
  · exact slice0_2937_15
  · exact slice0_2937_16
  · exact slice0_2937_17
  · exact slice0_2937_18
  · exact slice0_2937_19
  · exact slice0_2937_20
  · exact slice0_2937_21
  · exact slice0_2937_22
  · exact slice0_2937_23
  · exact slice0_2937_24
  · exact slice0_2937_25
  · exact slice0_2937_26
  · exact slice0_2937_27
  · exact slice0_2937_28
  · exact slice0_2937_29
  · exact slice0_2937_30
  · exact slice0_2937_31
  · exact slice0_2937_32
  · exact slice0_2937_33
  · exact slice0_2937_34
  · exact slice0_2937_35
  · exact slice0_2937_36
  · exact slice0_2937_37
  · exact slice0_2937_38
  · exact slice0_2937_39
  · exact slice0_2937_40

set_option maxHeartbeats 1600000 in
public theorem point0_2938 : stepCheck 0 2938 := by
  left
  decide +kernel

private def u0_2939 : List (Fin 96) := [87, 69, 58]
private def v0_2939 : List (Fin 96) := [69, 64, 12, 8, 16, 9, 59, 32, 70, 61]
private def lhs0_2939 (x : Nat) : Nat := Part6Nat.force Compressed.map87 (Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map58 (x)))
private def rhs0_2939 (x : Nat) : Nat := Part6Nat.force Compressed.map69 (Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map16 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map70 (Part6Nat.force Compressed.map61 (x))))))))))
private theorem lhs0_2939_eq : lhs0_2939 = Compressed.eval u0_2939 := by rfl
private theorem rhs0_2939_eq : rhs0_2939 = Compressed.eval v0_2939 := by rfl
private def fastSlice0_2939 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs0_2939 ((100 * b.val + x.val) % 4060) =
      rhs0_2939 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq0_2939 (b : Fin 41) :
    Compressed.slice u0_2939 v0_2939 b = fastSlice0_2939 b := by
  simp only [Compressed.slice, fastSlice0_2939, lhs0_2939_eq, rhs0_2939_eq]
set_option maxHeartbeats 1600000 in
private theorem left0_2939 : u0_2939.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 2939).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right0_2939 : v0_2939.flatMap Compressed.word =
    (L0RepWord (L0Act 0 2939)).map Compressed.up0 ++
      (L0Factor 0 2939).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_0 : fastSlice0_2939 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_1 : fastSlice0_2939 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_2 : fastSlice0_2939 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_3 : fastSlice0_2939 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_4 : fastSlice0_2939 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_5 : fastSlice0_2939 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_6 : fastSlice0_2939 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_7 : fastSlice0_2939 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_8 : fastSlice0_2939 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_9 : fastSlice0_2939 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_10 : fastSlice0_2939 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_11 : fastSlice0_2939 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_12 : fastSlice0_2939 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_13 : fastSlice0_2939 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_14 : fastSlice0_2939 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_15 : fastSlice0_2939 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_16 : fastSlice0_2939 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_17 : fastSlice0_2939 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_18 : fastSlice0_2939 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_19 : fastSlice0_2939 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_20 : fastSlice0_2939 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_21 : fastSlice0_2939 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_22 : fastSlice0_2939 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_23 : fastSlice0_2939 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_24 : fastSlice0_2939 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_25 : fastSlice0_2939 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_26 : fastSlice0_2939 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_27 : fastSlice0_2939 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_28 : fastSlice0_2939 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_29 : fastSlice0_2939 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_30 : fastSlice0_2939 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_31 : fastSlice0_2939 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_32 : fastSlice0_2939 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_33 : fastSlice0_2939 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_34 : fastSlice0_2939 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_35 : fastSlice0_2939 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_36 : fastSlice0_2939 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_37 : fastSlice0_2939 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_38 : fastSlice0_2939 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_39 : fastSlice0_2939 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice0_2939_40 : fastSlice0_2939 40 = true := by
  decide +kernel

public theorem point0_2939 : stepCheck 0 2939 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 2939 u0_2939 v0_2939
    left0_2939 right0_2939
  intro b
  rw [sliceEq0_2939]
  fin_cases b
  · exact slice0_2939_0
  · exact slice0_2939_1
  · exact slice0_2939_2
  · exact slice0_2939_3
  · exact slice0_2939_4
  · exact slice0_2939_5
  · exact slice0_2939_6
  · exact slice0_2939_7
  · exact slice0_2939_8
  · exact slice0_2939_9
  · exact slice0_2939_10
  · exact slice0_2939_11
  · exact slice0_2939_12
  · exact slice0_2939_13
  · exact slice0_2939_14
  · exact slice0_2939_15
  · exact slice0_2939_16
  · exact slice0_2939_17
  · exact slice0_2939_18
  · exact slice0_2939_19
  · exact slice0_2939_20
  · exact slice0_2939_21
  · exact slice0_2939_22
  · exact slice0_2939_23
  · exact slice0_2939_24
  · exact slice0_2939_25
  · exact slice0_2939_26
  · exact slice0_2939_27
  · exact slice0_2939_28
  · exact slice0_2939_29
  · exact slice0_2939_30
  · exact slice0_2939_31
  · exact slice0_2939_32
  · exact slice0_2939_33
  · exact slice0_2939_34
  · exact slice0_2939_35
  · exact slice0_2939_36
  · exact slice0_2939_37
  · exact slice0_2939_38
  · exact slice0_2939_39
  · exact slice0_2939_40

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
