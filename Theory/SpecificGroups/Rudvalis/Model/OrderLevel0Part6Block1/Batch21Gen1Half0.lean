module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 21, generator 1, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point1_3060 : stepCheck 1 3060 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3061 : stepCheck 1 3061 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3062 : stepCheck 1 3062 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3063 : stepCheck 1 3063 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3064 : stepCheck 1 3064 := by
  left
  decide +kernel

private def u1_3065 : List (Fin 96) := [66, 51, 50]
private def v1_3065 : List (Fin 96) := [0, 63, 33, 12, 3, 9, 36, 5, 5, 27, 31, 25, 53, 80, 55, 42, 86]
private def lhs1_3065 (x : Nat) : Nat := Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map50 (x)))
private def rhs1_3065 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map31 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map53 (Part6Nat.force Compressed.map80 (Part6Nat.force Compressed.map55 (Part6Nat.force Compressed.map42 (Part6Nat.force Compressed.map86 (x)))))))))))))))))
private theorem lhs1_3065_eq : lhs1_3065 = Compressed.eval u1_3065 := by rfl
private theorem rhs1_3065_eq : rhs1_3065 = Compressed.eval v1_3065 := by rfl
private def fastSlice1_3065 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3065 ((100 * b.val + x.val) % 4060) =
      rhs1_3065 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3065 (b : Fin 41) :
    Compressed.slice u1_3065 v1_3065 b = fastSlice1_3065 b := by
  simp only [Compressed.slice, fastSlice1_3065, lhs1_3065_eq, rhs1_3065_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3065 : u1_3065.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3065).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3065 : v1_3065.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3065)).map Compressed.up0 ++
      (L0Factor 1 3065).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_0 : fastSlice1_3065 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_1 : fastSlice1_3065 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_2 : fastSlice1_3065 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_3 : fastSlice1_3065 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_4 : fastSlice1_3065 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_5 : fastSlice1_3065 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_6 : fastSlice1_3065 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_7 : fastSlice1_3065 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_8 : fastSlice1_3065 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_9 : fastSlice1_3065 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_10 : fastSlice1_3065 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_11 : fastSlice1_3065 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_12 : fastSlice1_3065 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_13 : fastSlice1_3065 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_14 : fastSlice1_3065 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_15 : fastSlice1_3065 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_16 : fastSlice1_3065 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_17 : fastSlice1_3065 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_18 : fastSlice1_3065 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_19 : fastSlice1_3065 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_20 : fastSlice1_3065 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_21 : fastSlice1_3065 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_22 : fastSlice1_3065 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_23 : fastSlice1_3065 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_24 : fastSlice1_3065 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_25 : fastSlice1_3065 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_26 : fastSlice1_3065 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_27 : fastSlice1_3065 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_28 : fastSlice1_3065 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_29 : fastSlice1_3065 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_30 : fastSlice1_3065 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_31 : fastSlice1_3065 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_32 : fastSlice1_3065 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_33 : fastSlice1_3065 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_34 : fastSlice1_3065 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_35 : fastSlice1_3065 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_36 : fastSlice1_3065 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_37 : fastSlice1_3065 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_38 : fastSlice1_3065 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_39 : fastSlice1_3065 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3065_40 : fastSlice1_3065 40 = true := by
  decide +kernel

public theorem point1_3065 : stepCheck 1 3065 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3065 u1_3065 v1_3065
    left1_3065 right1_3065
  intro b
  rw [sliceEq1_3065]
  fin_cases b
  · exact slice1_3065_0
  · exact slice1_3065_1
  · exact slice1_3065_2
  · exact slice1_3065_3
  · exact slice1_3065_4
  · exact slice1_3065_5
  · exact slice1_3065_6
  · exact slice1_3065_7
  · exact slice1_3065_8
  · exact slice1_3065_9
  · exact slice1_3065_10
  · exact slice1_3065_11
  · exact slice1_3065_12
  · exact slice1_3065_13
  · exact slice1_3065_14
  · exact slice1_3065_15
  · exact slice1_3065_16
  · exact slice1_3065_17
  · exact slice1_3065_18
  · exact slice1_3065_19
  · exact slice1_3065_20
  · exact slice1_3065_21
  · exact slice1_3065_22
  · exact slice1_3065_23
  · exact slice1_3065_24
  · exact slice1_3065_25
  · exact slice1_3065_26
  · exact slice1_3065_27
  · exact slice1_3065_28
  · exact slice1_3065_29
  · exact slice1_3065_30
  · exact slice1_3065_31
  · exact slice1_3065_32
  · exact slice1_3065_33
  · exact slice1_3065_34
  · exact slice1_3065_35
  · exact slice1_3065_36
  · exact slice1_3065_37
  · exact slice1_3065_38
  · exact slice1_3065_39
  · exact slice1_3065_40

set_option maxHeartbeats 1600000 in
public theorem point1_3066 : stepCheck 1 3066 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_3067 : stepCheck 1 3067 := by
  left
  decide +kernel

private def u1_3068 : List (Fin 96) := [77, 78, 46]
private def v1_3068 : List (Fin 96) := [67, 63, 77, 3, 5, 30, 36, 25, 29, 37, 45, 29, 41, 32, 52]
private def lhs1_3068 (x : Nat) : Nat := Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map78 (Part6Nat.force Compressed.map46 (x)))
private def rhs1_3068 (x : Nat) : Nat := Part6Nat.force Compressed.map67 (Part6Nat.force Compressed.map63 (Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map3 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map30 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map25 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map37 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map41 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map52 (x)))))))))))))))
private theorem lhs1_3068_eq : lhs1_3068 = Compressed.eval u1_3068 := by rfl
private theorem rhs1_3068_eq : rhs1_3068 = Compressed.eval v1_3068 := by rfl
private def fastSlice1_3068 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_3068 ((100 * b.val + x.val) % 4060) =
      rhs1_3068 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_3068 (b : Fin 41) :
    Compressed.slice u1_3068 v1_3068 b = fastSlice1_3068 b := by
  simp only [Compressed.slice, fastSlice1_3068, lhs1_3068_eq, rhs1_3068_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_3068 : u1_3068.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3068).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_3068 : v1_3068.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3068)).map Compressed.up0 ++
      (L0Factor 1 3068).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_0 : fastSlice1_3068 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_1 : fastSlice1_3068 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_2 : fastSlice1_3068 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_3 : fastSlice1_3068 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_4 : fastSlice1_3068 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_5 : fastSlice1_3068 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_6 : fastSlice1_3068 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_7 : fastSlice1_3068 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_8 : fastSlice1_3068 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_9 : fastSlice1_3068 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_10 : fastSlice1_3068 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_11 : fastSlice1_3068 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_12 : fastSlice1_3068 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_13 : fastSlice1_3068 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_14 : fastSlice1_3068 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_15 : fastSlice1_3068 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_16 : fastSlice1_3068 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_17 : fastSlice1_3068 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_18 : fastSlice1_3068 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_19 : fastSlice1_3068 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_20 : fastSlice1_3068 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_21 : fastSlice1_3068 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_22 : fastSlice1_3068 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_23 : fastSlice1_3068 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_24 : fastSlice1_3068 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_25 : fastSlice1_3068 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_26 : fastSlice1_3068 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_27 : fastSlice1_3068 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_28 : fastSlice1_3068 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_29 : fastSlice1_3068 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_30 : fastSlice1_3068 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_31 : fastSlice1_3068 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_32 : fastSlice1_3068 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_33 : fastSlice1_3068 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_34 : fastSlice1_3068 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_35 : fastSlice1_3068 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_36 : fastSlice1_3068 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_37 : fastSlice1_3068 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_38 : fastSlice1_3068 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_39 : fastSlice1_3068 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_3068_40 : fastSlice1_3068 40 = true := by
  decide +kernel

public theorem point1_3068 : stepCheck 1 3068 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3068 u1_3068 v1_3068
    left1_3068 right1_3068
  intro b
  rw [sliceEq1_3068]
  fin_cases b
  · exact slice1_3068_0
  · exact slice1_3068_1
  · exact slice1_3068_2
  · exact slice1_3068_3
  · exact slice1_3068_4
  · exact slice1_3068_5
  · exact slice1_3068_6
  · exact slice1_3068_7
  · exact slice1_3068_8
  · exact slice1_3068_9
  · exact slice1_3068_10
  · exact slice1_3068_11
  · exact slice1_3068_12
  · exact slice1_3068_13
  · exact slice1_3068_14
  · exact slice1_3068_15
  · exact slice1_3068_16
  · exact slice1_3068_17
  · exact slice1_3068_18
  · exact slice1_3068_19
  · exact slice1_3068_20
  · exact slice1_3068_21
  · exact slice1_3068_22
  · exact slice1_3068_23
  · exact slice1_3068_24
  · exact slice1_3068_25
  · exact slice1_3068_26
  · exact slice1_3068_27
  · exact slice1_3068_28
  · exact slice1_3068_29
  · exact slice1_3068_30
  · exact slice1_3068_31
  · exact slice1_3068_32
  · exact slice1_3068_33
  · exact slice1_3068_34
  · exact slice1_3068_35
  · exact slice1_3068_36
  · exact slice1_3068_37
  · exact slice1_3068_38
  · exact slice1_3068_39
  · exact slice1_3068_40

set_option maxHeartbeats 1600000 in
public theorem point1_3069 : stepCheck 1 3069 := by
  left
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
