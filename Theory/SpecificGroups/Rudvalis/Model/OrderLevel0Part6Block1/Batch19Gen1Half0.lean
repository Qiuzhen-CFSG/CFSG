module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
import Mathlib.Tactic.FinCases
/-!
# Rudvalis batch 19, generator 1, slots 0–9

Algebraic transitions use the generator orders 2 and 4. Dense transitions use
compressed words, whose expansion and action are certified in Lean, followed
by kernel checks covering all 4060 points in slices of 100. Witness source:
`OrderLevel0Data`; shared subword tables are justified by `Soundness`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem point1_2780 : stepCheck 1 2780 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2781 : stepCheck 1 2781 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point1_2782 : stepCheck 1 2782 := by
  left
  decide +kernel

private def u1_2783 : List (Fin 96) := [66, 12, 76]
private def v1_2783 : List (Fin 96) := [14, 58, 33, 21, 17, 32, 23, 10, 39, 32, 52, 56]
private def lhs1_2783 (x : Nat) : Nat := Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map76 (x)))
private def rhs1_2783 (x : Nat) : Nat := Part6Nat.force Compressed.map14 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map33 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map17 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map39 (Part6Nat.force Compressed.map32 (Part6Nat.force Compressed.map52 (Part6Nat.force Compressed.map56 (x))))))))))))
private theorem lhs1_2783_eq : lhs1_2783 = Compressed.eval u1_2783 := by rfl
private theorem rhs1_2783_eq : rhs1_2783 = Compressed.eval v1_2783 := by rfl
private def fastSlice1_2783 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2783 ((100 * b.val + x.val) % 4060) =
      rhs1_2783 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2783 (b : Fin 41) :
    Compressed.slice u1_2783 v1_2783 b = fastSlice1_2783 b := by
  simp only [Compressed.slice, fastSlice1_2783, lhs1_2783_eq, rhs1_2783_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2783 : u1_2783.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2783).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2783 : v1_2783.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2783)).map Compressed.up0 ++
      (L0Factor 1 2783).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_0 : fastSlice1_2783 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_1 : fastSlice1_2783 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_2 : fastSlice1_2783 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_3 : fastSlice1_2783 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_4 : fastSlice1_2783 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_5 : fastSlice1_2783 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_6 : fastSlice1_2783 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_7 : fastSlice1_2783 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_8 : fastSlice1_2783 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_9 : fastSlice1_2783 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_10 : fastSlice1_2783 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_11 : fastSlice1_2783 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_12 : fastSlice1_2783 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_13 : fastSlice1_2783 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_14 : fastSlice1_2783 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_15 : fastSlice1_2783 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_16 : fastSlice1_2783 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_17 : fastSlice1_2783 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_18 : fastSlice1_2783 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_19 : fastSlice1_2783 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_20 : fastSlice1_2783 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_21 : fastSlice1_2783 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_22 : fastSlice1_2783 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_23 : fastSlice1_2783 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_24 : fastSlice1_2783 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_25 : fastSlice1_2783 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_26 : fastSlice1_2783 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_27 : fastSlice1_2783 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_28 : fastSlice1_2783 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_29 : fastSlice1_2783 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_30 : fastSlice1_2783 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_31 : fastSlice1_2783 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_32 : fastSlice1_2783 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_33 : fastSlice1_2783 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_34 : fastSlice1_2783 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_35 : fastSlice1_2783 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_36 : fastSlice1_2783 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_37 : fastSlice1_2783 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_38 : fastSlice1_2783 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_39 : fastSlice1_2783 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2783_40 : fastSlice1_2783 40 = true := by
  decide +kernel

public theorem point1_2783 : stepCheck 1 2783 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2783 u1_2783 v1_2783
    left1_2783 right1_2783
  intro b
  rw [sliceEq1_2783]
  fin_cases b
  · exact slice1_2783_0
  · exact slice1_2783_1
  · exact slice1_2783_2
  · exact slice1_2783_3
  · exact slice1_2783_4
  · exact slice1_2783_5
  · exact slice1_2783_6
  · exact slice1_2783_7
  · exact slice1_2783_8
  · exact slice1_2783_9
  · exact slice1_2783_10
  · exact slice1_2783_11
  · exact slice1_2783_12
  · exact slice1_2783_13
  · exact slice1_2783_14
  · exact slice1_2783_15
  · exact slice1_2783_16
  · exact slice1_2783_17
  · exact slice1_2783_18
  · exact slice1_2783_19
  · exact slice1_2783_20
  · exact slice1_2783_21
  · exact slice1_2783_22
  · exact slice1_2783_23
  · exact slice1_2783_24
  · exact slice1_2783_25
  · exact slice1_2783_26
  · exact slice1_2783_27
  · exact slice1_2783_28
  · exact slice1_2783_29
  · exact slice1_2783_30
  · exact slice1_2783_31
  · exact slice1_2783_32
  · exact slice1_2783_33
  · exact slice1_2783_34
  · exact slice1_2783_35
  · exact slice1_2783_36
  · exact slice1_2783_37
  · exact slice1_2783_38
  · exact slice1_2783_39
  · exact slice1_2783_40

private def u1_2784 : List (Fin 96) := [46, 19, 76]
private def v1_2784 : List (Fin 96) := [90, 21, 21, 60, 36, 5, 5, 27, 83, 59, 81]
private def lhs1_2784 (x : Nat) : Nat := Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map19 (Part6Nat.force Compressed.map76 (x)))
private def rhs1_2784 (x : Nat) : Nat := Part6Nat.force Compressed.map90 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map21 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map5 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map83 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map81 (x)))))))))))
private theorem lhs1_2784_eq : lhs1_2784 = Compressed.eval u1_2784 := by rfl
private theorem rhs1_2784_eq : rhs1_2784 = Compressed.eval v1_2784 := by rfl
private def fastSlice1_2784 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2784 ((100 * b.val + x.val) % 4060) =
      rhs1_2784 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2784 (b : Fin 41) :
    Compressed.slice u1_2784 v1_2784 b = fastSlice1_2784 b := by
  simp only [Compressed.slice, fastSlice1_2784, lhs1_2784_eq, rhs1_2784_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2784 : u1_2784.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2784).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2784 : v1_2784.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2784)).map Compressed.up0 ++
      (L0Factor 1 2784).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_0 : fastSlice1_2784 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_1 : fastSlice1_2784 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_2 : fastSlice1_2784 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_3 : fastSlice1_2784 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_4 : fastSlice1_2784 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_5 : fastSlice1_2784 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_6 : fastSlice1_2784 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_7 : fastSlice1_2784 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_8 : fastSlice1_2784 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_9 : fastSlice1_2784 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_10 : fastSlice1_2784 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_11 : fastSlice1_2784 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_12 : fastSlice1_2784 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_13 : fastSlice1_2784 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_14 : fastSlice1_2784 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_15 : fastSlice1_2784 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_16 : fastSlice1_2784 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_17 : fastSlice1_2784 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_18 : fastSlice1_2784 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_19 : fastSlice1_2784 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_20 : fastSlice1_2784 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_21 : fastSlice1_2784 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_22 : fastSlice1_2784 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_23 : fastSlice1_2784 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_24 : fastSlice1_2784 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_25 : fastSlice1_2784 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_26 : fastSlice1_2784 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_27 : fastSlice1_2784 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_28 : fastSlice1_2784 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_29 : fastSlice1_2784 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_30 : fastSlice1_2784 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_31 : fastSlice1_2784 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_32 : fastSlice1_2784 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_33 : fastSlice1_2784 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_34 : fastSlice1_2784 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_35 : fastSlice1_2784 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_36 : fastSlice1_2784 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_37 : fastSlice1_2784 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_38 : fastSlice1_2784 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_39 : fastSlice1_2784 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2784_40 : fastSlice1_2784 40 = true := by
  decide +kernel

public theorem point1_2784 : stepCheck 1 2784 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2784 u1_2784 v1_2784
    left1_2784 right1_2784
  intro b
  rw [sliceEq1_2784]
  fin_cases b
  · exact slice1_2784_0
  · exact slice1_2784_1
  · exact slice1_2784_2
  · exact slice1_2784_3
  · exact slice1_2784_4
  · exact slice1_2784_5
  · exact slice1_2784_6
  · exact slice1_2784_7
  · exact slice1_2784_8
  · exact slice1_2784_9
  · exact slice1_2784_10
  · exact slice1_2784_11
  · exact slice1_2784_12
  · exact slice1_2784_13
  · exact slice1_2784_14
  · exact slice1_2784_15
  · exact slice1_2784_16
  · exact slice1_2784_17
  · exact slice1_2784_18
  · exact slice1_2784_19
  · exact slice1_2784_20
  · exact slice1_2784_21
  · exact slice1_2784_22
  · exact slice1_2784_23
  · exact slice1_2784_24
  · exact slice1_2784_25
  · exact slice1_2784_26
  · exact slice1_2784_27
  · exact slice1_2784_28
  · exact slice1_2784_29
  · exact slice1_2784_30
  · exact slice1_2784_31
  · exact slice1_2784_32
  · exact slice1_2784_33
  · exact slice1_2784_34
  · exact slice1_2784_35
  · exact slice1_2784_36
  · exact slice1_2784_37
  · exact slice1_2784_38
  · exact slice1_2784_39
  · exact slice1_2784_40

set_option maxHeartbeats 1600000 in
public theorem point1_2785 : stepCheck 1 2785 := by
  left
  decide +kernel

private def u1_2786 : List (Fin 96) := [12, 46, 12, 76]
private def v1_2786 : List (Fin 96) := [90, 51, 95, 9, 36, 10, 27, 18, 48, 18, 59, 62, 56, 56]
private def lhs1_2786 (x : Nat) : Nat := Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map46 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map76 (x))))
private def rhs1_2786 (x : Nat) : Nat := Part6Nat.force Compressed.map90 (Part6Nat.force Compressed.map51 (Part6Nat.force Compressed.map95 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map10 (Part6Nat.force Compressed.map27 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map48 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map59 (Part6Nat.force Compressed.map62 (Part6Nat.force Compressed.map56 (Part6Nat.force Compressed.map56 (x))))))))))))))
private theorem lhs1_2786_eq : lhs1_2786 = Compressed.eval u1_2786 := by rfl
private theorem rhs1_2786_eq : rhs1_2786 = Compressed.eval v1_2786 := by rfl
private def fastSlice1_2786 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2786 ((100 * b.val + x.val) % 4060) =
      rhs1_2786 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2786 (b : Fin 41) :
    Compressed.slice u1_2786 v1_2786 b = fastSlice1_2786 b := by
  simp only [Compressed.slice, fastSlice1_2786, lhs1_2786_eq, rhs1_2786_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2786 : u1_2786.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2786).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2786 : v1_2786.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2786)).map Compressed.up0 ++
      (L0Factor 1 2786).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_0 : fastSlice1_2786 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_1 : fastSlice1_2786 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_2 : fastSlice1_2786 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_3 : fastSlice1_2786 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_4 : fastSlice1_2786 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_5 : fastSlice1_2786 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_6 : fastSlice1_2786 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_7 : fastSlice1_2786 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_8 : fastSlice1_2786 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_9 : fastSlice1_2786 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_10 : fastSlice1_2786 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_11 : fastSlice1_2786 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_12 : fastSlice1_2786 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_13 : fastSlice1_2786 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_14 : fastSlice1_2786 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_15 : fastSlice1_2786 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_16 : fastSlice1_2786 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_17 : fastSlice1_2786 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_18 : fastSlice1_2786 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_19 : fastSlice1_2786 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_20 : fastSlice1_2786 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_21 : fastSlice1_2786 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_22 : fastSlice1_2786 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_23 : fastSlice1_2786 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_24 : fastSlice1_2786 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_25 : fastSlice1_2786 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_26 : fastSlice1_2786 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_27 : fastSlice1_2786 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_28 : fastSlice1_2786 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_29 : fastSlice1_2786 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_30 : fastSlice1_2786 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_31 : fastSlice1_2786 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_32 : fastSlice1_2786 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_33 : fastSlice1_2786 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_34 : fastSlice1_2786 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_35 : fastSlice1_2786 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_36 : fastSlice1_2786 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_37 : fastSlice1_2786 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_38 : fastSlice1_2786 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_39 : fastSlice1_2786 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2786_40 : fastSlice1_2786 40 = true := by
  decide +kernel

public theorem point1_2786 : stepCheck 1 2786 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2786 u1_2786 v1_2786
    left1_2786 right1_2786
  intro b
  rw [sliceEq1_2786]
  fin_cases b
  · exact slice1_2786_0
  · exact slice1_2786_1
  · exact slice1_2786_2
  · exact slice1_2786_3
  · exact slice1_2786_4
  · exact slice1_2786_5
  · exact slice1_2786_6
  · exact slice1_2786_7
  · exact slice1_2786_8
  · exact slice1_2786_9
  · exact slice1_2786_10
  · exact slice1_2786_11
  · exact slice1_2786_12
  · exact slice1_2786_13
  · exact slice1_2786_14
  · exact slice1_2786_15
  · exact slice1_2786_16
  · exact slice1_2786_17
  · exact slice1_2786_18
  · exact slice1_2786_19
  · exact slice1_2786_20
  · exact slice1_2786_21
  · exact slice1_2786_22
  · exact slice1_2786_23
  · exact slice1_2786_24
  · exact slice1_2786_25
  · exact slice1_2786_26
  · exact slice1_2786_27
  · exact slice1_2786_28
  · exact slice1_2786_29
  · exact slice1_2786_30
  · exact slice1_2786_31
  · exact slice1_2786_32
  · exact slice1_2786_33
  · exact slice1_2786_34
  · exact slice1_2786_35
  · exact slice1_2786_36
  · exact slice1_2786_37
  · exact slice1_2786_38
  · exact slice1_2786_39
  · exact slice1_2786_40

private def u1_2787 : List (Fin 96) := [64, 12, 76]
private def v1_2787 : List (Fin 96) := [0, 50, 58, 75, 6, 11, 8, 36, 45, 29, 23, 74, 91, 31]
private def lhs1_2787 (x : Nat) : Nat := Part6Nat.force Compressed.map64 (Part6Nat.force Compressed.map12 (Part6Nat.force Compressed.map76 (x)))
private def rhs1_2787 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map50 (Part6Nat.force Compressed.map58 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map6 (Part6Nat.force Compressed.map11 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map45 (Part6Nat.force Compressed.map29 (Part6Nat.force Compressed.map23 (Part6Nat.force Compressed.map74 (Part6Nat.force Compressed.map91 (Part6Nat.force Compressed.map31 (x))))))))))))))
private theorem lhs1_2787_eq : lhs1_2787 = Compressed.eval u1_2787 := by rfl
private theorem rhs1_2787_eq : rhs1_2787 = Compressed.eval v1_2787 := by rfl
private def fastSlice1_2787 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2787 ((100 * b.val + x.val) % 4060) =
      rhs1_2787 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2787 (b : Fin 41) :
    Compressed.slice u1_2787 v1_2787 b = fastSlice1_2787 b := by
  simp only [Compressed.slice, fastSlice1_2787, lhs1_2787_eq, rhs1_2787_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2787 : u1_2787.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2787).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2787 : v1_2787.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2787)).map Compressed.up0 ++
      (L0Factor 1 2787).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_0 : fastSlice1_2787 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_1 : fastSlice1_2787 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_2 : fastSlice1_2787 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_3 : fastSlice1_2787 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_4 : fastSlice1_2787 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_5 : fastSlice1_2787 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_6 : fastSlice1_2787 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_7 : fastSlice1_2787 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_8 : fastSlice1_2787 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_9 : fastSlice1_2787 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_10 : fastSlice1_2787 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_11 : fastSlice1_2787 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_12 : fastSlice1_2787 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_13 : fastSlice1_2787 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_14 : fastSlice1_2787 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_15 : fastSlice1_2787 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_16 : fastSlice1_2787 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_17 : fastSlice1_2787 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_18 : fastSlice1_2787 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_19 : fastSlice1_2787 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_20 : fastSlice1_2787 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_21 : fastSlice1_2787 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_22 : fastSlice1_2787 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_23 : fastSlice1_2787 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_24 : fastSlice1_2787 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_25 : fastSlice1_2787 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_26 : fastSlice1_2787 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_27 : fastSlice1_2787 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_28 : fastSlice1_2787 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_29 : fastSlice1_2787 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_30 : fastSlice1_2787 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_31 : fastSlice1_2787 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_32 : fastSlice1_2787 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_33 : fastSlice1_2787 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_34 : fastSlice1_2787 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_35 : fastSlice1_2787 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_36 : fastSlice1_2787 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_37 : fastSlice1_2787 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_38 : fastSlice1_2787 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_39 : fastSlice1_2787 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2787_40 : fastSlice1_2787 40 = true := by
  decide +kernel

public theorem point1_2787 : stepCheck 1 2787 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2787 u1_2787 v1_2787
    left1_2787 right1_2787
  intro b
  rw [sliceEq1_2787]
  fin_cases b
  · exact slice1_2787_0
  · exact slice1_2787_1
  · exact slice1_2787_2
  · exact slice1_2787_3
  · exact slice1_2787_4
  · exact slice1_2787_5
  · exact slice1_2787_6
  · exact slice1_2787_7
  · exact slice1_2787_8
  · exact slice1_2787_9
  · exact slice1_2787_10
  · exact slice1_2787_11
  · exact slice1_2787_12
  · exact slice1_2787_13
  · exact slice1_2787_14
  · exact slice1_2787_15
  · exact slice1_2787_16
  · exact slice1_2787_17
  · exact slice1_2787_18
  · exact slice1_2787_19
  · exact slice1_2787_20
  · exact slice1_2787_21
  · exact slice1_2787_22
  · exact slice1_2787_23
  · exact slice1_2787_24
  · exact slice1_2787_25
  · exact slice1_2787_26
  · exact slice1_2787_27
  · exact slice1_2787_28
  · exact slice1_2787_29
  · exact slice1_2787_30
  · exact slice1_2787_31
  · exact slice1_2787_32
  · exact slice1_2787_33
  · exact slice1_2787_34
  · exact slice1_2787_35
  · exact slice1_2787_36
  · exact slice1_2787_37
  · exact slice1_2787_38
  · exact slice1_2787_39
  · exact slice1_2787_40

set_option maxHeartbeats 1600000 in
public theorem point1_2788 : stepCheck 1 2788 := by
  left
  decide +kernel

private def u1_2789 : List (Fin 96) := [77, 24, 76]
private def v1_2789 : List (Fin 96) := [0, 66, 75, 60, 9, 8, 36, 4, 8, 40, 18, 48, 22, 86]
private def lhs1_2789 (x : Nat) : Nat := Part6Nat.force Compressed.map77 (Part6Nat.force Compressed.map24 (Part6Nat.force Compressed.map76 (x)))
private def rhs1_2789 (x : Nat) : Nat := Part6Nat.force Compressed.map0 (Part6Nat.force Compressed.map66 (Part6Nat.force Compressed.map75 (Part6Nat.force Compressed.map60 (Part6Nat.force Compressed.map9 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map36 (Part6Nat.force Compressed.map4 (Part6Nat.force Compressed.map8 (Part6Nat.force Compressed.map40 (Part6Nat.force Compressed.map18 (Part6Nat.force Compressed.map48 (Part6Nat.force Compressed.map22 (Part6Nat.force Compressed.map86 (x))))))))))))))
private theorem lhs1_2789_eq : lhs1_2789 = Compressed.eval u1_2789 := by rfl
private theorem rhs1_2789_eq : rhs1_2789 = Compressed.eval v1_2789 := by rfl
private def fastSlice1_2789 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs1_2789 ((100 * b.val + x.val) % 4060) =
      rhs1_2789 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq1_2789 (b : Fin 41) :
    Compressed.slice u1_2789 v1_2789 b = fastSlice1_2789 b := by
  simp only [Compressed.slice, fastSlice1_2789, lhs1_2789_eq, rhs1_2789_eq]
set_option maxHeartbeats 1600000 in
private theorem left1_2789 : u1_2789.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 2789).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right1_2789 : v1_2789.flatMap Compressed.word =
    (L0RepWord (L0Act 1 2789)).map Compressed.up0 ++
      (L0Factor 1 2789).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_0 : fastSlice1_2789 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_1 : fastSlice1_2789 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_2 : fastSlice1_2789 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_3 : fastSlice1_2789 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_4 : fastSlice1_2789 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_5 : fastSlice1_2789 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_6 : fastSlice1_2789 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_7 : fastSlice1_2789 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_8 : fastSlice1_2789 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_9 : fastSlice1_2789 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_10 : fastSlice1_2789 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_11 : fastSlice1_2789 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_12 : fastSlice1_2789 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_13 : fastSlice1_2789 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_14 : fastSlice1_2789 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_15 : fastSlice1_2789 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_16 : fastSlice1_2789 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_17 : fastSlice1_2789 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_18 : fastSlice1_2789 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_19 : fastSlice1_2789 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_20 : fastSlice1_2789 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_21 : fastSlice1_2789 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_22 : fastSlice1_2789 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_23 : fastSlice1_2789 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_24 : fastSlice1_2789 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_25 : fastSlice1_2789 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_26 : fastSlice1_2789 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_27 : fastSlice1_2789 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_28 : fastSlice1_2789 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_29 : fastSlice1_2789 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_30 : fastSlice1_2789 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_31 : fastSlice1_2789 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_32 : fastSlice1_2789 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_33 : fastSlice1_2789 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_34 : fastSlice1_2789 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_35 : fastSlice1_2789 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_36 : fastSlice1_2789 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_37 : fastSlice1_2789 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_38 : fastSlice1_2789 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_39 : fastSlice1_2789 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem slice1_2789_40 : fastSlice1_2789 40 = true := by
  decide +kernel

public theorem point1_2789 : stepCheck 1 2789 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 2789 u1_2789 v1_2789
    left1_2789 right1_2789
  intro b
  rw [sliceEq1_2789]
  fin_cases b
  · exact slice1_2789_0
  · exact slice1_2789_1
  · exact slice1_2789_2
  · exact slice1_2789_3
  · exact slice1_2789_4
  · exact slice1_2789_5
  · exact slice1_2789_6
  · exact slice1_2789_7
  · exact slice1_2789_8
  · exact slice1_2789_9
  · exact slice1_2789_10
  · exact slice1_2789_11
  · exact slice1_2789_12
  · exact slice1_2789_13
  · exact slice1_2789_14
  · exact slice1_2789_15
  · exact slice1_2789_16
  · exact slice1_2789_17
  · exact slice1_2789_18
  · exact slice1_2789_19
  · exact slice1_2789_20
  · exact slice1_2789_21
  · exact slice1_2789_22
  · exact slice1_2789_23
  · exact slice1_2789_24
  · exact slice1_2789_25
  · exact slice1_2789_26
  · exact slice1_2789_27
  · exact slice1_2789_28
  · exact slice1_2789_29
  · exact slice1_2789_30
  · exact slice1_2789_31
  · exact slice1_2789_32
  · exact slice1_2789_33
  · exact slice1_2789_34
  · exact slice1_2789_35
  · exact slice1_2789_36
  · exact slice1_2789_37
  · exact slice1_2789_38
  · exact slice1_2789_39
  · exact slice1_2789_40

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1
