module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 227

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 227 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u227 : List (Fin 96) := [69, 21, 65]
private def v227 : List (Fin 96) := [0, 63, 75, 33, 4, 10, 36, 23, 29, 48, 85, 31]
private def lhs227 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map69 (Part6Nat.force Block1DivMaps.map21 (Part6Nat.force Block1DivMaps.map65 (x)))
private def rhs227 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map0 (Part6Nat.force Block1DivMaps.map63 (Part6Nat.force Block1DivMaps.map75 (Part6Nat.force Block1DivMaps.map33 (Part6Nat.force Block1DivMaps.map4 (Part6Nat.force Block1DivMaps.map10 (Part6Nat.force Block1DivMaps.map36 (Part6Nat.force Block1DivMaps.map23 (Part6Nat.force Block1DivMaps.map29 (Part6Nat.force Block1DivMaps.map48 (Part6Nat.force Block1DivMaps.map85 (Part6Nat.force Block1DivMaps.map31 (x))))))))))))
private theorem lhs227_eq : lhs227 = Compressed.eval u227 := by
  funext x
  simp only [lhs227, Block1DivMaps.map21_eq, Block1DivMaps.map65_eq, Block1DivMaps.map69_eq]
  rfl
private theorem rhs227_eq : rhs227 = Compressed.eval v227 := by
  funext x
  simp only [rhs227, Block1DivMaps.map0_eq, Block1DivMaps.map4_eq, Block1DivMaps.map10_eq, Block1DivMaps.map23_eq, Block1DivMaps.map29_eq, Block1DivMaps.map31_eq, Block1DivMaps.map33_eq, Block1DivMaps.map36_eq, Block1DivMaps.map48_eq, Block1DivMaps.map63_eq, Block1DivMaps.map75_eq, Block1DivMaps.map85_eq]
  rfl
private def fastSlice227 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs227 ((100 * b.val + x.val) % 4060) =
      rhs227 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq227 (b : Fin 41) :
    Compressed.slice u227 v227 b = fastSlice227 b := by
  simp only [Compressed.slice, fastSlice227, lhs227_eq, rhs227_eq]
set_option maxHeartbeats 1600000 in
private theorem left227 : u227.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3758).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right227 : v227.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3758)).map Compressed.up0 ++
      (L0Factor 1 3758).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice0 : fastSlice227 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice1 : fastSlice227 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice2 : fastSlice227 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice3 : fastSlice227 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice4 : fastSlice227 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice5 : fastSlice227 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice6 : fastSlice227 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice7 : fastSlice227 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice8 : fastSlice227 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice9 : fastSlice227 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice10 : fastSlice227 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice11 : fastSlice227 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice12 : fastSlice227 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice13 : fastSlice227 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice14 : fastSlice227 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice15 : fastSlice227 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice16 : fastSlice227 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice17 : fastSlice227 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice18 : fastSlice227 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice19 : fastSlice227 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice20 : fastSlice227 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice21 : fastSlice227 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice22 : fastSlice227 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice23 : fastSlice227 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice24 : fastSlice227 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice25 : fastSlice227 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice26 : fastSlice227 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice27 : fastSlice227 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice28 : fastSlice227 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice29 : fastSlice227 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice30 : fastSlice227 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice31 : fastSlice227 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice32 : fastSlice227 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice33 : fastSlice227 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice34 : fastSlice227 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice35 : fastSlice227 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice36 : fastSlice227 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice37 : fastSlice227 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice38 : fastSlice227 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice39 : fastSlice227 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point227slice40 : fastSlice227 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point227 : stepCheck 1 3758 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3758 u227 v227 left227 right227
  intro b
  rw [sliceEq227]
  fin_cases b
  · exact point227slice0
  · exact point227slice1
  · exact point227slice2
  · exact point227slice3
  · exact point227slice4
  · exact point227slice5
  · exact point227slice6
  · exact point227slice7
  · exact point227slice8
  · exact point227slice9
  · exact point227slice10
  · exact point227slice11
  · exact point227slice12
  · exact point227slice13
  · exact point227slice14
  · exact point227slice15
  · exact point227slice16
  · exact point227slice17
  · exact point227slice18
  · exact point227slice19
  · exact point227slice20
  · exact point227slice21
  · exact point227slice22
  · exact point227slice23
  · exact point227slice24
  · exact point227slice25
  · exact point227slice26
  · exact point227slice27
  · exact point227slice28
  · exact point227slice29
  · exact point227slice30
  · exact point227slice31
  · exact point227slice32
  · exact point227slice33
  · exact point227slice34
  · exact point227slice35
  · exact point227slice36
  · exact point227slice37
  · exact point227slice38
  · exact point227slice39
  · exact point227slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
