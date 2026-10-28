module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 235

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 235 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u235 : List (Fin 96) := [0, 66, 75, 46]
private def v235 : List (Fin 96) := [46, 19, 33, 24, 3, 6, 11, 29, 23, 53, 5, 8, 40, 59, 62, 56]
private def lhs235 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map0 (Part6Nat.force Block1DivMaps.map66 (Part6Nat.force Block1DivMaps.map75 (Part6Nat.force Block1DivMaps.map46 (x))))
private def rhs235 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map46 (Part6Nat.force Block1DivMaps.map19 (Part6Nat.force Block1DivMaps.map33 (Part6Nat.force Block1DivMaps.map24 (Part6Nat.force Block1DivMaps.map3 (Part6Nat.force Block1DivMaps.map6 (Part6Nat.force Block1DivMaps.map11 (Part6Nat.force Block1DivMaps.map29 (Part6Nat.force Block1DivMaps.map23 (Part6Nat.force Block1DivMaps.map53 (Part6Nat.force Block1DivMaps.map5 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map40 (Part6Nat.force Block1DivMaps.map59 (Part6Nat.force Block1DivMaps.map62 (Part6Nat.force Block1DivMaps.map56 (x))))))))))))))))
private theorem lhs235_eq : lhs235 = Compressed.eval u235 := by
  funext x
  simp only [lhs235, Block1DivMaps.map0_eq, Block1DivMaps.map46_eq, Block1DivMaps.map66_eq, Block1DivMaps.map75_eq]
  rfl
private theorem rhs235_eq : rhs235 = Compressed.eval v235 := by
  funext x
  simp only [rhs235, Block1DivMaps.map3_eq, Block1DivMaps.map5_eq, Block1DivMaps.map6_eq, Block1DivMaps.map8_eq, Block1DivMaps.map11_eq, Block1DivMaps.map19_eq, Block1DivMaps.map23_eq, Block1DivMaps.map24_eq, Block1DivMaps.map29_eq, Block1DivMaps.map33_eq, Block1DivMaps.map40_eq, Block1DivMaps.map46_eq, Block1DivMaps.map53_eq, Block1DivMaps.map56_eq, Block1DivMaps.map59_eq, Block1DivMaps.map62_eq]
  rfl
private def fastSlice235 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs235 ((100 * b.val + x.val) % 4060) =
      rhs235 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq235 (b : Fin 41) :
    Compressed.slice u235 v235 b = fastSlice235 b := by
  simp only [Compressed.slice, fastSlice235, lhs235_eq, rhs235_eq]
set_option maxHeartbeats 1600000 in
private theorem left235 : u235.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3894).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right235 : v235.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3894)).map Compressed.up0 ++
      (L0Factor 0 3894).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice0 : fastSlice235 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice1 : fastSlice235 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice2 : fastSlice235 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice3 : fastSlice235 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice4 : fastSlice235 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice5 : fastSlice235 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice6 : fastSlice235 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice7 : fastSlice235 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice8 : fastSlice235 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice9 : fastSlice235 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice10 : fastSlice235 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice11 : fastSlice235 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice12 : fastSlice235 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice13 : fastSlice235 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice14 : fastSlice235 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice15 : fastSlice235 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice16 : fastSlice235 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice17 : fastSlice235 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice18 : fastSlice235 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice19 : fastSlice235 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice20 : fastSlice235 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice21 : fastSlice235 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice22 : fastSlice235 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice23 : fastSlice235 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice24 : fastSlice235 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice25 : fastSlice235 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice26 : fastSlice235 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice27 : fastSlice235 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice28 : fastSlice235 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice29 : fastSlice235 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice30 : fastSlice235 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice31 : fastSlice235 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice32 : fastSlice235 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice33 : fastSlice235 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice34 : fastSlice235 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice35 : fastSlice235 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice36 : fastSlice235 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice37 : fastSlice235 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice38 : fastSlice235 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice39 : fastSlice235 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice40 : fastSlice235 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point235 : stepCheck 0 3894 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3894 u235 v235 left235 right235
  intro b
  rw [sliceEq235]
  fin_cases b
  · exact point235slice0
  · exact point235slice1
  · exact point235slice2
  · exact point235slice3
  · exact point235slice4
  · exact point235slice5
  · exact point235slice6
  · exact point235slice7
  · exact point235slice8
  · exact point235slice9
  · exact point235slice10
  · exact point235slice11
  · exact point235slice12
  · exact point235slice13
  · exact point235slice14
  · exact point235slice15
  · exact point235slice16
  · exact point235slice17
  · exact point235slice18
  · exact point235slice19
  · exact point235slice20
  · exact point235slice21
  · exact point235slice22
  · exact point235slice23
  · exact point235slice24
  · exact point235slice25
  · exact point235slice26
  · exact point235slice27
  · exact point235slice28
  · exact point235slice29
  · exact point235slice30
  · exact point235slice31
  · exact point235slice32
  · exact point235slice33
  · exact point235slice34
  · exact point235slice35
  · exact point235slice36
  · exact point235slice37
  · exact point235slice38
  · exact point235slice39
  · exact point235slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
