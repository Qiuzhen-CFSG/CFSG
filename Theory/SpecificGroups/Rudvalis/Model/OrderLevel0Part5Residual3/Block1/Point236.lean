module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 236

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 236 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u236 : List (Fin 96) := [0, 63, 69, 46]
private def v236 : List (Fin 96) := [51, 46, 33, 60, 9, 4, 5, 30, 71, 59, 91, 31, 56, 56]
private def lhs236 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map0 (Part6Nat.force Block1DivMaps.map63 (Part6Nat.force Block1DivMaps.map69 (Part6Nat.force Block1DivMaps.map46 (x))))
private def rhs236 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map51 (Part6Nat.force Block1DivMaps.map46 (Part6Nat.force Block1DivMaps.map33 (Part6Nat.force Block1DivMaps.map60 (Part6Nat.force Block1DivMaps.map9 (Part6Nat.force Block1DivMaps.map4 (Part6Nat.force Block1DivMaps.map5 (Part6Nat.force Block1DivMaps.map30 (Part6Nat.force Block1DivMaps.map71 (Part6Nat.force Block1DivMaps.map59 (Part6Nat.force Block1DivMaps.map91 (Part6Nat.force Block1DivMaps.map31 (Part6Nat.force Block1DivMaps.map56 (Part6Nat.force Block1DivMaps.map56 (x))))))))))))))
private theorem lhs236_eq : lhs236 = Compressed.eval u236 := by
  funext x
  simp only [lhs236, Block1DivMaps.map0_eq, Block1DivMaps.map46_eq, Block1DivMaps.map63_eq, Block1DivMaps.map69_eq]
  rfl
private theorem rhs236_eq : rhs236 = Compressed.eval v236 := by
  funext x
  simp only [rhs236, Block1DivMaps.map4_eq, Block1DivMaps.map5_eq, Block1DivMaps.map9_eq, Block1DivMaps.map30_eq, Block1DivMaps.map31_eq, Block1DivMaps.map33_eq, Block1DivMaps.map46_eq, Block1DivMaps.map51_eq, Block1DivMaps.map56_eq, Block1DivMaps.map59_eq, Block1DivMaps.map60_eq, Block1DivMaps.map71_eq, Block1DivMaps.map91_eq]
  rfl
private def fastSlice236 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs236 ((100 * b.val + x.val) % 4060) =
      rhs236 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq236 (b : Fin 41) :
    Compressed.slice u236 v236 b = fastSlice236 b := by
  simp only [Compressed.slice, fastSlice236, lhs236_eq, rhs236_eq]
set_option maxHeartbeats 1600000 in
private theorem left236 : u236.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3896).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right236 : v236.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3896)).map Compressed.up0 ++
      (L0Factor 0 3896).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice0 : fastSlice236 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice1 : fastSlice236 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice2 : fastSlice236 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice3 : fastSlice236 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice4 : fastSlice236 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice5 : fastSlice236 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice6 : fastSlice236 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice7 : fastSlice236 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice8 : fastSlice236 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice9 : fastSlice236 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice10 : fastSlice236 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice11 : fastSlice236 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice12 : fastSlice236 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice13 : fastSlice236 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice14 : fastSlice236 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice15 : fastSlice236 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice16 : fastSlice236 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice17 : fastSlice236 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice18 : fastSlice236 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice19 : fastSlice236 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice20 : fastSlice236 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice21 : fastSlice236 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice22 : fastSlice236 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice23 : fastSlice236 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice24 : fastSlice236 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice25 : fastSlice236 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice26 : fastSlice236 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice27 : fastSlice236 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice28 : fastSlice236 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice29 : fastSlice236 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice30 : fastSlice236 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice31 : fastSlice236 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice32 : fastSlice236 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice33 : fastSlice236 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice34 : fastSlice236 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice35 : fastSlice236 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice36 : fastSlice236 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice37 : fastSlice236 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice38 : fastSlice236 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice39 : fastSlice236 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point236slice40 : fastSlice236 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point236 : stepCheck 0 3896 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3896 u236 v236 left236 right236
  intro b
  rw [sliceEq236]
  fin_cases b
  · exact point236slice0
  · exact point236slice1
  · exact point236slice2
  · exact point236slice3
  · exact point236slice4
  · exact point236slice5
  · exact point236slice6
  · exact point236slice7
  · exact point236slice8
  · exact point236slice9
  · exact point236slice10
  · exact point236slice11
  · exact point236slice12
  · exact point236slice13
  · exact point236slice14
  · exact point236slice15
  · exact point236slice16
  · exact point236slice17
  · exact point236slice18
  · exact point236slice19
  · exact point236slice20
  · exact point236slice21
  · exact point236slice22
  · exact point236slice23
  · exact point236slice24
  · exact point236slice25
  · exact point236slice26
  · exact point236slice27
  · exact point236slice28
  · exact point236slice29
  · exact point236slice30
  · exact point236slice31
  · exact point236slice32
  · exact point236slice33
  · exact point236slice34
  · exact point236slice35
  · exact point236slice36
  · exact point236slice37
  · exact point236slice38
  · exact point236slice39
  · exact point236slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
