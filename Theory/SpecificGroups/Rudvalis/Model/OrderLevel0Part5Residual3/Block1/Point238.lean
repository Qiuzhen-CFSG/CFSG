module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 238

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 238 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u238 : List (Fin 96) := [0, 50, 69, 14, 46]
private def v238 : List (Fin 96) := [14, 63, 33, 24, 3, 79, 8, 93, 91, 83, 59, 22, 47, 56]
private def lhs238 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map0 (Part6Nat.force Block1DivMaps.map50 (Part6Nat.force Block1DivMaps.map69 (Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map46 (x)))))
private def rhs238 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map63 (Part6Nat.force Block1DivMaps.map33 (Part6Nat.force Block1DivMaps.map24 (Part6Nat.force Block1DivMaps.map3 (Part6Nat.force Block1DivMaps.map79 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map93 (Part6Nat.force Block1DivMaps.map91 (Part6Nat.force Block1DivMaps.map83 (Part6Nat.force Block1DivMaps.map59 (Part6Nat.force Block1DivMaps.map22 (Part6Nat.force Block1DivMaps.map47 (Part6Nat.force Block1DivMaps.map56 (x))))))))))))))
private theorem lhs238_eq : lhs238 = Compressed.eval u238 := by
  funext x
  simp only [lhs238, Block1DivMaps.map0_eq, Block1DivMaps.map14_eq, Block1DivMaps.map46_eq, Block1DivMaps.map50_eq, Block1DivMaps.map69_eq]
  rfl
private theorem rhs238_eq : rhs238 = Compressed.eval v238 := by
  funext x
  simp only [rhs238, Block1DivMaps.map3_eq, Block1DivMaps.map8_eq, Block1DivMaps.map14_eq, Block1DivMaps.map22_eq, Block1DivMaps.map24_eq, Block1DivMaps.map33_eq, Block1DivMaps.map47_eq, Block1DivMaps.map56_eq, Block1DivMaps.map59_eq, Block1DivMaps.map63_eq, Block1DivMaps.map79_eq, Block1DivMaps.map83_eq, Block1DivMaps.map91_eq, Block1DivMaps.map93_eq]
  rfl
private def fastSlice238 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs238 ((100 * b.val + x.val) % 4060) =
      rhs238 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq238 (b : Fin 41) :
    Compressed.slice u238 v238 b = fastSlice238 b := by
  simp only [Compressed.slice, fastSlice238, lhs238_eq, rhs238_eq]
set_option maxHeartbeats 1600000 in
private theorem left238 : u238.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3899).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right238 : v238.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3899)).map Compressed.up0 ++
      (L0Factor 0 3899).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice0 : fastSlice238 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice1 : fastSlice238 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice2 : fastSlice238 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice3 : fastSlice238 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice4 : fastSlice238 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice5 : fastSlice238 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice6 : fastSlice238 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice7 : fastSlice238 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice8 : fastSlice238 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice9 : fastSlice238 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice10 : fastSlice238 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice11 : fastSlice238 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice12 : fastSlice238 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice13 : fastSlice238 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice14 : fastSlice238 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice15 : fastSlice238 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice16 : fastSlice238 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice17 : fastSlice238 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice18 : fastSlice238 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice19 : fastSlice238 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice20 : fastSlice238 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice21 : fastSlice238 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice22 : fastSlice238 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice23 : fastSlice238 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice24 : fastSlice238 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice25 : fastSlice238 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice26 : fastSlice238 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice27 : fastSlice238 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice28 : fastSlice238 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice29 : fastSlice238 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice30 : fastSlice238 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice31 : fastSlice238 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice32 : fastSlice238 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice33 : fastSlice238 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice34 : fastSlice238 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice35 : fastSlice238 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice36 : fastSlice238 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice37 : fastSlice238 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice38 : fastSlice238 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice39 : fastSlice238 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point238slice40 : fastSlice238 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point238 : stepCheck 0 3899 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3899 u238 v238 left238 right238
  intro b
  rw [sliceEq238]
  fin_cases b
  · exact point238slice0
  · exact point238slice1
  · exact point238slice2
  · exact point238slice3
  · exact point238slice4
  · exact point238slice5
  · exact point238slice6
  · exact point238slice7
  · exact point238slice8
  · exact point238slice9
  · exact point238slice10
  · exact point238slice11
  · exact point238slice12
  · exact point238slice13
  · exact point238slice14
  · exact point238slice15
  · exact point238slice16
  · exact point238slice17
  · exact point238slice18
  · exact point238slice19
  · exact point238slice20
  · exact point238slice21
  · exact point238slice22
  · exact point238slice23
  · exact point238slice24
  · exact point238slice25
  · exact point238slice26
  · exact point238slice27
  · exact point238slice28
  · exact point238slice29
  · exact point238slice30
  · exact point238slice31
  · exact point238slice32
  · exact point238slice33
  · exact point238slice34
  · exact point238slice35
  · exact point238slice36
  · exact point238slice37
  · exact point238slice38
  · exact point238slice39
  · exact point238slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
