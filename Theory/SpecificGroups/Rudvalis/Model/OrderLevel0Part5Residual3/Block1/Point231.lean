module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 231

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 231 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u231 : List (Fin 96) := [0, 46, 65, 46]
private def v231 : List (Fin 96) := [77, 89, 3, 8, 11, 10, 27, 42, 17, 18, 37, 61, 6, 15, 22, 86]
private def lhs231 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map0 (Part6Nat.force Block1DivMaps.map46 (Part6Nat.force Block1DivMaps.map65 (Part6Nat.force Block1DivMaps.map46 (x))))
private def rhs231 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map77 (Part6Nat.force Block1DivMaps.map89 (Part6Nat.force Block1DivMaps.map3 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map11 (Part6Nat.force Block1DivMaps.map10 (Part6Nat.force Block1DivMaps.map27 (Part6Nat.force Block1DivMaps.map42 (Part6Nat.force Block1DivMaps.map17 (Part6Nat.force Block1DivMaps.map18 (Part6Nat.force Block1DivMaps.map37 (Part6Nat.force Block1DivMaps.map61 (Part6Nat.force Block1DivMaps.map6 (Part6Nat.force Block1DivMaps.map15 (Part6Nat.force Block1DivMaps.map22 (Part6Nat.force Block1DivMaps.map86 (x))))))))))))))))
private theorem lhs231_eq : lhs231 = Compressed.eval u231 := by
  funext x
  simp only [lhs231, Block1DivMaps.map0_eq, Block1DivMaps.map46_eq, Block1DivMaps.map65_eq]
  rfl
private theorem rhs231_eq : rhs231 = Compressed.eval v231 := by
  funext x
  simp only [rhs231, Block1DivMaps.map3_eq, Block1DivMaps.map6_eq, Block1DivMaps.map8_eq, Block1DivMaps.map10_eq, Block1DivMaps.map11_eq, Block1DivMaps.map15_eq, Block1DivMaps.map17_eq, Block1DivMaps.map18_eq, Block1DivMaps.map22_eq, Block1DivMaps.map27_eq, Block1DivMaps.map37_eq, Block1DivMaps.map42_eq, Block1DivMaps.map61_eq, Block1DivMaps.map77_eq, Block1DivMaps.map86_eq, Block1DivMaps.map89_eq]
  rfl
private def fastSlice231 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs231 ((100 * b.val + x.val) % 4060) =
      rhs231 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq231 (b : Fin 41) :
    Compressed.slice u231 v231 b = fastSlice231 b := by
  simp only [Compressed.slice, fastSlice231, lhs231_eq, rhs231_eq]
set_option maxHeartbeats 1600000 in
private theorem left231 : u231.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3884).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right231 : v231.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3884)).map Compressed.up0 ++
      (L0Factor 0 3884).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice0 : fastSlice231 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice1 : fastSlice231 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice2 : fastSlice231 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice3 : fastSlice231 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice4 : fastSlice231 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice5 : fastSlice231 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice6 : fastSlice231 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice7 : fastSlice231 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice8 : fastSlice231 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice9 : fastSlice231 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice10 : fastSlice231 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice11 : fastSlice231 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice12 : fastSlice231 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice13 : fastSlice231 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice14 : fastSlice231 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice15 : fastSlice231 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice16 : fastSlice231 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice17 : fastSlice231 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice18 : fastSlice231 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice19 : fastSlice231 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice20 : fastSlice231 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice21 : fastSlice231 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice22 : fastSlice231 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice23 : fastSlice231 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice24 : fastSlice231 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice25 : fastSlice231 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice26 : fastSlice231 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice27 : fastSlice231 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice28 : fastSlice231 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice29 : fastSlice231 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice30 : fastSlice231 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice31 : fastSlice231 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice32 : fastSlice231 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice33 : fastSlice231 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice34 : fastSlice231 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice35 : fastSlice231 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice36 : fastSlice231 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice37 : fastSlice231 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice38 : fastSlice231 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice39 : fastSlice231 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point231slice40 : fastSlice231 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point231 : stepCheck 0 3884 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3884 u231 v231 left231 right231
  intro b
  rw [sliceEq231]
  fin_cases b
  · exact point231slice0
  · exact point231slice1
  · exact point231slice2
  · exact point231slice3
  · exact point231slice4
  · exact point231slice5
  · exact point231slice6
  · exact point231slice7
  · exact point231slice8
  · exact point231slice9
  · exact point231slice10
  · exact point231slice11
  · exact point231slice12
  · exact point231slice13
  · exact point231slice14
  · exact point231slice15
  · exact point231slice16
  · exact point231slice17
  · exact point231slice18
  · exact point231slice19
  · exact point231slice20
  · exact point231slice21
  · exact point231slice22
  · exact point231slice23
  · exact point231slice24
  · exact point231slice25
  · exact point231slice26
  · exact point231slice27
  · exact point231slice28
  · exact point231slice29
  · exact point231slice30
  · exact point231slice31
  · exact point231slice32
  · exact point231slice33
  · exact point231slice34
  · exact point231slice35
  · exact point231slice36
  · exact point231slice37
  · exact point231slice38
  · exact point231slice39
  · exact point231slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
