module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 240

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 240 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u240 : List (Fin 96) := [77, 65, 46]
private def v240 : List (Fin 96) := [67, 82, 69, 4, 4, 8, 10, 10, 48, 37, 25, 71, 88]
private def lhs240 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map77 (Part6Nat.force Block1DivMaps.map65 (Part6Nat.force Block1DivMaps.map46 (x)))
private def rhs240 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map67 (Part6Nat.force Block1DivMaps.map82 (Part6Nat.force Block1DivMaps.map69 (Part6Nat.force Block1DivMaps.map4 (Part6Nat.force Block1DivMaps.map4 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map10 (Part6Nat.force Block1DivMaps.map10 (Part6Nat.force Block1DivMaps.map48 (Part6Nat.force Block1DivMaps.map37 (Part6Nat.force Block1DivMaps.map25 (Part6Nat.force Block1DivMaps.map71 (Part6Nat.force Block1DivMaps.map88 (x)))))))))))))
private theorem lhs240_eq : lhs240 = Compressed.eval u240 := by
  funext x
  simp only [lhs240, Block1DivMaps.map46_eq, Block1DivMaps.map65_eq, Block1DivMaps.map77_eq]
  rfl
private theorem rhs240_eq : rhs240 = Compressed.eval v240 := by
  funext x
  simp only [rhs240, Block1DivMaps.map4_eq, Block1DivMaps.map8_eq, Block1DivMaps.map10_eq, Block1DivMaps.map25_eq, Block1DivMaps.map37_eq, Block1DivMaps.map48_eq, Block1DivMaps.map67_eq, Block1DivMaps.map69_eq, Block1DivMaps.map71_eq, Block1DivMaps.map82_eq, Block1DivMaps.map88_eq]
  rfl
private def fastSlice240 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs240 ((100 * b.val + x.val) % 4060) =
      rhs240 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq240 (b : Fin 41) :
    Compressed.slice u240 v240 b = fastSlice240 b := by
  simp only [Compressed.slice, fastSlice240, lhs240_eq, rhs240_eq]
set_option maxHeartbeats 1600000 in
private theorem left240 : u240.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3883).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right240 : v240.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3883)).map Compressed.up0 ++
      (L0Factor 1 3883).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice0 : fastSlice240 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice1 : fastSlice240 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice2 : fastSlice240 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice3 : fastSlice240 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice4 : fastSlice240 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice5 : fastSlice240 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice6 : fastSlice240 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice7 : fastSlice240 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice8 : fastSlice240 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice9 : fastSlice240 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice10 : fastSlice240 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice11 : fastSlice240 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice12 : fastSlice240 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice13 : fastSlice240 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice14 : fastSlice240 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice15 : fastSlice240 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice16 : fastSlice240 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice17 : fastSlice240 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice18 : fastSlice240 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice19 : fastSlice240 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice20 : fastSlice240 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice21 : fastSlice240 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice22 : fastSlice240 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice23 : fastSlice240 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice24 : fastSlice240 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice25 : fastSlice240 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice26 : fastSlice240 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice27 : fastSlice240 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice28 : fastSlice240 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice29 : fastSlice240 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice30 : fastSlice240 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice31 : fastSlice240 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice32 : fastSlice240 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice33 : fastSlice240 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice34 : fastSlice240 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice35 : fastSlice240 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice36 : fastSlice240 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice37 : fastSlice240 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice38 : fastSlice240 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice39 : fastSlice240 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice40 : fastSlice240 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point240 : stepCheck 1 3883 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3883 u240 v240 left240 right240
  intro b
  rw [sliceEq240]
  fin_cases b
  · exact point240slice0
  · exact point240slice1
  · exact point240slice2
  · exact point240slice3
  · exact point240slice4
  · exact point240slice5
  · exact point240slice6
  · exact point240slice7
  · exact point240slice8
  · exact point240slice9
  · exact point240slice10
  · exact point240slice11
  · exact point240slice12
  · exact point240slice13
  · exact point240slice14
  · exact point240slice15
  · exact point240slice16
  · exact point240slice17
  · exact point240slice18
  · exact point240slice19
  · exact point240slice20
  · exact point240slice21
  · exact point240slice22
  · exact point240slice23
  · exact point240slice24
  · exact point240slice25
  · exact point240slice26
  · exact point240slice27
  · exact point240slice28
  · exact point240slice29
  · exact point240slice30
  · exact point240slice31
  · exact point240slice32
  · exact point240slice33
  · exact point240slice34
  · exact point240slice35
  · exact point240slice36
  · exact point240slice37
  · exact point240slice38
  · exact point240slice39
  · exact point240slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
