module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 232

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 232 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u232 : List (Fin 96) := [0, 75, 33, 58, 14]
private def v232 : List (Fin 96) := [46, 64, 21, 24, 8, 11, 13, 8, 6, 40, 23, 27, 37, 61]
private def lhs232 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map0 (Part6Nat.force Block1DivMaps.map75 (Part6Nat.force Block1DivMaps.map33 (Part6Nat.force Block1DivMaps.map58 (Part6Nat.force Block1DivMaps.map14 (x)))))
private def rhs232 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map46 (Part6Nat.force Block1DivMaps.map64 (Part6Nat.force Block1DivMaps.map21 (Part6Nat.force Block1DivMaps.map24 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map11 (Part6Nat.force Block1DivMaps.map13 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map6 (Part6Nat.force Block1DivMaps.map40 (Part6Nat.force Block1DivMaps.map23 (Part6Nat.force Block1DivMaps.map27 (Part6Nat.force Block1DivMaps.map37 (Part6Nat.force Block1DivMaps.map61 (x))))))))))))))
private theorem lhs232_eq : lhs232 = Compressed.eval u232 := by
  funext x
  simp only [lhs232, Block1DivMaps.map0_eq, Block1DivMaps.map14_eq, Block1DivMaps.map33_eq, Block1DivMaps.map58_eq, Block1DivMaps.map75_eq]
  rfl
private theorem rhs232_eq : rhs232 = Compressed.eval v232 := by
  funext x
  simp only [rhs232, Block1DivMaps.map6_eq, Block1DivMaps.map8_eq, Block1DivMaps.map11_eq, Block1DivMaps.map13_eq, Block1DivMaps.map21_eq, Block1DivMaps.map23_eq, Block1DivMaps.map24_eq, Block1DivMaps.map27_eq, Block1DivMaps.map37_eq, Block1DivMaps.map40_eq, Block1DivMaps.map46_eq, Block1DivMaps.map61_eq, Block1DivMaps.map64_eq]
  rfl
private def fastSlice232 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs232 ((100 * b.val + x.val) % 4060) =
      rhs232 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq232 (b : Fin 41) :
    Compressed.slice u232 v232 b = fastSlice232 b := by
  simp only [Compressed.slice, fastSlice232, lhs232_eq, rhs232_eq]
set_option maxHeartbeats 1600000 in
private theorem left232 : u232.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3887).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right232 : v232.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3887)).map Compressed.up0 ++
      (L0Factor 0 3887).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice0 : fastSlice232 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice1 : fastSlice232 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice2 : fastSlice232 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice3 : fastSlice232 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice4 : fastSlice232 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice5 : fastSlice232 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice6 : fastSlice232 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice7 : fastSlice232 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice8 : fastSlice232 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice9 : fastSlice232 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice10 : fastSlice232 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice11 : fastSlice232 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice12 : fastSlice232 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice13 : fastSlice232 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice14 : fastSlice232 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice15 : fastSlice232 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice16 : fastSlice232 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice17 : fastSlice232 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice18 : fastSlice232 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice19 : fastSlice232 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice20 : fastSlice232 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice21 : fastSlice232 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice22 : fastSlice232 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice23 : fastSlice232 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice24 : fastSlice232 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice25 : fastSlice232 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice26 : fastSlice232 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice27 : fastSlice232 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice28 : fastSlice232 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice29 : fastSlice232 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice30 : fastSlice232 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice31 : fastSlice232 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice32 : fastSlice232 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice33 : fastSlice232 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice34 : fastSlice232 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice35 : fastSlice232 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice36 : fastSlice232 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice37 : fastSlice232 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice38 : fastSlice232 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice39 : fastSlice232 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point232slice40 : fastSlice232 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point232 : stepCheck 0 3887 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3887 u232 v232 left232 right232
  intro b
  rw [sliceEq232]
  fin_cases b
  · exact point232slice0
  · exact point232slice1
  · exact point232slice2
  · exact point232slice3
  · exact point232slice4
  · exact point232slice5
  · exact point232slice6
  · exact point232slice7
  · exact point232slice8
  · exact point232slice9
  · exact point232slice10
  · exact point232slice11
  · exact point232slice12
  · exact point232slice13
  · exact point232slice14
  · exact point232slice15
  · exact point232slice16
  · exact point232slice17
  · exact point232slice18
  · exact point232slice19
  · exact point232slice20
  · exact point232slice21
  · exact point232slice22
  · exact point232slice23
  · exact point232slice24
  · exact point232slice25
  · exact point232slice26
  · exact point232slice27
  · exact point232slice28
  · exact point232slice29
  · exact point232slice30
  · exact point232slice31
  · exact point232slice32
  · exact point232slice33
  · exact point232slice34
  · exact point232slice35
  · exact point232slice36
  · exact point232slice37
  · exact point232slice38
  · exact point232slice39
  · exact point232slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
