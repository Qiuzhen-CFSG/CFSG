module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 226

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 226 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u226 : List (Fin 96) := [64, 50, 65]
private def v226 : List (Fin 96) := [14, 19, 46, 69, 6, 40, 8, 28, 5, 27, 37, 25, 74, 6, 8, 6, 73]
private def lhs226 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map64 (Part6Nat.force Block1DivMaps.map50 (Part6Nat.force Block1DivMaps.map65 (x)))
private def rhs226 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map19 (Part6Nat.force Block1DivMaps.map46 (Part6Nat.force Block1DivMaps.map69 (Part6Nat.force Block1DivMaps.map6 (Part6Nat.force Block1DivMaps.map40 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map28 (Part6Nat.force Block1DivMaps.map5 (Part6Nat.force Block1DivMaps.map27 (Part6Nat.force Block1DivMaps.map37 (Part6Nat.force Block1DivMaps.map25 (Part6Nat.force Block1DivMaps.map74 (Part6Nat.force Block1DivMaps.map6 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map6 (Part6Nat.force Block1DivMaps.map73 (x)))))))))))))))))
private theorem lhs226_eq : lhs226 = Compressed.eval u226 := by
  funext x
  simp only [lhs226, Block1DivMaps.map50_eq, Block1DivMaps.map64_eq, Block1DivMaps.map65_eq]
  rfl
private theorem rhs226_eq : rhs226 = Compressed.eval v226 := by
  funext x
  simp only [rhs226, Block1DivMaps.map5_eq, Block1DivMaps.map6_eq, Block1DivMaps.map8_eq, Block1DivMaps.map14_eq, Block1DivMaps.map19_eq, Block1DivMaps.map25_eq, Block1DivMaps.map27_eq, Block1DivMaps.map28_eq, Block1DivMaps.map37_eq, Block1DivMaps.map40_eq, Block1DivMaps.map46_eq, Block1DivMaps.map69_eq, Block1DivMaps.map73_eq, Block1DivMaps.map74_eq]
  rfl
private def fastSlice226 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs226 ((100 * b.val + x.val) % 4060) =
      rhs226 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq226 (b : Fin 41) :
    Compressed.slice u226 v226 b = fastSlice226 b := by
  simp only [Compressed.slice, fastSlice226, lhs226_eq, rhs226_eq]
set_option maxHeartbeats 1600000 in
private theorem left226 : u226.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3757).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right226 : v226.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3757)).map Compressed.up0 ++
      (L0Factor 1 3757).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice0 : fastSlice226 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice1 : fastSlice226 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice2 : fastSlice226 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice3 : fastSlice226 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice4 : fastSlice226 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice5 : fastSlice226 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice6 : fastSlice226 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice7 : fastSlice226 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice8 : fastSlice226 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice9 : fastSlice226 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice10 : fastSlice226 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice11 : fastSlice226 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice12 : fastSlice226 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice13 : fastSlice226 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice14 : fastSlice226 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice15 : fastSlice226 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice16 : fastSlice226 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice17 : fastSlice226 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice18 : fastSlice226 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice19 : fastSlice226 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice20 : fastSlice226 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice21 : fastSlice226 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice22 : fastSlice226 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice23 : fastSlice226 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice24 : fastSlice226 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice25 : fastSlice226 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice26 : fastSlice226 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice27 : fastSlice226 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice28 : fastSlice226 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice29 : fastSlice226 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice30 : fastSlice226 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice31 : fastSlice226 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice32 : fastSlice226 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice33 : fastSlice226 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice34 : fastSlice226 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice35 : fastSlice226 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice36 : fastSlice226 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice37 : fastSlice226 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice38 : fastSlice226 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice39 : fastSlice226 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point226slice40 : fastSlice226 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point226 : stepCheck 1 3757 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3757 u226 v226 left226 right226
  intro b
  rw [sliceEq226]
  fin_cases b
  · exact point226slice0
  · exact point226slice1
  · exact point226slice2
  · exact point226slice3
  · exact point226slice4
  · exact point226slice5
  · exact point226slice6
  · exact point226slice7
  · exact point226slice8
  · exact point226slice9
  · exact point226slice10
  · exact point226slice11
  · exact point226slice12
  · exact point226slice13
  · exact point226slice14
  · exact point226slice15
  · exact point226slice16
  · exact point226slice17
  · exact point226slice18
  · exact point226slice19
  · exact point226slice20
  · exact point226slice21
  · exact point226slice22
  · exact point226slice23
  · exact point226slice24
  · exact point226slice25
  · exact point226slice26
  · exact point226slice27
  · exact point226slice28
  · exact point226slice29
  · exact point226slice30
  · exact point226slice31
  · exact point226slice32
  · exact point226slice33
  · exact point226slice34
  · exact point226slice35
  · exact point226slice36
  · exact point226slice37
  · exact point226slice38
  · exact point226slice39
  · exact point226slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
