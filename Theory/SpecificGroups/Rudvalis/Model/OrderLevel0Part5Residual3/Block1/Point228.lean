module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 228

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 228 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u228 : List (Fin 96) := [64, 21, 65]
private def v228 : List (Fin 96) := [21, 63, 63, 12, 20, 9, 10, 18, 37, 25, 27, 42, 47, 56]
private def lhs228 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map64 (Part6Nat.force Block1DivMaps.map21 (Part6Nat.force Block1DivMaps.map65 (x)))
private def rhs228 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map21 (Part6Nat.force Block1DivMaps.map63 (Part6Nat.force Block1DivMaps.map63 (Part6Nat.force Block1DivMaps.map12 (Part6Nat.force Block1DivMaps.map20 (Part6Nat.force Block1DivMaps.map9 (Part6Nat.force Block1DivMaps.map10 (Part6Nat.force Block1DivMaps.map18 (Part6Nat.force Block1DivMaps.map37 (Part6Nat.force Block1DivMaps.map25 (Part6Nat.force Block1DivMaps.map27 (Part6Nat.force Block1DivMaps.map42 (Part6Nat.force Block1DivMaps.map47 (Part6Nat.force Block1DivMaps.map56 (x))))))))))))))
private theorem lhs228_eq : lhs228 = Compressed.eval u228 := by
  funext x
  simp only [lhs228, Block1DivMaps.map21_eq, Block1DivMaps.map64_eq, Block1DivMaps.map65_eq]
  rfl
private theorem rhs228_eq : rhs228 = Compressed.eval v228 := by
  funext x
  simp only [rhs228, Block1DivMaps.map9_eq, Block1DivMaps.map10_eq, Block1DivMaps.map12_eq, Block1DivMaps.map18_eq, Block1DivMaps.map20_eq, Block1DivMaps.map21_eq, Block1DivMaps.map25_eq, Block1DivMaps.map27_eq, Block1DivMaps.map37_eq, Block1DivMaps.map42_eq, Block1DivMaps.map47_eq, Block1DivMaps.map56_eq, Block1DivMaps.map63_eq]
  rfl
private def fastSlice228 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs228 ((100 * b.val + x.val) % 4060) =
      rhs228 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq228 (b : Fin 41) :
    Compressed.slice u228 v228 b = fastSlice228 b := by
  simp only [Compressed.slice, fastSlice228, lhs228_eq, rhs228_eq]
set_option maxHeartbeats 1600000 in
private theorem left228 : u228.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3759).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right228 : v228.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3759)).map Compressed.up0 ++
      (L0Factor 1 3759).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice0 : fastSlice228 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice1 : fastSlice228 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice2 : fastSlice228 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice3 : fastSlice228 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice4 : fastSlice228 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice5 : fastSlice228 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice6 : fastSlice228 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice7 : fastSlice228 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice8 : fastSlice228 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice9 : fastSlice228 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice10 : fastSlice228 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice11 : fastSlice228 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice12 : fastSlice228 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice13 : fastSlice228 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice14 : fastSlice228 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice15 : fastSlice228 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice16 : fastSlice228 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice17 : fastSlice228 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice18 : fastSlice228 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice19 : fastSlice228 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice20 : fastSlice228 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice21 : fastSlice228 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice22 : fastSlice228 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice23 : fastSlice228 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice24 : fastSlice228 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice25 : fastSlice228 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice26 : fastSlice228 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice27 : fastSlice228 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice28 : fastSlice228 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice29 : fastSlice228 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice30 : fastSlice228 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice31 : fastSlice228 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice32 : fastSlice228 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice33 : fastSlice228 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice34 : fastSlice228 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice35 : fastSlice228 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice36 : fastSlice228 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice37 : fastSlice228 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice38 : fastSlice228 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice39 : fastSlice228 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point228slice40 : fastSlice228 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point228 : stepCheck 1 3759 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3759 u228 v228 left228 right228
  intro b
  rw [sliceEq228]
  fin_cases b
  · exact point228slice0
  · exact point228slice1
  · exact point228slice2
  · exact point228slice3
  · exact point228slice4
  · exact point228slice5
  · exact point228slice6
  · exact point228slice7
  · exact point228slice8
  · exact point228slice9
  · exact point228slice10
  · exact point228slice11
  · exact point228slice12
  · exact point228slice13
  · exact point228slice14
  · exact point228slice15
  · exact point228slice16
  · exact point228slice17
  · exact point228slice18
  · exact point228slice19
  · exact point228slice20
  · exact point228slice21
  · exact point228slice22
  · exact point228slice23
  · exact point228slice24
  · exact point228slice25
  · exact point228slice26
  · exact point228slice27
  · exact point228slice28
  · exact point228slice29
  · exact point228slice30
  · exact point228slice31
  · exact point228slice32
  · exact point228slice33
  · exact point228slice34
  · exact point228slice35
  · exact point228slice36
  · exact point228slice37
  · exact point228slice38
  · exact point228slice39
  · exact point228slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
