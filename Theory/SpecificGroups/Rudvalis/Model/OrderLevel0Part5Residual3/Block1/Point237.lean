module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 237

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 237 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u237 : List (Fin 96) := [0, 58, 21, 50, 46]
private def v237 : List (Fin 96) := [63, 21, 50, 19, 4, 4, 8, 10, 5, 27, 42, 30, 18, 42, 86]
private def lhs237 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map0 (Part6Nat.force Block1DivMaps.map58 (Part6Nat.force Block1DivMaps.map21 (Part6Nat.force Block1DivMaps.map50 (Part6Nat.force Block1DivMaps.map46 (x)))))
private def rhs237 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map63 (Part6Nat.force Block1DivMaps.map21 (Part6Nat.force Block1DivMaps.map50 (Part6Nat.force Block1DivMaps.map19 (Part6Nat.force Block1DivMaps.map4 (Part6Nat.force Block1DivMaps.map4 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map10 (Part6Nat.force Block1DivMaps.map5 (Part6Nat.force Block1DivMaps.map27 (Part6Nat.force Block1DivMaps.map42 (Part6Nat.force Block1DivMaps.map30 (Part6Nat.force Block1DivMaps.map18 (Part6Nat.force Block1DivMaps.map42 (Part6Nat.force Block1DivMaps.map86 (x)))))))))))))))
private theorem lhs237_eq : lhs237 = Compressed.eval u237 := by
  funext x
  simp only [lhs237, Block1DivMaps.map0_eq, Block1DivMaps.map21_eq, Block1DivMaps.map46_eq, Block1DivMaps.map50_eq, Block1DivMaps.map58_eq]
  rfl
private theorem rhs237_eq : rhs237 = Compressed.eval v237 := by
  funext x
  simp only [rhs237, Block1DivMaps.map4_eq, Block1DivMaps.map5_eq, Block1DivMaps.map8_eq, Block1DivMaps.map10_eq, Block1DivMaps.map18_eq, Block1DivMaps.map19_eq, Block1DivMaps.map21_eq, Block1DivMaps.map27_eq, Block1DivMaps.map30_eq, Block1DivMaps.map42_eq, Block1DivMaps.map50_eq, Block1DivMaps.map63_eq, Block1DivMaps.map86_eq]
  rfl
private def fastSlice237 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs237 ((100 * b.val + x.val) % 4060) =
      rhs237 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq237 (b : Fin 41) :
    Compressed.slice u237 v237 b = fastSlice237 b := by
  simp only [Compressed.slice, fastSlice237, lhs237_eq, rhs237_eq]
set_option maxHeartbeats 1600000 in
private theorem left237 : u237.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3897).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right237 : v237.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3897)).map Compressed.up0 ++
      (L0Factor 0 3897).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice0 : fastSlice237 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice1 : fastSlice237 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice2 : fastSlice237 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice3 : fastSlice237 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice4 : fastSlice237 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice5 : fastSlice237 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice6 : fastSlice237 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice7 : fastSlice237 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice8 : fastSlice237 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice9 : fastSlice237 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice10 : fastSlice237 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice11 : fastSlice237 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice12 : fastSlice237 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice13 : fastSlice237 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice14 : fastSlice237 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice15 : fastSlice237 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice16 : fastSlice237 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice17 : fastSlice237 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice18 : fastSlice237 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice19 : fastSlice237 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice20 : fastSlice237 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice21 : fastSlice237 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice22 : fastSlice237 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice23 : fastSlice237 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice24 : fastSlice237 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice25 : fastSlice237 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice26 : fastSlice237 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice27 : fastSlice237 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice28 : fastSlice237 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice29 : fastSlice237 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice30 : fastSlice237 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice31 : fastSlice237 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice32 : fastSlice237 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice33 : fastSlice237 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice34 : fastSlice237 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice35 : fastSlice237 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice36 : fastSlice237 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice37 : fastSlice237 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice38 : fastSlice237 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice39 : fastSlice237 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point237slice40 : fastSlice237 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point237 : stepCheck 0 3897 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3897 u237 v237 left237 right237
  intro b
  rw [sliceEq237]
  fin_cases b
  · exact point237slice0
  · exact point237slice1
  · exact point237slice2
  · exact point237slice3
  · exact point237slice4
  · exact point237slice5
  · exact point237slice6
  · exact point237slice7
  · exact point237slice8
  · exact point237slice9
  · exact point237slice10
  · exact point237slice11
  · exact point237slice12
  · exact point237slice13
  · exact point237slice14
  · exact point237slice15
  · exact point237slice16
  · exact point237slice17
  · exact point237slice18
  · exact point237slice19
  · exact point237slice20
  · exact point237slice21
  · exact point237slice22
  · exact point237slice23
  · exact point237slice24
  · exact point237slice25
  · exact point237slice26
  · exact point237slice27
  · exact point237slice28
  · exact point237slice29
  · exact point237slice30
  · exact point237slice31
  · exact point237slice32
  · exact point237slice33
  · exact point237slice34
  · exact point237slice35
  · exact point237slice36
  · exact point237slice37
  · exact point237slice38
  · exact point237slice39
  · exact point237slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
