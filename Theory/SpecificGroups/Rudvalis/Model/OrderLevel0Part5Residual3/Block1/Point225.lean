module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 225

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 225 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u225 : List (Fin 96) := [63, 14, 64, 14, 3]
private def v225 : List (Fin 96) := [0, 33, 64, 58, 6, 13, 8, 91, 70]
private def lhs225 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map63 (Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map64 (Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map3 (x)))))
private def rhs225 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map0 (Part6Nat.force Block1DivMaps.map33 (Part6Nat.force Block1DivMaps.map64 (Part6Nat.force Block1DivMaps.map58 (Part6Nat.force Block1DivMaps.map6 (Part6Nat.force Block1DivMaps.map13 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map91 (Part6Nat.force Block1DivMaps.map70 (x)))))))))
private theorem lhs225_eq : lhs225 = Compressed.eval u225 := by
  funext x
  simp only [lhs225, Block1DivMaps.map3_eq, Block1DivMaps.map14_eq, Block1DivMaps.map63_eq, Block1DivMaps.map64_eq]
  rfl
private theorem rhs225_eq : rhs225 = Compressed.eval v225 := by
  funext x
  simp only [rhs225, Block1DivMaps.map0_eq, Block1DivMaps.map6_eq, Block1DivMaps.map8_eq, Block1DivMaps.map13_eq, Block1DivMaps.map33_eq, Block1DivMaps.map58_eq, Block1DivMaps.map64_eq, Block1DivMaps.map70_eq, Block1DivMaps.map91_eq]
  rfl
private def fastSlice225 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs225 ((100 * b.val + x.val) % 4060) =
      rhs225 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq225 (b : Fin 41) :
    Compressed.slice u225 v225 b = fastSlice225 b := by
  simp only [Compressed.slice, fastSlice225, lhs225_eq, rhs225_eq]
set_option maxHeartbeats 1600000 in
private theorem left225 : u225.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3755).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right225 : v225.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3755)).map Compressed.up0 ++
      (L0Factor 1 3755).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice0 : fastSlice225 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice1 : fastSlice225 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice2 : fastSlice225 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice3 : fastSlice225 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice4 : fastSlice225 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice5 : fastSlice225 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice6 : fastSlice225 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice7 : fastSlice225 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice8 : fastSlice225 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice9 : fastSlice225 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice10 : fastSlice225 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice11 : fastSlice225 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice12 : fastSlice225 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice13 : fastSlice225 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice14 : fastSlice225 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice15 : fastSlice225 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice16 : fastSlice225 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice17 : fastSlice225 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice18 : fastSlice225 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice19 : fastSlice225 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice20 : fastSlice225 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice21 : fastSlice225 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice22 : fastSlice225 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice23 : fastSlice225 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice24 : fastSlice225 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice25 : fastSlice225 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice26 : fastSlice225 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice27 : fastSlice225 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice28 : fastSlice225 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice29 : fastSlice225 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice30 : fastSlice225 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice31 : fastSlice225 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice32 : fastSlice225 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice33 : fastSlice225 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice34 : fastSlice225 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice35 : fastSlice225 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice36 : fastSlice225 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice37 : fastSlice225 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice38 : fastSlice225 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice39 : fastSlice225 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice40 : fastSlice225 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point225 : stepCheck 1 3755 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3755 u225 v225 left225 right225
  intro b
  rw [sliceEq225]
  fin_cases b
  · exact point225slice0
  · exact point225slice1
  · exact point225slice2
  · exact point225slice3
  · exact point225slice4
  · exact point225slice5
  · exact point225slice6
  · exact point225slice7
  · exact point225slice8
  · exact point225slice9
  · exact point225slice10
  · exact point225slice11
  · exact point225slice12
  · exact point225slice13
  · exact point225slice14
  · exact point225slice15
  · exact point225slice16
  · exact point225slice17
  · exact point225slice18
  · exact point225slice19
  · exact point225slice20
  · exact point225slice21
  · exact point225slice22
  · exact point225slice23
  · exact point225slice24
  · exact point225slice25
  · exact point225slice26
  · exact point225slice27
  · exact point225slice28
  · exact point225slice29
  · exact point225slice30
  · exact point225slice31
  · exact point225slice32
  · exact point225slice33
  · exact point225slice34
  · exact point225slice35
  · exact point225slice36
  · exact point225slice37
  · exact point225slice38
  · exact point225slice39
  · exact point225slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
