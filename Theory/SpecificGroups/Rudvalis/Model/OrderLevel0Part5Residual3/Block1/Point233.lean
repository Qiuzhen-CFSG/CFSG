module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 233

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 233 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u233 : List (Fin 96) := [67, 50, 33, 58, 14]
private def v233 : List (Fin 96) := [50, 33, 66, 12, 4, 36, 11, 35, 48, 23, 10, 39, 18, 7]
private def lhs233 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map67 (Part6Nat.force Block1DivMaps.map50 (Part6Nat.force Block1DivMaps.map33 (Part6Nat.force Block1DivMaps.map58 (Part6Nat.force Block1DivMaps.map14 (x)))))
private def rhs233 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map50 (Part6Nat.force Block1DivMaps.map33 (Part6Nat.force Block1DivMaps.map66 (Part6Nat.force Block1DivMaps.map12 (Part6Nat.force Block1DivMaps.map4 (Part6Nat.force Block1DivMaps.map36 (Part6Nat.force Block1DivMaps.map11 (Part6Nat.force Block1DivMaps.map35 (Part6Nat.force Block1DivMaps.map48 (Part6Nat.force Block1DivMaps.map23 (Part6Nat.force Block1DivMaps.map10 (Part6Nat.force Block1DivMaps.map39 (Part6Nat.force Block1DivMaps.map18 (Part6Nat.force Block1DivMaps.map7 (x))))))))))))))
private theorem lhs233_eq : lhs233 = Compressed.eval u233 := by
  funext x
  simp only [lhs233, Block1DivMaps.map14_eq, Block1DivMaps.map33_eq, Block1DivMaps.map50_eq, Block1DivMaps.map58_eq, Block1DivMaps.map67_eq]
  rfl
private theorem rhs233_eq : rhs233 = Compressed.eval v233 := by
  funext x
  simp only [rhs233, Block1DivMaps.map4_eq, Block1DivMaps.map7_eq, Block1DivMaps.map10_eq, Block1DivMaps.map11_eq, Block1DivMaps.map12_eq, Block1DivMaps.map18_eq, Block1DivMaps.map23_eq, Block1DivMaps.map33_eq, Block1DivMaps.map35_eq, Block1DivMaps.map36_eq, Block1DivMaps.map39_eq, Block1DivMaps.map48_eq, Block1DivMaps.map50_eq, Block1DivMaps.map66_eq]
  rfl
private def fastSlice233 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs233 ((100 * b.val + x.val) % 4060) =
      rhs233 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq233 (b : Fin 41) :
    Compressed.slice u233 v233 b = fastSlice233 b := by
  simp only [Compressed.slice, fastSlice233, lhs233_eq, rhs233_eq]
set_option maxHeartbeats 1600000 in
private theorem left233 : u233.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3890).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right233 : v233.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3890)).map Compressed.up0 ++
      (L0Factor 0 3890).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice0 : fastSlice233 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice1 : fastSlice233 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice2 : fastSlice233 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice3 : fastSlice233 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice4 : fastSlice233 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice5 : fastSlice233 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice6 : fastSlice233 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice7 : fastSlice233 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice8 : fastSlice233 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice9 : fastSlice233 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice10 : fastSlice233 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice11 : fastSlice233 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice12 : fastSlice233 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice13 : fastSlice233 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice14 : fastSlice233 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice15 : fastSlice233 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice16 : fastSlice233 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice17 : fastSlice233 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice18 : fastSlice233 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice19 : fastSlice233 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice20 : fastSlice233 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice21 : fastSlice233 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice22 : fastSlice233 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice23 : fastSlice233 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice24 : fastSlice233 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice25 : fastSlice233 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice26 : fastSlice233 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice27 : fastSlice233 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice28 : fastSlice233 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice29 : fastSlice233 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice30 : fastSlice233 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice31 : fastSlice233 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice32 : fastSlice233 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice33 : fastSlice233 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice34 : fastSlice233 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice35 : fastSlice233 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice36 : fastSlice233 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice37 : fastSlice233 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice38 : fastSlice233 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice39 : fastSlice233 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point233slice40 : fastSlice233 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point233 : stepCheck 0 3890 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3890 u233 v233 left233 right233
  intro b
  rw [sliceEq233]
  fin_cases b
  · exact point233slice0
  · exact point233slice1
  · exact point233slice2
  · exact point233slice3
  · exact point233slice4
  · exact point233slice5
  · exact point233slice6
  · exact point233slice7
  · exact point233slice8
  · exact point233slice9
  · exact point233slice10
  · exact point233slice11
  · exact point233slice12
  · exact point233slice13
  · exact point233slice14
  · exact point233slice15
  · exact point233slice16
  · exact point233slice17
  · exact point233slice18
  · exact point233slice19
  · exact point233slice20
  · exact point233slice21
  · exact point233slice22
  · exact point233slice23
  · exact point233slice24
  · exact point233slice25
  · exact point233slice26
  · exact point233slice27
  · exact point233slice28
  · exact point233slice29
  · exact point233slice30
  · exact point233slice31
  · exact point233slice32
  · exact point233slice33
  · exact point233slice34
  · exact point233slice35
  · exact point233slice36
  · exact point233slice37
  · exact point233slice38
  · exact point233slice39
  · exact point233slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
