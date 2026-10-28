module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 224

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 224 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u224 : List (Fin 96) := [50, 46, 63, 14, 3]
private def v224 : List (Fin 96) := [0, 63, 63, 14, 3, 36, 8, 6, 15, 18, 18, 42, 47, 56]
private def lhs224 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map50 (Part6Nat.force Block1DivMaps.map46 (Part6Nat.force Block1DivMaps.map63 (Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map3 (x)))))
private def rhs224 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map0 (Part6Nat.force Block1DivMaps.map63 (Part6Nat.force Block1DivMaps.map63 (Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map3 (Part6Nat.force Block1DivMaps.map36 (Part6Nat.force Block1DivMaps.map8 (Part6Nat.force Block1DivMaps.map6 (Part6Nat.force Block1DivMaps.map15 (Part6Nat.force Block1DivMaps.map18 (Part6Nat.force Block1DivMaps.map18 (Part6Nat.force Block1DivMaps.map42 (Part6Nat.force Block1DivMaps.map47 (Part6Nat.force Block1DivMaps.map56 (x))))))))))))))
private theorem lhs224_eq : lhs224 = Compressed.eval u224 := by
  funext x
  simp only [lhs224, Block1DivMaps.map3_eq, Block1DivMaps.map14_eq, Block1DivMaps.map46_eq, Block1DivMaps.map50_eq, Block1DivMaps.map63_eq]
  rfl
private theorem rhs224_eq : rhs224 = Compressed.eval v224 := by
  funext x
  simp only [rhs224, Block1DivMaps.map0_eq, Block1DivMaps.map3_eq, Block1DivMaps.map6_eq, Block1DivMaps.map8_eq, Block1DivMaps.map14_eq, Block1DivMaps.map15_eq, Block1DivMaps.map18_eq, Block1DivMaps.map36_eq, Block1DivMaps.map42_eq, Block1DivMaps.map47_eq, Block1DivMaps.map56_eq, Block1DivMaps.map63_eq]
  rfl
private def fastSlice224 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs224 ((100 * b.val + x.val) % 4060) =
      rhs224 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq224 (b : Fin 41) :
    Compressed.slice u224 v224 b = fastSlice224 b := by
  simp only [Compressed.slice, fastSlice224, lhs224_eq, rhs224_eq]
set_option maxHeartbeats 1600000 in
private theorem left224 : u224.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3754).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right224 : v224.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3754)).map Compressed.up0 ++
      (L0Factor 1 3754).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice0 : fastSlice224 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice1 : fastSlice224 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice2 : fastSlice224 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice3 : fastSlice224 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice4 : fastSlice224 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice5 : fastSlice224 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice6 : fastSlice224 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice7 : fastSlice224 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice8 : fastSlice224 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice9 : fastSlice224 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice10 : fastSlice224 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice11 : fastSlice224 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice12 : fastSlice224 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice13 : fastSlice224 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice14 : fastSlice224 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice15 : fastSlice224 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice16 : fastSlice224 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice17 : fastSlice224 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice18 : fastSlice224 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice19 : fastSlice224 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice20 : fastSlice224 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice21 : fastSlice224 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice22 : fastSlice224 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice23 : fastSlice224 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice24 : fastSlice224 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice25 : fastSlice224 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice26 : fastSlice224 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice27 : fastSlice224 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice28 : fastSlice224 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice29 : fastSlice224 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice30 : fastSlice224 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice31 : fastSlice224 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice32 : fastSlice224 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice33 : fastSlice224 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice34 : fastSlice224 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice35 : fastSlice224 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice36 : fastSlice224 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice37 : fastSlice224 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice38 : fastSlice224 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice39 : fastSlice224 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice40 : fastSlice224 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point224 : stepCheck 1 3754 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3754 u224 v224 left224 right224
  intro b
  rw [sliceEq224]
  fin_cases b
  · exact point224slice0
  · exact point224slice1
  · exact point224slice2
  · exact point224slice3
  · exact point224slice4
  · exact point224slice5
  · exact point224slice6
  · exact point224slice7
  · exact point224slice8
  · exact point224slice9
  · exact point224slice10
  · exact point224slice11
  · exact point224slice12
  · exact point224slice13
  · exact point224slice14
  · exact point224slice15
  · exact point224slice16
  · exact point224slice17
  · exact point224slice18
  · exact point224slice19
  · exact point224slice20
  · exact point224slice21
  · exact point224slice22
  · exact point224slice23
  · exact point224slice24
  · exact point224slice25
  · exact point224slice26
  · exact point224slice27
  · exact point224slice28
  · exact point224slice29
  · exact point224slice30
  · exact point224slice31
  · exact point224slice32
  · exact point224slice33
  · exact point224slice34
  · exact point224slice35
  · exact point224slice36
  · exact point224slice37
  · exact point224slice38
  · exact point224slice39
  · exact point224slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
