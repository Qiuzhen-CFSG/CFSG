module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 234

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 234 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u234 : List (Fin 96) := [90, 14, 66, 46]
private def v234 : List (Fin 96) := [65, 21, 69, 36, 17, 15, 91, 37, 25, 29, 42, 47]
private def lhs234 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map90 (Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map66 (Part6Nat.force Block1DivMaps.map46 (x))))
private def rhs234 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map65 (Part6Nat.force Block1DivMaps.map21 (Part6Nat.force Block1DivMaps.map69 (Part6Nat.force Block1DivMaps.map36 (Part6Nat.force Block1DivMaps.map17 (Part6Nat.force Block1DivMaps.map15 (Part6Nat.force Block1DivMaps.map91 (Part6Nat.force Block1DivMaps.map37 (Part6Nat.force Block1DivMaps.map25 (Part6Nat.force Block1DivMaps.map29 (Part6Nat.force Block1DivMaps.map42 (Part6Nat.force Block1DivMaps.map47 (x))))))))))))
private theorem lhs234_eq : lhs234 = Compressed.eval u234 := by
  funext x
  simp only [lhs234, Block1DivMaps.map14_eq, Block1DivMaps.map46_eq, Block1DivMaps.map66_eq, Block1DivMaps.map90_eq]
  rfl
private theorem rhs234_eq : rhs234 = Compressed.eval v234 := by
  funext x
  simp only [rhs234, Block1DivMaps.map15_eq, Block1DivMaps.map17_eq, Block1DivMaps.map21_eq, Block1DivMaps.map25_eq, Block1DivMaps.map29_eq, Block1DivMaps.map36_eq, Block1DivMaps.map37_eq, Block1DivMaps.map42_eq, Block1DivMaps.map47_eq, Block1DivMaps.map65_eq, Block1DivMaps.map69_eq, Block1DivMaps.map91_eq]
  rfl
private def fastSlice234 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs234 ((100 * b.val + x.val) % 4060) =
      rhs234 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq234 (b : Fin 41) :
    Compressed.slice u234 v234 b = fastSlice234 b := by
  simp only [Compressed.slice, fastSlice234, lhs234_eq, rhs234_eq]
set_option maxHeartbeats 1600000 in
private theorem left234 : u234.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3893).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right234 : v234.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3893)).map Compressed.up0 ++
      (L0Factor 0 3893).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice0 : fastSlice234 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice1 : fastSlice234 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice2 : fastSlice234 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice3 : fastSlice234 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice4 : fastSlice234 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice5 : fastSlice234 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice6 : fastSlice234 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice7 : fastSlice234 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice8 : fastSlice234 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice9 : fastSlice234 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice10 : fastSlice234 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice11 : fastSlice234 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice12 : fastSlice234 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice13 : fastSlice234 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice14 : fastSlice234 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice15 : fastSlice234 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice16 : fastSlice234 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice17 : fastSlice234 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice18 : fastSlice234 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice19 : fastSlice234 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice20 : fastSlice234 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice21 : fastSlice234 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice22 : fastSlice234 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice23 : fastSlice234 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice24 : fastSlice234 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice25 : fastSlice234 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice26 : fastSlice234 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice27 : fastSlice234 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice28 : fastSlice234 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice29 : fastSlice234 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice30 : fastSlice234 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice31 : fastSlice234 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice32 : fastSlice234 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice33 : fastSlice234 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice34 : fastSlice234 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice35 : fastSlice234 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice36 : fastSlice234 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice37 : fastSlice234 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice38 : fastSlice234 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice39 : fastSlice234 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point234slice40 : fastSlice234 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point234 : stepCheck 0 3893 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3893 u234 v234 left234 right234
  intro b
  rw [sliceEq234]
  fin_cases b
  · exact point234slice0
  · exact point234slice1
  · exact point234slice2
  · exact point234slice3
  · exact point234slice4
  · exact point234slice5
  · exact point234slice6
  · exact point234slice7
  · exact point234slice8
  · exact point234slice9
  · exact point234slice10
  · exact point234slice11
  · exact point234slice12
  · exact point234slice13
  · exact point234slice14
  · exact point234slice15
  · exact point234slice16
  · exact point234slice17
  · exact point234slice18
  · exact point234slice19
  · exact point234slice20
  · exact point234slice21
  · exact point234slice22
  · exact point234slice23
  · exact point234slice24
  · exact point234slice25
  · exact point234slice26
  · exact point234slice27
  · exact point234slice28
  · exact point234slice29
  · exact point234slice30
  · exact point234slice31
  · exact point234slice32
  · exact point234slice33
  · exact point234slice34
  · exact point234slice35
  · exact point234slice36
  · exact point234slice37
  · exact point234slice38
  · exact point234slice39
  · exact point234slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
