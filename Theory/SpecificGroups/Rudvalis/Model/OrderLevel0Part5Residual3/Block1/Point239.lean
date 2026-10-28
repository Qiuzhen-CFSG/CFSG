module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 239

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 239 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u239 : List (Fin 96) := [33, 58, 46, 50]
private def v239 : List (Fin 96) := [14, 77, 46, 78, 4, 20, 40, 94, 29, 23, 53, 80, 29, 49, 86]
private def lhs239 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map33 (Part6Nat.force Block1DivMaps.map58 (Part6Nat.force Block1DivMaps.map46 (Part6Nat.force Block1DivMaps.map50 (x))))
private def rhs239 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map77 (Part6Nat.force Block1DivMaps.map46 (Part6Nat.force Block1DivMaps.map78 (Part6Nat.force Block1DivMaps.map4 (Part6Nat.force Block1DivMaps.map20 (Part6Nat.force Block1DivMaps.map40 (Part6Nat.force Block1DivMaps.map94 (Part6Nat.force Block1DivMaps.map29 (Part6Nat.force Block1DivMaps.map23 (Part6Nat.force Block1DivMaps.map53 (Part6Nat.force Block1DivMaps.map80 (Part6Nat.force Block1DivMaps.map29 (Part6Nat.force Block1DivMaps.map49 (Part6Nat.force Block1DivMaps.map86 (x)))))))))))))))
private theorem lhs239_eq : lhs239 = Compressed.eval u239 := by
  funext x
  simp only [lhs239, Block1DivMaps.map33_eq, Block1DivMaps.map46_eq, Block1DivMaps.map50_eq, Block1DivMaps.map58_eq]
  rfl
private theorem rhs239_eq : rhs239 = Compressed.eval v239 := by
  funext x
  simp only [rhs239, Block1DivMaps.map4_eq, Block1DivMaps.map14_eq, Block1DivMaps.map20_eq, Block1DivMaps.map23_eq, Block1DivMaps.map29_eq, Block1DivMaps.map40_eq, Block1DivMaps.map46_eq, Block1DivMaps.map49_eq, Block1DivMaps.map53_eq, Block1DivMaps.map77_eq, Block1DivMaps.map78_eq, Block1DivMaps.map80_eq, Block1DivMaps.map86_eq, Block1DivMaps.map94_eq]
  rfl
private def fastSlice239 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs239 ((100 * b.val + x.val) % 4060) =
      rhs239 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq239 (b : Fin 41) :
    Compressed.slice u239 v239 b = fastSlice239 b := by
  simp only [Compressed.slice, fastSlice239, lhs239_eq, rhs239_eq]
set_option maxHeartbeats 1600000 in
private theorem left239 : u239.flatMap Compressed.word =
    ((1 : Fin 4) :: L0RepWord 3880).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right239 : v239.flatMap Compressed.word =
    (L0RepWord (L0Act 1 3880)).map Compressed.up0 ++
      (L0Factor 1 3880).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice0 : fastSlice239 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice1 : fastSlice239 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice2 : fastSlice239 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice3 : fastSlice239 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice4 : fastSlice239 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice5 : fastSlice239 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice6 : fastSlice239 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice7 : fastSlice239 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice8 : fastSlice239 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice9 : fastSlice239 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice10 : fastSlice239 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice11 : fastSlice239 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice12 : fastSlice239 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice13 : fastSlice239 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice14 : fastSlice239 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice15 : fastSlice239 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice16 : fastSlice239 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice17 : fastSlice239 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice18 : fastSlice239 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice19 : fastSlice239 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice20 : fastSlice239 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice21 : fastSlice239 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice22 : fastSlice239 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice23 : fastSlice239 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice24 : fastSlice239 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice25 : fastSlice239 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice26 : fastSlice239 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice27 : fastSlice239 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice28 : fastSlice239 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice29 : fastSlice239 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice30 : fastSlice239 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice31 : fastSlice239 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice32 : fastSlice239 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice33 : fastSlice239 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice34 : fastSlice239 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice35 : fastSlice239 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice36 : fastSlice239 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice37 : fastSlice239 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice38 : fastSlice239 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice39 : fastSlice239 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point239slice40 : fastSlice239 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point239 : stepCheck 1 3880 := by
  apply Compressed.ofSlices Compressed.gen_sound 1 3880 u239 v239 left239 right239
  intro b
  rw [sliceEq239]
  fin_cases b
  · exact point239slice0
  · exact point239slice1
  · exact point239slice2
  · exact point239slice3
  · exact point239slice4
  · exact point239slice5
  · exact point239slice6
  · exact point239slice7
  · exact point239slice8
  · exact point239slice9
  · exact point239slice10
  · exact point239slice11
  · exact point239slice12
  · exact point239slice13
  · exact point239slice14
  · exact point239slice15
  · exact point239slice16
  · exact point239slice17
  · exact point239slice18
  · exact point239slice19
  · exact point239slice20
  · exact point239slice21
  · exact point239slice22
  · exact point239slice23
  · exact point239slice24
  · exact point239slice25
  · exact point239slice26
  · exact point239slice27
  · exact point239slice28
  · exact point239slice29
  · exact point239slice30
  · exact point239slice31
  · exact point239slice32
  · exact point239slice33
  · exact point239slice34
  · exact point239slice35
  · exact point239slice36
  · exact point239slice37
  · exact point239slice38
  · exact point239slice39
  · exact point239slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
