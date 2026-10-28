module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 230

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 230 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u230 : List (Fin 96) := [0, 64, 64, 50]
private def v230 : List (Fin 96) := [78, 14, 33, 24, 60, 11, 36, 15, 84, 42, 30, 83, 52]
private def lhs230 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map0 (Part6Nat.force Block1DivMaps.map64 (Part6Nat.force Block1DivMaps.map64 (Part6Nat.force Block1DivMaps.map50 (x))))
private def rhs230 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map78 (Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map33 (Part6Nat.force Block1DivMaps.map24 (Part6Nat.force Block1DivMaps.map60 (Part6Nat.force Block1DivMaps.map11 (Part6Nat.force Block1DivMaps.map36 (Part6Nat.force Block1DivMaps.map15 (Part6Nat.force Block1DivMaps.map84 (Part6Nat.force Block1DivMaps.map42 (Part6Nat.force Block1DivMaps.map30 (Part6Nat.force Block1DivMaps.map83 (Part6Nat.force Block1DivMaps.map52 (x)))))))))))))
private theorem lhs230_eq : lhs230 = Compressed.eval u230 := by
  funext x
  simp only [lhs230, Block1DivMaps.map0_eq, Block1DivMaps.map50_eq, Block1DivMaps.map64_eq]
  rfl
private theorem rhs230_eq : rhs230 = Compressed.eval v230 := by
  funext x
  simp only [rhs230, Block1DivMaps.map11_eq, Block1DivMaps.map14_eq, Block1DivMaps.map15_eq, Block1DivMaps.map24_eq, Block1DivMaps.map30_eq, Block1DivMaps.map33_eq, Block1DivMaps.map36_eq, Block1DivMaps.map42_eq, Block1DivMaps.map52_eq, Block1DivMaps.map60_eq, Block1DivMaps.map78_eq, Block1DivMaps.map83_eq, Block1DivMaps.map84_eq]
  rfl
private def fastSlice230 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs230 ((100 * b.val + x.val) % 4060) =
      rhs230 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq230 (b : Fin 41) :
    Compressed.slice u230 v230 b = fastSlice230 b := by
  simp only [Compressed.slice, fastSlice230, lhs230_eq, rhs230_eq]
set_option maxHeartbeats 1600000 in
private theorem left230 : u230.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3881).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right230 : v230.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3881)).map Compressed.up0 ++
      (L0Factor 0 3881).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice0 : fastSlice230 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice1 : fastSlice230 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice2 : fastSlice230 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice3 : fastSlice230 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice4 : fastSlice230 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice5 : fastSlice230 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice6 : fastSlice230 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice7 : fastSlice230 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice8 : fastSlice230 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice9 : fastSlice230 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice10 : fastSlice230 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice11 : fastSlice230 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice12 : fastSlice230 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice13 : fastSlice230 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice14 : fastSlice230 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice15 : fastSlice230 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice16 : fastSlice230 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice17 : fastSlice230 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice18 : fastSlice230 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice19 : fastSlice230 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice20 : fastSlice230 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice21 : fastSlice230 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice22 : fastSlice230 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice23 : fastSlice230 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice24 : fastSlice230 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice25 : fastSlice230 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice26 : fastSlice230 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice27 : fastSlice230 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice28 : fastSlice230 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice29 : fastSlice230 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice30 : fastSlice230 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice31 : fastSlice230 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice32 : fastSlice230 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice33 : fastSlice230 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice34 : fastSlice230 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice35 : fastSlice230 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice36 : fastSlice230 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice37 : fastSlice230 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice38 : fastSlice230 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice39 : fastSlice230 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice40 : fastSlice230 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point230 : stepCheck 0 3881 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3881 u230 v230 left230 right230
  intro b
  rw [sliceEq230]
  fin_cases b
  · exact point230slice0
  · exact point230slice1
  · exact point230slice2
  · exact point230slice3
  · exact point230slice4
  · exact point230slice5
  · exact point230slice6
  · exact point230slice7
  · exact point230slice8
  · exact point230slice9
  · exact point230slice10
  · exact point230slice11
  · exact point230slice12
  · exact point230slice13
  · exact point230slice14
  · exact point230slice15
  · exact point230slice16
  · exact point230slice17
  · exact point230slice18
  · exact point230slice19
  · exact point230slice20
  · exact point230slice21
  · exact point230slice22
  · exact point230slice23
  · exact point230slice24
  · exact point230slice25
  · exact point230slice26
  · exact point230slice27
  · exact point230slice28
  · exact point230slice29
  · exact point230slice30
  · exact point230slice31
  · exact point230slice32
  · exact point230slice33
  · exact point230slice34
  · exact point230slice35
  · exact point230slice36
  · exact point230slice37
  · exact point230slice38
  · exact point230slice39
  · exact point230slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
