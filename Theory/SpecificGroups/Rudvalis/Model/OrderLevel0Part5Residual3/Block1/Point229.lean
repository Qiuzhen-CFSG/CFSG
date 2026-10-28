module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.DivMaps
import Mathlib.Tactic.FinCases
/-!
# Rudvalis residual transition 229

Reuse the certified subword tables from part 6. Kernel-checked word expansions
identify the exact target transition, and 41 slices of 100 points certify its
permutation identity. Explicit compositions and division lookups reduce kernel-checking cost.

Source: entry 229 of `Part5Residual.target` and `OrderLevel0Data`.
Adapted from `OrderCertificate/GenerateLevel0Part6Block1Compressed.py`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
open Part6Block1
set_option maxRecDepth 30000
set_option Elab.async false

private def u229 : List (Fin 96) := [90, 58, 46, 50]
private def v229 : List (Fin 96) := [14, 58, 14, 69, 3, 68, 4, 10, 6, 28, 35, 37, 25, 29, 32, 18, 42, 47, 56]
private def lhs229 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map90 (Part6Nat.force Block1DivMaps.map58 (Part6Nat.force Block1DivMaps.map46 (Part6Nat.force Block1DivMaps.map50 (x))))
private def rhs229 (x : Nat) : Nat := Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map58 (Part6Nat.force Block1DivMaps.map14 (Part6Nat.force Block1DivMaps.map69 (Part6Nat.force Block1DivMaps.map3 (Part6Nat.force Block1DivMaps.map68 (Part6Nat.force Block1DivMaps.map4 (Part6Nat.force Block1DivMaps.map10 (Part6Nat.force Block1DivMaps.map6 (Part6Nat.force Block1DivMaps.map28 (Part6Nat.force Block1DivMaps.map35 (Part6Nat.force Block1DivMaps.map37 (Part6Nat.force Block1DivMaps.map25 (Part6Nat.force Block1DivMaps.map29 (Part6Nat.force Block1DivMaps.map32 (Part6Nat.force Block1DivMaps.map18 (Part6Nat.force Block1DivMaps.map42 (Part6Nat.force Block1DivMaps.map47 (Part6Nat.force Block1DivMaps.map56 (x)))))))))))))))))))
private theorem lhs229_eq : lhs229 = Compressed.eval u229 := by
  funext x
  simp only [lhs229, Block1DivMaps.map46_eq, Block1DivMaps.map50_eq, Block1DivMaps.map58_eq, Block1DivMaps.map90_eq]
  rfl
private theorem rhs229_eq : rhs229 = Compressed.eval v229 := by
  funext x
  simp only [rhs229, Block1DivMaps.map3_eq, Block1DivMaps.map4_eq, Block1DivMaps.map6_eq, Block1DivMaps.map10_eq, Block1DivMaps.map14_eq, Block1DivMaps.map18_eq, Block1DivMaps.map25_eq, Block1DivMaps.map28_eq, Block1DivMaps.map29_eq, Block1DivMaps.map32_eq, Block1DivMaps.map35_eq, Block1DivMaps.map37_eq, Block1DivMaps.map42_eq, Block1DivMaps.map47_eq, Block1DivMaps.map56_eq, Block1DivMaps.map58_eq, Block1DivMaps.map68_eq, Block1DivMaps.map69_eq]
  rfl
private def fastSlice229 (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide
    (lhs229 ((100 * b.val + x.val) % 4060) =
      rhs229 ((100 * b.val + x.val) % 4060)))
private theorem sliceEq229 (b : Fin 41) :
    Compressed.slice u229 v229 b = fastSlice229 b := by
  simp only [Compressed.slice, fastSlice229, lhs229_eq, rhs229_eq]
set_option maxHeartbeats 1600000 in
private theorem left229 : u229.flatMap Compressed.word =
    ((0 : Fin 4) :: L0RepWord 3880).map Compressed.up0 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem right229 : v229.flatMap Compressed.word =
    (L0RepWord (L0Act 0 3880)).map Compressed.up0 ++
      (L0Factor 0 3880).map Compressed.up1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice0 : fastSlice229 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice1 : fastSlice229 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice2 : fastSlice229 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice3 : fastSlice229 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice4 : fastSlice229 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice5 : fastSlice229 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice6 : fastSlice229 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice7 : fastSlice229 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice8 : fastSlice229 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice9 : fastSlice229 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice10 : fastSlice229 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice11 : fastSlice229 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice12 : fastSlice229 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice13 : fastSlice229 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice14 : fastSlice229 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice15 : fastSlice229 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice16 : fastSlice229 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice17 : fastSlice229 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice18 : fastSlice229 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice19 : fastSlice229 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice20 : fastSlice229 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice21 : fastSlice229 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice22 : fastSlice229 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice23 : fastSlice229 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice24 : fastSlice229 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice25 : fastSlice229 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice26 : fastSlice229 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice27 : fastSlice229 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice28 : fastSlice229 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice29 : fastSlice229 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice30 : fastSlice229 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice31 : fastSlice229 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice32 : fastSlice229 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice33 : fastSlice229 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice34 : fastSlice229 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice35 : fastSlice229 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice36 : fastSlice229 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice37 : fastSlice229 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice38 : fastSlice229 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice39 : fastSlice229 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point229slice40 : fastSlice229 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem point229 : stepCheck 0 3880 := by
  apply Compressed.ofSlices Compressed.gen_sound 0 3880 u229 v229 left229 right229
  intro b
  rw [sliceEq229]
  fin_cases b
  · exact point229slice0
  · exact point229slice1
  · exact point229slice2
  · exact point229slice3
  · exact point229slice4
  · exact point229slice5
  · exact point229slice6
  · exact point229slice7
  · exact point229slice8
  · exact point229slice9
  · exact point229slice10
  · exact point229slice11
  · exact point229slice12
  · exact point229slice13
  · exact point229slice14
  · exact point229slice15
  · exact point229slice16
  · exact point229slice17
  · exact point229slice18
  · exact point229slice19
  · exact point229slice20
  · exact point229slice21
  · exact point229slice22
  · exact point229slice23
  · exact point229slice24
  · exact point229slice25
  · exact point229slice26
  · exact point229slice27
  · exact point229slice28
  · exact point229slice29
  · exact point229slice30
  · exact point229slice31
  · exact point229slice32
  · exact point229slice33
  · exact point229slice34
  · exact point229slice35
  · exact point229slice36
  · exact point229slice37
  · exact point229slice38
  · exact point229slice39
  · exact point229slice40

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
