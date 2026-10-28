module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose.Masks
import Mathlib.Tactic.FinCases

/-!
# Certified address routing for the block transpose

Sixteen bounded certificates cover the 128 possible output rows, checking
every column address in each row. Their assembly proves that output address
`128*i+j` has exactly the single input address `128*j+i`. The symbolic routing
semantics then applies this identity to every natural number, independently
of the HS numerical data. See `source/README.md` for the measured checks.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose

private def routeCheck (start count : ℕ) : Bool :=
  (List.range count).all fun i => (List.range 128).all fun j =>
    route stages128 (128 * (start + i) + j) == [128 * j + (start + i)]

private theorem routeChunk00 : routeCheck 0 8 = true := by decide +kernel

private theorem routeChunk01 : routeCheck 8 8 = true := by decide +kernel

private theorem routeChunk02 : routeCheck 16 8 = true := by decide +kernel

private theorem routeChunk03 : routeCheck 24 8 = true := by decide +kernel

private theorem routeChunk04 : routeCheck 32 8 = true := by decide +kernel

private theorem routeChunk05 : routeCheck 40 8 = true := by decide +kernel

private theorem routeChunk06 : routeCheck 48 8 = true := by decide +kernel

private theorem routeChunk07 : routeCheck 56 8 = true := by decide +kernel

private theorem routeChunk08 : routeCheck 64 8 = true := by decide +kernel

private theorem routeChunk09 : routeCheck 72 8 = true := by decide +kernel

private theorem routeChunk10 : routeCheck 80 8 = true := by decide +kernel

private theorem routeChunk11 : routeCheck 88 8 = true := by decide +kernel

private theorem routeChunk12 : routeCheck 96 8 = true := by decide +kernel

private theorem routeChunk13 : routeCheck 104 8 = true := by decide +kernel

private theorem routeChunk14 : routeCheck 112 8 = true := by decide +kernel

private theorem routeChunk15 : routeCheck 120 8 = true := by decide +kernel

private theorem routeChecks (k : Fin 16) : routeCheck (8 * k.val) 8 = true := by
  fin_cases k
  · exact routeChunk00
  · exact routeChunk01
  · exact routeChunk02
  · exact routeChunk03
  · exact routeChunk04
  · exact routeChunk05
  · exact routeChunk06
  · exact routeChunk07
  · exact routeChunk08
  · exact routeChunk09
  · exact routeChunk10
  · exact routeChunk11
  · exact routeChunk12
  · exact routeChunk13
  · exact routeChunk14
  · exact routeChunk15

/-- Every address in a 128-by-128 block is routed to its transpose. -/
theorem routes_correct (i j : Fin 128) :
    route stages128 (128 * i.val + j.val) = [128 * j.val + i.val] := by
  let k : Fin 16 := ⟨i.val / 8, by omega⟩
  have hi := List.all_eq_true.mp (routeChecks k) (i.val % 8)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hj := List.all_eq_true.mp hi j.val (List.mem_range.mpr j.isLt)
  have he : 8 * k.val + i.val % 8 = i.val := by dsimp [k]; omega
  simpa only [he, beq_iff_eq] using hj

/-- The bit-routing certificate is valid for arbitrary block data. -/
theorem testBit_transpose (x : ℕ) (i j : Fin 128) :
    (permute stages128 x).testBit (128 * i.val + j.val) =
      x.testBit (128 * j.val + i.val) := by
  rw [testBit_permute, routes_correct]
  simp

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose
