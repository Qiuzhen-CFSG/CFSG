/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryBinaryComparisonData.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.TernaryGolaySupports
public import Theory.AtlasPort.OtherSporadic.Codes.GolayBasis

/-!
# TernaryBinaryComparisonData

Explicit coordinate markings and binary masks connect ternary Golay
coordinates to words of the binary Golay code. Kernel-checked generator
identities verify the lift basis and the distinguished comparison words.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryBinaryComparisonData.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

/-- Integer masks use the retained ((3 × 2) × 4) Golay coordinate marking. -/
def comparisonBinaryMask (n : ℕ) : BinaryWord := fun p =>
  if n.testBit (8*p.1.1.val + 4*p.1.2.val + p.2.val) then 1 else 0

def comparisonBinaryCoefficients (n : ℕ) : BinaryWord :=
  ∑ i : Fin 12, (if n.testBit i.val then (1 : Bit) else 0) • golayGenerators i

theorem comparisonBinaryCoefficients_mem (n : ℕ) : comparisonBinaryCoefficients n ∈ golay := by
  apply golay.sum_mem
  intro i _
  apply golay.smul_mem
  rw [← golayBasis_coe]
  exact (golayBasis i).prop

/-- The explicit twelve-coordinate comparison, in ternary-coordinate order. -/
def ternaryBinaryPosition : Fin 12 → Omega :=
  ![((0,0),1), ((0,0),3), ((0,1),1), ((0,1),3), ((1,0),1), ((2,0),1),
    ((1,1),3), ((2,1),1), ((1,1),1), ((2,1),3), ((1,0),3), ((2,0),3)]

theorem ternaryBinaryPosition_injective : Function.Injective ternaryBinaryPosition := by decide

def ternaryBinaryLiftParameters : Fin 11 → ℕ :=
  ![3458,386,1205,3890,3265,2503,2366,359,1017,3744,1926]

def ternaryBinaryLiftMasks : Fin 11 → ℕ :=
  ![1917970,808204,6030688,1589716,1905220,4932676,5079316,7098448,603472,14160916,5855488]

def ternaryBinaryLiftBasis (i : Fin 11) : BinaryWord :=
  comparisonBinaryMask (ternaryBinaryLiftMasks i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Eleven small binary linear identities; kernel reduction checks every coordinate.
theorem ternaryBinaryLiftBasis_eq : ∀ i, ternaryBinaryLiftBasis i =
    comparisonBinaryCoefficients (ternaryBinaryLiftParameters i) := by decide +kernel

theorem ternaryBinaryLiftBasis_mem (i : Fin 11) : ternaryBinaryLiftBasis i ∈ golay := by
  rw [ternaryBinaryLiftBasis_eq]
  exact comparisonBinaryCoefficients_mem _

def ternaryBinaryDodecadWord : BinaryWord := comparisonBinaryMask 11184810

def ternaryBinaryComplementWord : BinaryWord := comparisonBinaryMask 5592405

theorem ternaryBinaryDodecadWord_mem : ternaryBinaryDodecadWord ∈ golay := by
  have he : ternaryBinaryDodecadWord = comparisonBinaryCoefficients 7 := by decide +kernel
  rw [he]; exact comparisonBinaryCoefficients_mem _

theorem ternaryBinaryComplementWord_mem : ternaryBinaryComplementWord ∈ golay := by
  have he : ternaryBinaryComplementWord = comparisonBinaryCoefficients 1991 := by decide +kernel
  rw [he]; exact comparisonBinaryCoefficients_mem _

/-- Extend the first eleven trace coordinates linearly using actual Golay words. -/
def ternaryBinaryRawLift (u : TernaryWord) : BinaryWord :=
  ∑ i : Fin 11, (if u i.castSucc ≠ 0 then (1 : Bit) else 0) • ternaryBinaryLiftBasis i

def ternaryBinaryOctadWord (u : TernaryWord) : BinaryWord :=
  let w := ternaryBinaryRawLift u
  if hammingNorm w = 8 then w else w + ternaryBinaryComplementWord

theorem ternaryBinaryRawLift_mem (u : TernaryWord) : ternaryBinaryRawLift u ∈ golay := by
  apply golay.sum_mem
  intro i _
  exact golay.smul_mem _ (ternaryBinaryLiftBasis_mem i)

theorem ternaryBinaryOctadWord_mem (u : TernaryWord) : ternaryBinaryOctadWord u ∈ golay := by
  unfold ternaryBinaryOctadWord
  dsimp only
  split_ifs
  · exact ternaryBinaryRawLift_mem u
  · exact golay.add_mem (ternaryBinaryRawLift_mem u) ternaryBinaryComplementWord_mem

end Atlas.Codes
