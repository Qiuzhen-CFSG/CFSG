module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Data

/-!
# Coordinate independence of the exterior and radical families

The first 1221 upper-triangle coordinates of the original exterior family
form the identity matrix. Ten of these coordinates also extract the ten
literal radical coefficients. The finite checks below certify those two
identity blocks, without group-order or invariance assumptions.

Source: `IntrinsicAlgebra/source/README.md` and the reproducible
`Scratch/J4FleetGuidance/SeedCentralizer/explore.py` calculation.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

/-- The first 1221 lexicographic strict upper-triangle positions. -/
def exteriorCoordinatePair (k : Fin 1221) : Fin 112 × Fin 112 :=
  if h0 : k.val < 111 then (⟨0, by omega⟩, ⟨k.val - 0 + 1, by omega⟩) else
  if h1 : k.val < 221 then (⟨1, by omega⟩, ⟨k.val - 111 + 2, by omega⟩) else
  if h2 : k.val < 330 then (⟨2, by omega⟩, ⟨k.val - 221 + 3, by omega⟩) else
  if h3 : k.val < 438 then (⟨3, by omega⟩, ⟨k.val - 330 + 4, by omega⟩) else
  if h4 : k.val < 545 then (⟨4, by omega⟩, ⟨k.val - 438 + 5, by omega⟩) else
  if h5 : k.val < 651 then (⟨5, by omega⟩, ⟨k.val - 545 + 6, by omega⟩) else
  if h6 : k.val < 756 then (⟨6, by omega⟩, ⟨k.val - 651 + 7, by omega⟩) else
  if h7 : k.val < 860 then (⟨7, by omega⟩, ⟨k.val - 756 + 8, by omega⟩) else
  if h8 : k.val < 963 then (⟨8, by omega⟩, ⟨k.val - 860 + 9, by omega⟩) else
  if h9 : k.val < 1065 then (⟨9, by omega⟩, ⟨k.val - 963 + 10, by omega⟩) else
  if h10 : k.val < 1166 then (⟨10, by omega⟩, ⟨k.val - 1065 + 11, by omega⟩) else
  (⟨11, by omega⟩, ⟨k.val - 1166 + 12, by omega⟩)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem exteriorCoordinatePair_spec : ∀ k : Fin 1221,
    (exteriorCoordinatePair k).1 < (exteriorCoordinatePair k).2 ∧
    exteriorIndex (exteriorCoordinatePair k).1 (exteriorCoordinatePair k).2 = k.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem exteriorRows_initial : ∀ i : Fin 1221,
    exteriorFormRows.get i % 2^1221 = 2^i.val := by
  decide +kernel

/-- The original exterior forms have an actual identity coordinate block. -/
theorem exteriorBasisForm_coordinate (i j : Fin 1221) :
    exteriorBasisForm i (exteriorCoordinatePair j).1 (exteriorCoordinatePair j).2 =
      if i = j then 1 else 0 := by
  have h := congrArg (fun r : ℕ => r.testBit j.val) (exteriorRows_initial i)
  simp only [Nat.testBit_mod_two_pow, j.isLt, decide_true, Bool.true_and,
    Nat.testBit_two_pow] at h
  simp only [exteriorBasisForm, decodeExteriorForm,
    (exteriorCoordinatePair_spec j).1, if_true, (exteriorCoordinatePair_spec j).2,
    h, decide_eq_true_eq, Fin.ext_iff]

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
