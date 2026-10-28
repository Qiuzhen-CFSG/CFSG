/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleBase.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.NormSixVector
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalPairGeometry
public import Theory.AtlasPort.OtherSporadic.Conway.OddPointStabilizerOrbits
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleBase.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem oddMinimumVector_zero_apply (a i : Omega) :
    (oddMinimumVector a 0).val i = if i = a then -3 else 1 := by
  rw [oddMinimumVector_zero]
  by_cases h : i = a <;> simp [oddProfileBase,h]

theorem oddMinimumVector_norm (a : Omega) :
    integerDot (oddMinimumVector a 0).val (oddMinimumVector a 0).val = 32 := by
  simpa [oddMinimumVector] using signedOddProfile_norm {a} ∅ (by simp) (0 : golay)

theorem normSix_sub_oddMinimum (a : Omega) :
    normSixVector a - oddMinimumVector a 0 = coordinateEight a := by
  apply Subtype.ext
  funext i
  change (normSixVector a).val i - (oddMinimumVector a 0).val i = _
  rw [normSixVector_apply,oddMinimumVector_zero_apply]
  change (if i = a then 5 else 1) - (if i = a then -3 else 1) =
    coordinateVector a 8 i
  by_cases h : i = a <;> simp [coordinateVector,h]

theorem co3_base_triangle_norms (a : Omega) :
    integerDot (oddMinimumVector a 0).val (oddMinimumVector a 0).val = 32 ∧
    integerDot (normSixVector a - oddMinimumVector a 0).val
      (normSixVector a - oddMinimumVector a 0).val = 64 := by
  refine ⟨oddMinimumVector_norm a,?_⟩
  rw [normSix_sub_oddMinimum]
  change integerDot (coordinateVector a 8) (coordinateVector a 8) = 64
  rw [integerDot_coordinateVector]; simp [coordinateVector]

/-- The corrected point-type decomposition uses two entries equal to four. -/
theorem normSix_point_decomposition (a b : Omega) (hab : a ≠ b) :
    minimumPairPlus a b + oddMinimumVector b 0 = normSixVector a := by
  apply Subtype.ext
  funext i
  change (minimumPairPlus a b).val i + (oddMinimumVector b 0).val i = _
  rw [normSixVector_apply,oddMinimumVector_zero_apply]
  by_cases ha : i = a
  · subst i; simp [minimumPairPlus,coordinateVector,hab]
  by_cases hb : i = b
  · subst i; simp [minimumPairPlus,coordinateVector,hab.symm]
  simp [minimumPairPlus,coordinateVector,ha,hb]

theorem mathieu23_fixes_triangle (a : Omega) (g : Mathieu23PointModel a) :
    (mathieu23ToNormSixStabilizer a g).val.val (oddMinimumVector a 0) = oddMinimumVector a 0 := by
  apply Subtype.ext
  change integerPermutation g.val.val (oddMinimumVector a 0).val = _
  rw [oddMinimumVector_zero,permutation_odd_singleton]
  exact congrArg (fun i => oddProfileBase {i} ∅) g.prop

end Atlas.Conway
