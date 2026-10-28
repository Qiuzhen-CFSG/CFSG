/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianCoordinateNorm.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianUnitCandidates

/-!
# IcosianCoordinateNorm

Half-integral quaternion coordinates express the reduced norm through
two integer quadratic forms. The formula verifies norm one for every
member of the finite norm-one coordinate list.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianCoordinateNorm.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra BigOperators

def icosianCoordinatesQuaternion (v : IcosianIntegerCoordinates) : IcosianQuaternion :=
  ⟨⟨(v 0 : ℚ)/2,(v 1 : ℚ)/2⟩,⟨(v 2 : ℚ)/2,(v 3 : ℚ)/2⟩,
    ⟨(v 4 : ℚ)/2,(v 5 : ℚ)/2⟩,⟨(v 6 : ℚ)/2,(v 7 : ℚ)/2⟩⟩

theorem icosianCoordinatesQuaternion_norm (v : IcosianIntegerCoordinates) :
    icosianNorm (icosianCoordinatesQuaternion v)=
      ⟨(icosianCoordinateNorm v : ℚ)/4,(icosianCoordinateTau v : ℚ)/4⟩ := by
  rw [icosianNorm_coordinates]
  ext <;> simp [icosianCoordinatesQuaternion,
    icosianCoordinateNorm,icosianCoordinateTau,Fin.sum_univ_succ,pow_two] <;> ring

theorem icosianNormOneCoordinates_norm {v : IcosianIntegerCoordinates}
    (hv : v ∈ icosianNormOneCoordinates) :
    icosianNorm (icosianCoordinatesQuaternion v)=1 := by
  obtain ⟨hshort,htau⟩ := Finset.mem_filter.mp hv
  rw [icosianCoordinatesQuaternion_norm,icosianShortCoordinates_norm v hshort,htau]
  ext <;> norm_num

end Atlas.Algebra
