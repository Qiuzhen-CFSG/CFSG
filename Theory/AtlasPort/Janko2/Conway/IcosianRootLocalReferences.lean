/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootLocalReferences.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointShapes
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionDiagonalData

/-!
# IcosianRootLocalReferences

Explicit lattice roots represent shapes C and D. Coordinate, norm, and reduction
identities certify their memberships and shape labels.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootLocalReferences.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes
open scoped Matrix Quaternion QuadraticAlgebra

/-- A scalar norm-two icosian making the mixed root `(q,1,1)` integral. -/
def icosianLocalCScalarCoordinates : IcosianIntegerCoordinates := ![1,0,1,0,-1,0,-1,2]

def icosianLocalCScalar : icosianOrder :=
  icosianIntegralSynthesis (icosianParityIntegralCoefficients icosianLocalCScalarCoordinates)

theorem icosianLocalCScalar_norm : icosianNorm icosianLocalCScalar.val=2 := by
  decide +kernel

theorem icosianLocalCScalar_reduction : icosianModuloTwo icosianLocalCScalar=!![0,0;0,1] := by
  rw [icosianLocalCScalar,icosianModuloTwo_synthesis]
  decide +kernel

def icosianLocalCVector : IcosianCoordinates := ![icosianLocalCScalar,1,1]

theorem icosianLocalCVector_mem : icosianLocalCVector∈icosianLeechModule := by
  rw [icosianLeechModule_matrix_glue,icosianMatrixGlue_constraints]
  intro j
  fin_cases j <;> simp [icosianLocalCVector,icosianLocalCScalar_reduction]
  apply QuadraticAlgebra.ext <;> decide +kernel

theorem icosianLocalCVector_norm :
    icosianHermitian (icosianCoordinateEmbedding icosianLocalCVector)
      (icosianCoordinateEmbedding icosianLocalCVector)=2 := by
  apply QuaternionAlgebra.ext <;> decide +kernel

def icosianLocalCRoot : IcosianRoot :=
  ⟨icosianLocalCVector,icosianLocalCVector_mem,icosianLocalCVector_norm⟩

theorem icosianLocalCRoot_shape : HasIcosianRootShape icosianLocalCRoot 2 := by
  apply (icosianRootShape_c _).mpr
  apply icosianRootC_recognition _ 0
  intro j
  apply icosianRootNormWord_of_norm
  fin_cases j
  · change icosianNorm icosianLocalCScalar.val=goldenIntegerToRational 2
    simpa only [map_ofNat] using icosianLocalCScalar_norm
  · change icosianNorm (1 : IcosianQuaternion)=goldenIntegerToRational 1
    rw [map_one]
    exact icosianNormOneGroup_norm 1
  · change icosianNorm (1 : IcosianQuaternion)=goldenIntegerToRational 1
    rw [map_one]
    exact icosianNormOneGroup_norm 1

/-- The already verified first reflection root is a reference for the three
pairwise distinct golden coordinate norms. -/
def icosianLocalDRoot : IcosianRoot :=
  ⟨icosianReflectionDiagonalIntegral 0,icosianReflectionDiagonalIntegral_mem 0,by
    have he : icosianCoordinateEmbedding (icosianReflectionDiagonalIntegral 0)=
        icosianReflectionDiagonalRoot 0 := funext (icosianReflectionDiagonalIntegral_coordinates 0)
    rw [he]
    exact icosianReflectionDiagonalRoot_norm 0⟩

theorem icosianLocalDRoot_norm_word :
    icosianRootNormWord icosianLocalDRoot=![((1-ω)^2 : GoldenInteger),ω^2,1] := by
  funext i
  apply icosianRootNormWord_of_norm
  change icosianNorm ((icosianReflectionDiagonalIntegral 0 i).val)=_
  rw [icosianReflectionDiagonalIntegral_coordinates]
  fin_cases i <;> decide +kernel

theorem icosianLocalDRoot_shape : HasIcosianRootShape icosianLocalDRoot 3 := by
  change List.Perm _ [1,(ω : GoldenInteger)^2,(1-ω)^2]
  rw [icosianLocalDRoot_norm_word]
  exact Atlas.triple_perm_reindex (Equiv.swap 0 2) icosianRootDNorms

end Atlas.Conway
