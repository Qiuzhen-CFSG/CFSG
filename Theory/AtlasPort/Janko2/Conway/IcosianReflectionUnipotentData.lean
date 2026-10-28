/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionUnipotentData.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionDiagonalData

/-!
# IcosianReflectionUnipotentData

Explicit edge roots and norm-one units define the unipotent reflection words.
Lattice, norm, and reduction checks certify their finite tables.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionUnipotentData.lean`, revision
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

/-- The second block of the swap root and two unipotent roots. -/
def icosianReflectionEdgeSecond : Fin 3 → IcosianIntegerCoordinates :=
  ![![2,0,2,0,0,0,0,0],![-2,0,2,0,0,0,0,0],![0,0,0,0,-2,0,2,0]]

def icosianReflectionEdgePartner (p : Fin 2) : Fin 3 := ⟨p.val+1,by omega⟩

def icosianReflectionEdgeData (k : Fin 3) (p : Fin 2) (i : Fin 3) :
    IcosianIntegerCoordinates :=
  if i=0 then ![-2,0,-2,0,0,0,0,0]
  else if i=icosianReflectionEdgePartner p then icosianReflectionEdgeSecond k else 0

def icosianReflectionEdgeRoot (k : Fin 3) (p : Fin 2) : IcosianRationalCoordinates :=
  fun i => icosianCoordinatesQuaternion (icosianReflectionEdgeData k p i)

def icosianReflectionEdgeIntegral (k : Fin 3) (p : Fin 2) : IcosianCoordinates :=
  fun i => icosianIntegralSynthesis
    (icosianParityIntegralCoefficients (icosianReflectionEdgeData k p i))

theorem icosianReflectionEdgeIntegral_coordinates :
    ∀ k p i, (icosianReflectionEdgeIntegral k p i).val = icosianReflectionEdgeRoot k p i := by
  intro k p i
  fin_cases k <;> fin_cases p <;> fin_cases i <;>
    apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianReflectionEdgeRoot_norm :
    ∀ k p, icosianHermitian (icosianReflectionEdgeRoot k p)
      (icosianReflectionEdgeRoot k p) = 2 := by
  intro k p
  fin_cases k <;> fin_cases p <;> apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianReflectionEdgeIntegral_mem (k : Fin 3) (p : Fin 2) :
    icosianReflectionEdgeIntegral k p ∈ icosianLeechModule := by
  rw [icosianLeechModule_matrix_glue,icosianMatrixGlue_constraints]
  simp only [icosianReflectionEdgeIntegral,icosianModuloTwo_synthesis]
  fin_cases k <;> fin_cases p <;> intro j <;> fin_cases j <;>
    refine ⟨?_,?_,?_⟩ <;> apply QuadraticAlgebra.ext <;> decide +kernel

theorem icosianReflectionEdgeRoot_mem (k : Fin 3) (p : Fin 2) :
    icosianReflectionEdgeRoot k p ∈ rationalIcosianLattice :=
  ⟨icosianReflectionEdgeIntegral k p,icosianReflectionEdgeIntegral_mem k p,
    funext (icosianReflectionEdgeIntegral_coordinates k p)⟩

def icosianReflectionEdgeGenerator (k : Fin 3) (p : Fin 2) : icosianHermitianGroup :=
  icosianRootReflection (icosianReflectionEdgeRoot k p)
    (icosianReflectionEdgeRoot_norm k p) (icosianReflectionEdgeRoot_mem k p)

def icosianReflectionEdgeUnitData : Fin 3 → IcosianIntegerCoordinates :=
  ![![2,0,0,0,0,0,0,0],![0,0,-2,0,0,0,0,0],![0,0,0,0,2,0,0,0]]

def icosianReflectionEdgeUnitIntegral (k : Fin 3) : icosianOrder :=
  icosianIntegralSynthesis (icosianParityIntegralCoefficients (icosianReflectionEdgeUnitData k))

theorem icosianReflectionEdgeUnit_norm :
    ∀ k, icosianNorm (icosianReflectionEdgeUnitIntegral k).val = 1 := by decide +kernel

def icosianReflectionEdgeUnit (k : Fin 3) : icosianNormOneGroup :=
  icosianNormOneGroupOf (icosianReflectionEdgeUnitIntegral k).val
    (icosianReflectionEdgeUnitIntegral k).property (icosianReflectionEdgeUnit_norm k)

def icosianReflectionEdgeParameter : Fin 3 → GoldenFour := ![0,1,goldenFourTau+1]

theorem icosianReflectionEdgeUnit_reduction :
    ∀ k, icosianModuloTwo (icosianReflectionEdgeUnitIntegral k) =
      !![1,icosianReflectionEdgeParameter k;0,1] := by
  simp only [icosianReflectionEdgeUnitIntegral,icosianModuloTwo_synthesis]
  decide +kernel

end Atlas.Conway
