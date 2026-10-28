/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionDiagonalData.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionIsometries
public import Theory.AtlasPort.Janko2.Lattices.IcosianGlueFreeCoordinates
public import Theory.AtlasPort.Janko2.Algebra.IcosianParityIntegral

/-!
# IcosianReflectionDiagonalData

Explicit integral roots and norm-one units supply the diagonal reflection word.
Finite coordinate and reduction checks certify the table entries.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionDiagonalData.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes
open scoped Matrix Quaternion QuadraticAlgebra

/-- Three explicit roots used in the four-reflection diagonal identity.
Entries are twice the coefficients on 1,tau,i,tau*i,j,tau*j,k,tau*k.
No ambient root enumeration is used. -/
def icosianReflectionDiagonalRootData : Fin 3 → Fin 3 → IcosianIntegerCoordinates :=
  ![![![2,-2,0,0,0,0,0,0],![0,-1,0,-1,0,-1,0,1],![1,0,-1,0,-1,0,1,0]],
    ![![-2,0,-2,0,0,0,0,0],![0,0,0,0,0,0,0,0],![0,0,0,0,-2,0,2,0]],
    ![![-2,0,-2,0,0,0,0,0],![-2,0,2,0,0,0,0,0],![0,0,0,0,0,0,0,0]]]

attribute [local irreducible] icosianReflectionDiagonalRootData

def icosianReflectionDiagonalIntegral (k : Fin 3) : IcosianCoordinates :=
  fun i => icosianIntegralSynthesis
    (icosianParityIntegralCoefficients (icosianReflectionDiagonalRootData k i))

def icosianReflectionDiagonalRoot (k : Fin 3) : IcosianRationalCoordinates :=
  fun i => icosianCoordinatesQuaternion (icosianReflectionDiagonalRootData k i)

theorem icosianReflectionDiagonalRoot_coordinates (k i : Fin 3) :
    icosianReflectionDiagonalRoot k i =
      icosianCoordinatesQuaternion (icosianReflectionDiagonalRootData k i) := rfl

theorem icosianReflectionDiagonalIntegral_coordinates :
    ∀ k i, (icosianReflectionDiagonalIntegral k i).val =
      icosianReflectionDiagonalRoot k i := by
  intro k i
  fin_cases k <;> fin_cases i <;> apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianReflectionDiagonalRoot_norm :
    ∀ k, icosianHermitian (icosianReflectionDiagonalRoot k)
      (icosianReflectionDiagonalRoot k) = 2 := by
  intro k
  fin_cases k <;> apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianReflectionDiagonalIntegral_mem (k : Fin 3) :
    icosianReflectionDiagonalIntegral k ∈ icosianLeechModule := by
  rw [icosianLeechModule_matrix_glue,icosianMatrixGlue_constraints]
  simp only [icosianReflectionDiagonalIntegral,icosianModuloTwo_synthesis]
  unfold icosianReflectionDiagonalRootData
  fin_cases k <;> intro j <;> fin_cases j <;> refine ⟨?_,?_,?_⟩ <;>
    apply QuadraticAlgebra.ext <;> decide +kernel

theorem icosianReflectionDiagonalRoot_mem (k : Fin 3) :
    icosianReflectionDiagonalRoot k ∈ rationalIcosianLattice :=
  ⟨icosianReflectionDiagonalIntegral k,icosianReflectionDiagonalIntegral_mem k,
    funext (icosianReflectionDiagonalIntegral_coordinates k)⟩

def icosianReflectionDiagonalGenerator (k : Fin 3) : icosianHermitianGroup :=
  icosianRootReflection (icosianReflectionDiagonalRoot k)
    (icosianReflectionDiagonalRoot_norm k) (icosianReflectionDiagonalRoot_mem k)

/-- Listed in output-coordinate order. -/
def icosianReflectionDiagonalUnitData : Fin 3 → IcosianIntegerCoordinates :=
  ![![1,0,1,0,-1,0,-1,0],![1,0,-1,0,1,0,-1,0],![1,0,1,0,1,0,1,0]]

def icosianReflectionDiagonalUnitIntegral (i : Fin 3) : icosianOrder :=
  icosianIntegralSynthesis (icosianParityIntegralCoefficients
    (icosianReflectionDiagonalUnitData i))

theorem icosianReflectionDiagonalUnit_norm :
    ∀ i, icosianNorm (icosianReflectionDiagonalUnitIntegral i).val = 1 := by
  decide +kernel

def icosianReflectionDiagonalUnit (i : Fin 3) : icosianNormOneGroup :=
  icosianNormOneGroupOf (icosianReflectionDiagonalUnitIntegral i).val
    (icosianReflectionDiagonalUnitIntegral i).property (icosianReflectionDiagonalUnit_norm i)

theorem icosianReflectionDiagonalUnit_reduction :
    ∀ i, icosianModuloTwo (icosianReflectionDiagonalUnitIntegral i) =
      !![goldenFourTau, (![goldenFourTau+1,1,goldenFourTau] i);0,goldenFourTau+1] := by
  simp only [icosianReflectionDiagonalUnitIntegral,icosianModuloTwo_synthesis]
  decide +kernel

end Atlas.Conway
