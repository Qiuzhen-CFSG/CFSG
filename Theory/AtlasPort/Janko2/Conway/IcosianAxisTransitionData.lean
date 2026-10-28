/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisTransitionData.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionIsometries
public import Theory.AtlasPort.Janko2.Lattices.IcosianGlueFreeCoordinates
public import Theory.AtlasPort.Janko2.Algebra.IcosianParityIntegral

/-!
# IcosianAxisTransitionData

Explicit integral norm-two roots define the axis-transition reflections. Finite
coordinate calculations certify lattice membership and Hermitian norm.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisTransitionData.lean`, revision
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

/-- Four local roots: one (2,1,1) root and three roots orthogonal to axis zero.
Only these displayed coordinates enter the local transition proofs. -/
def icosianAxisTransitionRootData : Fin 4 → Fin 3 → IcosianIntegerCoordinates :=
  ![![![-2,0,-1,0,-1,1,0,1],![0,0,1,0,-1,1,0,1],![0,0,1,0,-1,1,0,1]],![![0,0,0,0,0,0,0,0],![-2,0,-2,0,0,0,0,0],![-2,0,2,0,0,0,0,0]],![![0,0,0,0,0,0,0,0],![-2,0,-2,0,0,0,0,0],![0,0,0,0,-2,0,-2,0]],![![0,0,0,0,0,0,0,0],![-2,0,-2,0,0,0,0,0],![0,0,0,0,-2,0,2,0]]]

attribute [local irreducible] icosianAxisTransitionRootData

def icosianAxisTransitionIntegral (k : Fin 4) : IcosianCoordinates :=
  fun i => icosianIntegralSynthesis
    (icosianParityIntegralCoefficients (icosianAxisTransitionRootData k i))

def icosianAxisTransitionRoot (k : Fin 4) : IcosianRationalCoordinates :=
  fun i => icosianCoordinatesQuaternion (icosianAxisTransitionRootData k i)

theorem icosianAxisTransitionRoot_coordinates (k : Fin 4) (i : Fin 3) :
    icosianAxisTransitionRoot k i =
      icosianCoordinatesQuaternion (icosianAxisTransitionRootData k i) := rfl

theorem icosianAxisTransitionIntegral_coordinates :
    ∀ k i, (icosianAxisTransitionIntegral k i).val =
      icosianAxisTransitionRoot k i := by
  intro k i
  fin_cases k <;> fin_cases i <;> apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianAxisTransitionRoot_norm :
    ∀ k, icosianHermitian (icosianAxisTransitionRoot k)
      (icosianAxisTransitionRoot k) = 2 := by
  intro k
  fin_cases k <;> apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianAxisTransitionIntegral_mem (k : Fin 4) :
    icosianAxisTransitionIntegral k ∈ icosianLeechModule := by
  rw [icosianLeechModule_matrix_glue,icosianMatrixGlue_constraints]
  simp only [icosianAxisTransitionIntegral,icosianModuloTwo_synthesis]
  unfold icosianAxisTransitionRootData
  fin_cases k <;> intro j <;> fin_cases j <;> refine ⟨?_,?_,?_⟩ <;>
    apply QuadraticAlgebra.ext <;> decide +kernel

theorem icosianAxisTransitionRoot_mem (k : Fin 4) :
    icosianAxisTransitionRoot k ∈ rationalIcosianLattice :=
  ⟨icosianAxisTransitionIntegral k,icosianAxisTransitionIntegral_mem k,
    funext (icosianAxisTransitionIntegral_coordinates k)⟩

def icosianAxisTransitionGenerator (k : Fin 4) : icosianHermitianGroup :=
  icosianRootReflection (icosianAxisTransitionRoot k)
    (icosianAxisTransitionRoot_norm k) (icosianAxisTransitionRoot_mem k)

end Atlas.Conway
