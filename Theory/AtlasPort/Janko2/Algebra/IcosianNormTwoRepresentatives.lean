/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormTwoRepresentatives.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormTwoAssociates
public import Theory.AtlasPort.Janko2.Algebra.IcosianParityIntegral
public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoCoordinates
public import Theory.AtlasPort.Janko2.Algebra.GoldenFourFinite

/-!
# IcosianNormTwoRepresentatives

Five explicit norm-two icosians represent the five possible reduction
image lines. Their norms and reductions are calculated in coordinates;
finite matrix checks prove coverage and separation.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormTwoRepresentatives.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix QuadraticAlgebra Quaternion BigOperators

def icosianNormTwoRepresentativeCoordinates : Fin 5 → IcosianIntegerCoordinates :=
  ![![-2,0,-2,0,0,0,0,0],![-2,0,-1,0,1,-1,0,-1],![-2,0,-1,0,1,-1,0,1],
    ![-2,0,-1,0,-1,1,0,-1],![-2,0,-1,0,-1,1,0,1]]

def icosianNormTwoRepresentative (i : Fin 5) : icosianOrder :=
  icosianIntegralSynthesis (icosianParityIntegralCoefficients (icosianNormTwoRepresentativeCoordinates i))

def icosianNormTwoRepresentativeMatrix (i : Fin 5) : IcosianMatrix :=
  icosianMatrixFromCoefficients (fun j => goldenModuloTwo
    (icosianParityIntegralCoefficients (icosianNormTwoRepresentativeCoordinates i) j))

theorem icosianNormTwoRepresentative_reduction (i : Fin 5) :
    icosianModuloTwo (icosianNormTwoRepresentative i)=icosianNormTwoRepresentativeMatrix i :=
  icosianModuloTwo_synthesis _

theorem icosianNormTwoRepresentative_norm (i : Fin 5) :
    icosianNorm (icosianNormTwoRepresentative i).val=2 := by
  fin_cases i <;> decide +kernel

/-- The five reduction image lines exhaust singular two-by-two matrices.
This is a scalar F4 calculation, not an enumeration of lattice roots. -/
theorem icosianNormTwoRepresentative_cover :
    ∀ m : IcosianMatrix, Matrix.det m=0 →
      ∃ i : Fin 5,Matrix.adjugate (icosianNormTwoRepresentativeMatrix i)*m=0 := by
  decide +kernel

theorem icosianNormTwoRepresentative_separate :
    ∀ i j : Fin 5,i≠j →
      Matrix.adjugate (icosianNormTwoRepresentativeMatrix i)*icosianNormTwoRepresentativeMatrix j≠0 := by
  decide +kernel

end Atlas.Algebra
