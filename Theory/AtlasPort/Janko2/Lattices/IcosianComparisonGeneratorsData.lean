/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianComparisonGeneratorsData.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonMatrix
public import Theory.AtlasPort.Janko2.Lattices.IcosianCongruence
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechGeneratorCriterion

/-!
# Icosian Comparison Generators Data

Explicit integral generator and preimage tables for the comparison with
the Golay Leech lattice. Integral icosian synthesis turns the tables into
vectors, while the target generators use the retained Golay marking.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianComparisonGeneratorsData.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix

def icosianComparisonSourceData : Matrix (Fin 36) (Fin 24) ℤ :=
![![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2],
![1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0],
![0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0],
![1,1,1,0,1,0,1,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0],
![1,1,0,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
![1,0,1,1,1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
![1,1,1,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0],
![1,0,1,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0],
![1,1,1,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0],
![1,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1]]

def icosianComparisonPreimageData : Matrix (Fin 38) (Fin 24) ℤ :=
![![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![-2,2,0,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![-2,0,0,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![-2,0,-2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,-4,2,2,-2,2,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![2,-2,0,0,-2,2,2,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![-1,0,-1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
![-1,0,-1,0,0,0,0,0,3,-2,1,0,-2,2,2,-2,0,0,0,0,0,0,0,0],
![-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0,0,-2,0],
![-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,-1,2,2,0,0,0],
![-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,2,1,0,0,0,-2,0],
![-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,-2,0,0,0],
![-1,0,-1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],
![-1,0,-1,0,0,0,0,0,1,0,-3,2,2,-2,2,-2,0,0,0,0,0,0,0,0],
![-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-3,2,2,-2,2,-2],
![-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0],
![-1,0,-1,0,0,0,0,0,-1,2,1,0,0,0,-2,0,0,0,0,0,0,0,0,0],
![-1,0,-1,0,0,0,0,0,1,0,1,0,-2,0,0,0,0,0,0,0,0,0,0,0],
![-1,0,-1,0,0,0,0,0,-1,0,1,0,0,0,-2,0,0,0,0,0,0,0,0,0],
![-1,0,-1,0,0,0,0,0,-1,0,-1,2,2,0,0,0,0,0,0,0,0,0,0,0],
![-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,3,-2,1,0,-2,2,2,-2],
![-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0],
![2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![2,-1,1,0,-2,1,0,-1,0,1,1,0,-1,0,-1,0,-1,0,0,1,1,0,-1,0],
![-1,1,1,0,0,0,-2,0,2,0,0,1,-1,0,1,-2,0,0,0,1,0,0,0,0],
![-1,1,1,0,0,0,-2,0,0,0,0,1,0,0,0,0,0,0,0,1,1,0,-1,0],
![1,0,0,1,0,0,0,-2,1,0,-2,1,1,-1,1,-1,-1,0,0,1,1,0,-1,0],
![1,0,0,1,0,0,0,-2,0,1,1,0,-1,0,-1,0,2,-1,1,0,-1,1,1,-1],
![0,0,0,0,0,0,-1,0,1,0,1,0,-1,1,0,-1,2,-1,0,1,0,1,1,-1],
![2,0,0,2,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,1,1,0,0,0,-2,0,2,-1,1,0,-1,1,1,-1,-1,0,0,1,1,0,-1,0],
![0,1,1,0,0,0,-2,0,1,0,-2,1,1,-1,1,-1,0,1,1,0,-1,0,-1,0],
![0,1,1,0,0,0,-2,0,0,1,1,0,-1,0,-1,0,1,0,-2,1,1,-1,1,-1],
![0,1,1,0,0,0,-2,0,-1,0,0,1,1,0,-1,0,2,-1,1,0,-1,1,1,-1],
![0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,2,0,0,1,0,0,1,-2],
![0,0,-1,1,0,0,0,-1,1,0,0,1,0,0,0,-1,1,0,0,1,0,0,0,-1]]

def icosianComparisonSourceCoefficients (n : Fin 36) (i : Fin 3) (j : Fin 4) : GoldenInteger :=
  ⟨icosianComparisonSourceData n (icosianRealCoordinateIndex (i,j,0)),
    icosianComparisonSourceData n (icosianRealCoordinateIndex (i,j,1))⟩

def icosianComparisonPreimageCoefficients (n : Fin 38) (i : Fin 3) (j : Fin 4) : GoldenInteger :=
  ⟨icosianComparisonPreimageData n (icosianRealCoordinateIndex (i,j,0)),
    icosianComparisonPreimageData n (icosianRealCoordinateIndex (i,j,1))⟩

noncomputable def icosianComparisonSourceGenerator (n : Fin 36) : IcosianCoordinates :=
  fun i => icosianIntegralSynthesis (icosianComparisonSourceCoefficients n i)

noncomputable def icosianComparisonPreimage (n : Fin 38) : IcosianCoordinates :=
  fun i => icosianIntegralSynthesis (icosianComparisonPreimageCoefficients n i)

def icosianOldPoint (j : Fin 24) : Omega :=
  ((⟨j.val/8, by omega⟩, ⟨(j.val/4)%2, by omega⟩), ⟨j.val%4, by omega⟩)

def icosianComparisonTargetGenerator (j : Fin 38) : IntegerCoordinates :=
  if h24 : j.val < 24 then
    coordinateVector (icosianOldPoint ⟨j.val,h24⟩) 4 - coordinateVector ((0,0),0) 4
  else if h25 : j.val = 24 then coordinateVector ((0,0),0) 8
  else if h37 : j.val < 37 then
    (2 : ℤ) • golayIntegerLift (golayGenerators ⟨j.val-25, by omega⟩)
  else oddGlue ((0,0),0)

end Atlas.Lattices
