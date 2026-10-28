/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianComparisonMatrix.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRationalSpace

/-!
# Icosian Comparison Matrix

A signed pair-Hadamard transform in the marked 24 rational coordinates.
Kernel-checked matrix identities give its inverse and Gram matrix,
providing the explicit rational isometry used by the lattice comparison.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianComparisonMatrix.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace Atlas.Lattices
open Atlas.Codes
open scoped Matrix

/-- A signed pair-Hadamard transform with the retained Golay coordinate marking. -/
def icosianComparisonData : Matrix (Fin 24) (Fin 24) ℚ :=
![![2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,-2,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,2,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,0,0,2,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,-2],
![0,0,0,0,0,0,0,0,2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,2,0,-2,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,-2,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,-2,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,-2,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,-2,0,0,0,2,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0]]

def icosianLeechCoordinateIndex (p : Omega) : Fin 24 :=
  ⟨8*p.1.1.val+4*p.1.2.val+p.2.val, by
    have := p.1.1.isLt; have := p.1.2.isLt; have := p.2.isLt; omega⟩

def icosianRealCoordinateIndex (p : IcosianRealIndex) : Fin 24 :=
  ⟨8*p.1.val+2*p.2.1.val+p.2.2.val, by
    have := p.1.isLt; have := p.2.1.isLt; have := p.2.2.isLt; omega⟩

def icosianComparisonMatrix : Matrix Omega IcosianRealIndex ℚ := fun p q =>
  icosianComparisonData (icosianLeechCoordinateIndex p) (icosianRealCoordinateIndex q)

def icosianComparisonInverseMatrix : Matrix IcosianRealIndex Omega ℚ :=
  (1/8 : ℚ) • icosianComparisonMatrix.transpose

theorem icosianComparison_matrix_inverse :
    icosianComparisonMatrix * icosianComparisonInverseMatrix = 1 := by
  decide +kernel

theorem icosianComparison_inverse_matrix :
    icosianComparisonInverseMatrix * icosianComparisonMatrix = 1 := by
  decide +kernel

theorem icosianComparison_matrix_gram :
    icosianComparisonMatrix.transpose * icosianComparisonMatrix = (8 : ℚ) • 1 := by
  decide +kernel

end Atlas.Lattices
