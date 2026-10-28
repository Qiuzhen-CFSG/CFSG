/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormTwoMatrixFibers.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormTwoCount

/-!
# IcosianNormTwoMatrixFibers

Each nonzero singular matrix over F₄ has four parameterizations by
a norm-two line representative and a special linear matrix. The finite
statement is verified by kernel reduction.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormTwoMatrixFibers.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

noncomputable section
namespace Atlas.Algebra
open scoped Matrix

abbrev IcosianSpecialLinear := Matrix.SpecialLinearGroup (Fin 2) GoldenFour

abbrev IcosianNormTwoMatrixParameters (m : IcosianMatrix) :=
  {p : Fin 5 × IcosianSpecialLinear //
    icosianNormTwoRepresentativeMatrix p.1 * (p.2 : IcosianMatrix) = m}

/-- Each nonzero singular scalar matrix has four lifted special-linear
coordinates among the five projective image-line representatives. -/
theorem icosianNormTwoMatrixParameters_count :
    ∀ m : IcosianMatrix, Matrix.det m = 0 → m ≠ 0 →
      Fintype.card (IcosianNormTwoMatrixParameters m) = 4 := by
  decide +kernel

end Atlas.Algebra
