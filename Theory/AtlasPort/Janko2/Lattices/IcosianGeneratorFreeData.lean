/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianGeneratorFreeData.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonSourceMembership
public import Theory.AtlasPort.Janko2.Lattices.IcosianGlueFreeCoordinates

/-!
# Icosian Generator Free Data

The twelve glue-generator rows realize the binary information positions
of the six-dimensional matrix glue. Finite coordinate checks establish
their information matrix and their membership in the glue.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianGeneratorFreeData.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix QuadraticAlgebra BigOperators

/-- The twelve binary information positions, grouped into six F4 coefficients. -/
def icosianGlueFreePosition : Fin 12 → Fin 24 := ![10,11,14,15,16,17,18,19,20,21,22,23]

def icosianGlueRowIndex (k : Fin 12) : Fin 36 := ⟨24+k.val,by omega⟩

theorem icosianGlueRows_free : ∀ k l : Fin 12,
    icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition l) =
      if k=l then 1 else 0 := by
  decide +kernel

theorem icosianGlueRows_mem : ∀ k : Fin 12,
    (fun i => icosianMatrixFromCoefficients
      (fun j => goldenModuloTwo (icosianComparisonSourceCoefficients (icosianGlueRowIndex k) i j)))
      ∈ icosianMatrixGlue GoldenFour := by
  intro k
  have h := (icosianLeechModule_matrix_glue _).mp
    (icosianComparisonSourceGenerator_mem (icosianGlueRowIndex k))
  simpa only [icosianComparisonSourceGenerator,icosianModuloTwo_synthesis] using h

end Atlas.Lattices
