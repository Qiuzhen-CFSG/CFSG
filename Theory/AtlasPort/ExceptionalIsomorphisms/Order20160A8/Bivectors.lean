module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.Basic

/-!
Adapted from `Atlas/LinearGroups/Orthogonal/B2ExteriorCoordinates.lean`.
Only the six bivector coordinates and their Pfaffian form are retained.
The coordinates are 01, 02, 03, 12, 13, 23.
-/

@[expose] public noncomputable section
namespace Atlas.Order20160A8.Bivectors

variable {F : Type*} [CommRing F]

abbrev Four (F : Type*) := Fin 4 → F
abbrev Six (F : Type*) := Fin 6 → F

/-- The six two-by-two minors of the ordered pair of vectors. -/
def wedge (u v : Four F) : Six F :=
  ![u 0 * v 1 - u 1 * v 0, u 0 * v 2 - u 2 * v 0,
    u 0 * v 3 - u 3 * v 0, u 1 * v 2 - u 2 * v 1,
    u 1 * v 3 - u 3 * v 1, u 2 * v 3 - u 3 * v 2]

/-- The quadratic Pfaffian, not the determinant (its square). -/
def pfaffian : QuadraticForm F (Six F) :=
  QuadraticMap.proj (R := F) 0 5 - QuadraticMap.proj (R := F) 1 4 +
    QuadraticMap.proj (R := F) 2 3

@[simp] theorem pfaffian_apply (w : Six F) :
    pfaffian w = w 0 * w 5 - w 1 * w 4 + w 2 * w 3 := by
  simp [pfaffian, QuadraticMap.proj, QuadraticMap.linMulLin_apply]

end Atlas.Order20160A8.Bivectors
