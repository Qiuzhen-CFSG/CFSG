module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.Bivectors

/-!
Adapted from `Atlas/LinearGroups/Orthogonal/B2ExteriorAction.lean`.
The compound matrix acts on genuine two-by-two minors. Naturality proves
composition, and a polynomial identity gives Pfaffian preservation for SL₄.
-/

@[expose] public noncomputable section
namespace Atlas.Order20160A8.Bivectors
open Matrix
variable {F : Type*} [CommRing F]

/-- First endpoint of each coordinate pair. -/
def first : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
/-- Second endpoint of each coordinate pair. -/
def second : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- The second compound matrix, consisting of the genuine two-by-two minors. -/
def compound (A : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 6) (Fin 6) F :=
  fun i j => A (first i) (first j) * A (second i) (second j) -
    A (first i) (second j) * A (second i) (first j)

/-- The six-coordinate linear action, defined for arbitrary endomorphisms. -/
def exteriorMap (A : Matrix (Fin 4) (Fin 4) F) : Six F →ₗ[F] Six F :=
  (compound A).toLin'

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1800000 in
-- Expanding all six minors gives a moderate polynomial identity.
/-- Its defining naturality on every decomposable bivector. -/
theorem exteriorMap_wedge (A : Matrix (Fin 4) (Fin 4) F) (u v : Four F) :
    exteriorMap A (wedge u v) = wedge (A *ᵥ u) (A *ᵥ v) := by
  ext i
  fin_cases i <;>
    simp [exteriorMap, compound, first, second, wedge, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Each standard exterior coordinate is a decomposable bivector. -/
theorem wedge_basis (i : Fin 6) :
    wedge (Pi.single (first i) (1 : F)) (Pi.single (second i) 1) = Pi.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [wedge, first, second]

/-- The wedge coordinates span the full six-dimensional space. -/
theorem exterior_ext {W : Type*} [AddCommGroup W] [Module F W] {L M : Six F →ₗ[F] W}
    (h : ∀ u v : Four F, L (wedge u v) = M (wedge u v)) : L = M := by
  apply (Pi.basisFun F (Fin 6)).ext
  intro i
  simpa only [Pi.basisFun_apply, ← wedge_basis i] using
    h (Pi.single (first i) 1) (Pi.single (second i) 1)

/-- Functoriality comes from the natural action on pairs, not from an assumed representation. -/
theorem exteriorMap_mul (A B : Matrix (Fin 4) (Fin 4) F) :
    exteriorMap (A * B) = (exteriorMap A).comp (exteriorMap B) := by
  apply exterior_ext
  intro u v
  simp only [LinearMap.comp_apply, exteriorMap_wedge, Matrix.mulVec_mulVec]

@[simp] theorem exteriorMap_one : exteriorMap (1 : Matrix (Fin 4) (Fin 4) F) = LinearMap.id := by
  apply exterior_ext
  intro u v
  simp [exteriorMap_wedge]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1800000 in
-- The quartic Pfaffian identity is verified by ring normalization of the actual minors.
/-- The quadratic form scales by the determinant of the original four-dimensional map. -/
theorem pfaffian_exteriorMap (A : Matrix (Fin 4) (Fin 4) F) (w : Six F) :
    pfaffian (exteriorMap A w) = A.det * pfaffian w := by
  rw [Matrix.det_succ_row_zero]
  simp [pfaffian_apply, exteriorMap, compound, first, second, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.succAbove]
  ring

end Atlas.Order20160A8.Bivectors
