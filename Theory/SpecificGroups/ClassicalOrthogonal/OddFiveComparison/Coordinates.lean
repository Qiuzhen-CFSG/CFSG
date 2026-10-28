/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
See also LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorAction
public import Theory.SpecificGroups.PSp4Three.MatrixModel

/-!
# The five-dimensional contraction kernel

The six exterior coordinates and Pfaffian are the existing CFSG definitions.
The kernel of symplectic contraction is isometric, with multiplier exactly one,
to the literal form `formB 2 F`. This fixes the orthogonal carrier and coordinate
conventions used in the odd B₂/C₂ comparison (GLS3 §2.7).

Adapted from `Atlas/LinearGroups/Orthogonal/B2ExteriorCoordinates.lean`:
reuse CFSG's forms, bivectors, and matrix symplectic API; add module boundaries.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.OddFiveComparison
open Atlas.Order20160A8.Bivectors
variable {F : Type*} [CommRing F]

/-- Symplectic contraction for the basis e₀,e₁,f₀,f₁. -/
def contraction : Six F →ₗ[F] F where
  toFun w := w 1 + w 4
  map_add' _ _ := by simp only [Pi.add_apply]; ring
  map_smul' _ _ := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem contraction_apply (w : Six F) : contraction w = w 1 + w 4 := rfl

/-- The actual ordered coordinates of the previously constructed symplectic module. -/
def symplecticCoordinates (v : Matrix.PSp4Three.Vector 2 F) : Four F :=
  ![v (.inl 0), v (.inl 1), v (.inr 0), v (.inr 1)]

theorem contraction_wedge (u v : Matrix.PSp4Three.Vector 2 F) :
    contraction (wedge (symplecticCoordinates u) (symplecticCoordinates v)) =
      Matrix.PSp4Three.form u v := by
  simp [wedge, symplecticCoordinates, Matrix.PSp4Three.form_apply, Fin.sum_univ_two]
  ring

theorem pfaffian_wedge (u v : Four F) : pfaffian (wedge u v) = 0 := by
  simp [wedge]
  ring

/-- Explicit coordinates on the contraction kernel, retaining the existing B₂ carrier. -/
def fromB : VectorB 2 F →ₗ[F] Six F where
  toFun v := ![v.1 (.inl 0), v.2, v.1 (.inl 1), v.1 (.inr 1), -v.2,
    v.1 (.inr 0)]
  map_add' u v := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' c v := by ext i; fin_cases i <;> simp

@[simp] theorem fromB_contraction (v : VectorB 2 F) : contraction (fromB v) = 0 := by
  simp [fromB]

/-- The multiplier is exactly one for these coordinate and Pfaffian conventions. -/
theorem fromB_pfaffian (v : VectorB 2 F) : pfaffian (fromB v) = formB 2 F v := by
  simp [fromB, formD_apply, Fin.sum_univ_two]
  ring

/-- All contraction-zero bivectors, with no odd-characteristic hypothesis. -/
def kernelEquiv : VectorB 2 F ≃ₗ[F] LinearMap.ker (contraction (F := F)) where
  toFun v := ⟨fromB v, fromB_contraction v⟩
  invFun w := ⟨Sum.elim ![w.val 0, w.val 2] ![w.val 5, w.val 3], w.val 1⟩
  left_inv v := by
    apply Prod.ext
    · funext i
      rcases i with i | i <;> fin_cases i <;> rfl
    · rfl
  right_inv w := by
    apply Subtype.ext
    funext i
    have hw : w.val 1 + w.val 4 = 0 := w.prop
    fin_cases i
    all_goals first | rfl | exact (eq_neg_of_add_eq_zero_right hw).symm
  map_add' u v := Subtype.ext (fromB.map_add u v)
  map_smul' c v := Subtype.ext (fromB.map_smul c v)

/-- The restriction itself, as an isometry, rather than merely an equality of orders. -/
def kernelIsometry : (formB 2 F).IsometryEquiv
    (pfaffian.comp (LinearMap.ker contraction).subtype) where
  toLinearEquiv := kernelEquiv
  map_app' := fromB_pfaffian

end ClassicalOrthogonal.OddFiveComparison
