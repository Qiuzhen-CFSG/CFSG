/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
See also LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison.Coordinates
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The actual Sp₄ action on the odd five-space

Restrict the existing exterior-square action to the contraction kernel and
transport across its explicit isometry with `formB 2 F`. The resulting
homomorphism targets CFSG's full quadratic isometry subgroup directly.

Adapted from ATLAS `LinearGroups/Orthogonal/B2ExteriorAction.lean` and
`B2ExteriorSymplectic.lean`: retain only contraction invariance and the
restriction, reuse CFSG exterior identities, and use its subgroup membership
API. Source: GLS3 §2.7, the odd B₂/C₂ comparison.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.OddFiveComparison
open Matrix Atlas.Order20160A8.Bivectors
variable {F : Type*} [CommRing F]

/-- Preservation of the symplectic pairing on vector pairs gives preservation of
contraction on every bivector, not only the decomposable ones. -/
theorem contraction_exteriorMap (A : Matrix (Fin 4) (Fin 4) F)
    (hA : ∀ u v : Four F, contraction (wedge (A *ᵥ u) (A *ᵥ v)) =
      contraction (wedge u v)) (w : Six F) :
    contraction (exteriorMap A w) = contraction w := by
  have h : contraction.comp (exteriorMap A) = contraction := by
    apply exterior_ext
    intro u v
    simpa only [LinearMap.comp_apply, exteriorMap_wedge] using hA u v
  exact LinearMap.congr_fun h w

/-- The actual symplectic matrix, with coordinates ordered e₀,e₁,f₀,f₁. -/
def symplecticMatrix (g : Matrix.PSp4Three.Sp 2 F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.reindexAlgEquiv F F finSumFinEquiv g.val

@[simp] theorem symplecticMatrix_one : symplecticMatrix (1 : Matrix.PSp4Three.Sp 2 F) = 1 :=
  map_one (Matrix.reindexAlgEquiv F F finSumFinEquiv)

@[simp] theorem symplecticMatrix_mul (g h : Matrix.PSp4Three.Sp 2 F) :
    symplecticMatrix (g * h) = symplecticMatrix g * symplecticMatrix h :=
  map_mul (Matrix.reindexAlgEquiv F F finSumFinEquiv) g.val h.val

theorem symplecticMatrix_det (g : Matrix.PSp4Three.Sp 2 F) : (symplecticMatrix g).det = 1 := by
  rw [symplecticMatrix, Matrix.det_reindexAlgEquiv]
  exact Matrix.PSp4Three.determinant_one g

omit [CommRing F] in
theorem symplecticCoordinates_eq (v : Matrix.PSp4Three.Vector 2 F) :
    symplecticCoordinates v = v ∘ (finSumFinEquiv : Matrix.PSp4Three.Index 2 ≃ Fin 4).symm := by
  ext i
  fin_cases i <;> rfl

omit [CommRing F] in
theorem symplecticCoordinates_surjective :
    Function.Surjective (symplecticCoordinates (F := F)) := by
  intro v
  refine ⟨v ∘ (finSumFinEquiv : Matrix.PSp4Three.Index 2 ≃ Fin 4), ?_⟩
  rw [symplecticCoordinates_eq]
  ext i
  simp

theorem symplecticMatrix_mulVec (g : Matrix.PSp4Three.Sp 2 F)
    (v : Matrix.PSp4Three.Vector 2 F) :
    symplecticMatrix g *ᵥ symplecticCoordinates v =
      symplecticCoordinates (g.val *ᵥ v) := by
  rw [symplecticCoordinates_eq, symplecticCoordinates_eq]
  change g.val.submatrix finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ
    (v ∘ finSumFinEquiv.symm) = _
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_def, Equiv.apply_symm_apply]

/-- Contraction is invariant on the entire exterior space for the actual Sp₄ action. -/
theorem symplectic_contraction (g : Matrix.PSp4Three.Sp 2 F) (w : Six F) :
    contraction (exteriorMap (symplecticMatrix g) w) = contraction w := by
  apply contraction_exteriorMap
  intro u v
  obtain ⟨u, rfl⟩ := symplecticCoordinates_surjective u
  obtain ⟨v, rfl⟩ := symplecticCoordinates_surjective v
  rw [symplecticMatrix_mulVec, symplecticMatrix_mulVec, contraction_wedge, contraction_wedge]
  exact Matrix.PSp4Three.preserves g u v

/-- Pfaffian invariance for the actual symplectic matrices. -/
theorem symplectic_pfaffian (g : Matrix.PSp4Three.Sp 2 F) (w : Six F) :
    pfaffian (exteriorMap (symplecticMatrix g) w) = pfaffian w := by
  rw [pfaffian_exteriorMap, symplecticMatrix_det, one_mul]

/-- The restricted linear action on contraction-zero bivectors. -/
def kernelMap (g : Matrix.PSp4Three.Sp 2 F) :
    LinearMap.ker (contraction (F := F)) →ₗ[F] LinearMap.ker (contraction (F := F)) where
  toFun w := ⟨exteriorMap (symplecticMatrix g) w.val, by
    change contraction (exteriorMap (symplecticMatrix g) w.val) = 0
    rw [symplectic_contraction]
    exact w.prop⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem kernelMap_mul (g h : Matrix.PSp4Three.Sp 2 F) :
    kernelMap (g * h) = (kernelMap g).comp (kernelMap h) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change exteriorMap (symplecticMatrix (g * h)) w.val =
    exteriorMap (symplecticMatrix g) (exteriorMap (symplecticMatrix h) w.val)
  rw [symplecticMatrix_mul, exteriorMap_mul, LinearMap.comp_apply]

@[simp] theorem kernelMap_one : kernelMap (1 : Matrix.PSp4Three.Sp 2 F) = LinearMap.id := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change exteriorMap (symplecticMatrix 1) w.val = w.val
  rw [symplecticMatrix_one, exteriorMap_one, LinearMap.id_apply]

/-- Restriction remains invertible, with inverse induced by the original inverse matrix. -/
def kernelAction (g : Matrix.PSp4Three.Sp 2 F) :
    LinearMap.ker (contraction (F := F)) ≃ₗ[F] LinearMap.ker (contraction (F := F)) where
  __ := kernelMap g
  invFun := kernelMap g⁻¹
  left_inv w := by
    change ((kernelMap g⁻¹).comp (kernelMap g)) w = w
    rw [← kernelMap_mul, inv_mul_cancel, kernelMap_one, LinearMap.id_apply]
  right_inv w := by
    change ((kernelMap g).comp (kernelMap g⁻¹)) w = w
    rw [← kernelMap_mul, mul_inv_cancel, kernelMap_one, LinearMap.id_apply]

/-- The induced linear automorphism of the already fixed B₂ carrier. -/
def onB (g : Matrix.PSp4Three.Sp 2 F) : VectorB 2 F ≃ₗ[F] VectorB 2 F :=
  kernelEquiv.trans ((kernelAction g).trans kernelEquiv.symm)

theorem onB_pfaffian (g : Matrix.PSp4Three.Sp 2 F) (v : VectorB 2 F) :
    formB 2 F (onB g v) = formB 2 F v := by
  rw [← fromB_pfaffian, ← fromB_pfaffian]
  have hv : fromB (onB g v) = exteriorMap (symplecticMatrix g) (fromB v) :=
    congrArg Subtype.val (kernelEquiv.apply_symm_apply (kernelAction g (kernelEquiv v)))
  rw [hv, symplectic_pfaffian]

end ClassicalOrthogonal.OddFiveComparison

@[expose] public noncomputable section
namespace ClassicalOrthogonal.OddFiveComparison
open Matrix Atlas.Order20160A8.Bivectors
variable {F : Type*} [Field F]

/-- The actual homomorphism Sp₄ → O(B₂), defined by exterior square and restriction. -/
def toOrthogonal : Matrix.PSp4Three.Sp 2 F →* Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB 2 F) where
  toFun g := ⟨onB g, (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    (onB_pfaffian g)⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change kernelEquiv.symm (kernelMap 1 (kernelEquiv v)) = v
    rw [kernelMap_one, LinearMap.id_apply, LinearEquiv.symm_apply_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change kernelEquiv.symm (kernelMap (g * h) (kernelEquiv v)) =
      kernelEquiv.symm (kernelMap g (kernelEquiv (kernelEquiv.symm (kernelMap h (kernelEquiv v)))))
    rw [LinearEquiv.apply_symm_apply, kernelMap_mul, LinearMap.comp_apply]

end ClassicalOrthogonal.OddFiveComparison
