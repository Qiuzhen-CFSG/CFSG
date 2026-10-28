/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
See also LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison.Action
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Theory.SpecificGroups.PSp4Three.Generation

/-!
# The exterior-square image is elementary

The transvection with direction e₀ acts as the literal Siegel transformation
with singular direction (e₀,0) and parameter (a e₁,0). Every symplectic
transvection is a conjugate of one of these, and conjugation by every
quadratic isometry preserves the Siegel-generated subgroup. Symplectic
transvection generation therefore puts the entire exterior image in Omega.

The reverse image inclusion is proved in `Surjectivity.lean`. This proof
uses no order formula or identification with an orthogonal commutator group.
The conjugation argument adapts ATLAS `LinearGroups/Orthogonal/ElementaryNormal.lean`,
using CFSG's literal carriers; the base matrix calculation uses the existing
ATLAS exterior-square coordinates. Source: GLS3 §2.7, odd B₂/C₂ comparison.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.OddFiveComparison
open Matrix Atlas.Order20160A8.Bivectors
open ClassicalOrthogonal.Quadratic Atlas.Order20160A8
variable {F : Type} [Field F]

private theorem transvection_matrix (a : F) :
    symplecticMatrix (Matrix.PSp4Three.transvection (Matrix.PSp4Three.e 0) a) =
      !![1,0,-a,0; 0,1,0,0; 0,0,1,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticMatrix, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.PSp4Three.transvection,
      LinearMap.toMatrix'_apply, Matrix.PSp4Three.transvectionMap_apply,
      Matrix.PSp4Three.form_apply, Matrix.PSp4Three.e, Fin.sum_univ_two,
      finSumFinEquiv, Fin.addCases]

theorem base_polar (a : F) :
    (formB 2 F).polarBilin (e 0, 0) (a • e 1, 0) = 0 := by
  simp [-QuadraticMap.polarBilin_apply_apply, polarB_apply, polarD_apply, e]

/-- A matrix transvection acts as the displayed literal Siegel transformation. -/
theorem transvection_base (a : F) :
    toOrthogonal (Matrix.PSp4Three.transvection (Matrix.PSp4Three.e 0) a) =
      siegelElement (formB 2 F) (e 0, 0) (a • e 1, 0)
        (by simp [e]) (base_polar a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply kernelEquiv.injective
  apply Subtype.ext
  change fromB (onB _ v) = fromB (siegel (formB 2 F) (e 0, 0) (a • e 1, 0) v)
  have hv : fromB (onB (Matrix.PSp4Three.transvection (Matrix.PSp4Three.e 0) a) v) =
      exteriorMap (symplecticMatrix (Matrix.PSp4Three.transvection (Matrix.PSp4Three.e 0) a))
        (fromB v) :=
    congrArg Subtype.val (kernelEquiv.apply_symm_apply (kernelAction _ (kernelEquiv v)))
  rw [hv, transvection_matrix]
  ext i
  fin_cases i <;>
    simp [-QuadraticMap.polarBilin_apply_apply, exteriorMap, compound, first, second, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, fromB, siegel, polarB_apply, polarD_apply,
      formD_apply, e]
  all_goals ring

private theorem siegel_conj (g : Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB 2 F))
    (u v : VectorB 2 F) (hu : formB 2 F u = 0) (huv : (formB 2 F).polarBilin u v = 0) :
    g * siegelElement (formB 2 F) u v hu huv * g⁻¹ =
      siegelElement (formB 2 F) (g.val u) (g.val v)
        ((isometryCarrierEquiv _ g).map_app u |>.trans hu)
        ((isometry_polar _ (isometryCarrierEquiv _ g) u v).trans huv) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (siegel _ u v (g.val.symm x)) = siegel _ (g.val u) (g.val v) x
  have h := siegel_covariant _ (isometryCarrierEquiv _ g) u v (g.val.symm x)
  change g.val (siegel _ u v (g.val.symm x)) =
    siegel _ (g.val u) (g.val v) (g.val (g.val.symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- Siegel generators are stable under all isometries of the fixed odd form. -/
instance elementary_normal : (elementarySubgroup (formB 2 F)).Normal := by
  constructor
  intro x hx g
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, hu, huv, rfl⟩ := hx
    rw [siegel_conj]
    exact siegelElement_mem _ _ _ _ _
  | one => simp
  | mul x y _ _ ihx ihy =>
    have he : g * (x*y) * g⁻¹ = (g*x*g⁻¹) * (g*y*g⁻¹) := by group
    rw [he]
    exact (elementarySubgroup _).mul_mem ihx ihy
  | inv x _ ih =>
    have he : g * x⁻¹ * g⁻¹ = (g*x*g⁻¹)⁻¹ := by group
    rw [he]
    exact (elementarySubgroup _).inv_mem ih

/-- Every symplectic transvection has elementary orthogonal image. -/
theorem transvection_mem_elementary (v : Matrix.PSp4Three.Vector 2 F) (a : F) :
    toOrthogonal (Matrix.PSp4Three.transvection v a) ∈ elementarySubgroup (formB 2 F) := by
  by_cases hv : v = 0
  · subst v
    simp
  have he : Matrix.PSp4Three.e (n := 2) (F := F) 0 ≠ 0 := by
    intro h
    have h' := congrFun h (.inl 0)
    simp [Matrix.PSp4Three.e] at h'
  obtain ⟨g, _, hg⟩ := Matrix.PSp4Three.exists_generated_send he hv
  rw [← hg, ← Matrix.PSp4Three.transvection_conjugate, map_mul, map_mul, map_inv,
    transvection_base]
  exact (inferInstance : (elementarySubgroup (formB 2 F)).Normal).conj_mem _ (siegelElement_mem _ _ _ _ _) _

/-- The full matrix symplectic group lands in the literal Siegel-generated subgroup. -/
theorem toOrthogonal_mem_elementary (g : Matrix.PSp4Three.Sp 2 F) :
    toOrthogonal g ∈ elementarySubgroup (formB 2 F) := by
  have hle : Matrix.PSp4Three.transvectionGroup 2 F ≤
      (elementarySubgroup (formB 2 F)).comap toOrthogonal := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨v, a, rfl⟩
    exact transvection_mem_elementary v a
  exact hle (Matrix.PSp4Three.mem_transvectionGroup 2 g)

/-- The actual action with codomain restricted to its proved elementary image. -/
def toElementary : Matrix.PSp4Three.Sp 2 F →* OmegaOdd 2 F :=
  toOrthogonal.codRestrict _ toOrthogonal_mem_elementary

/-- Restriction preserves the original exterior action on every matrix. -/
theorem toElementary_coe (g : Matrix.PSp4Three.Sp 2 F) :
    (toElementary g).val = toOrthogonal g := rfl

/-- One direction of the exact geometric image identification. -/
theorem range_le_elementary :
    (toOrthogonal (F := F)).range ≤ elementarySubgroup (formB 2 F) := by
  rintro _ ⟨g, rfl⟩
  exact toOrthogonal_mem_elementary g

end ClassicalOrthogonal.OddFiveComparison
