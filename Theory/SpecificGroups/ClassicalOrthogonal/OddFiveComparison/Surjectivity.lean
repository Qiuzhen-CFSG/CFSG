/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
See also LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison.Image
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry

/-!
# Every odd-five Siegel generator lifts through exterior square

The matrix with identity diagonal blocks and a symmetric upper-right block
lifts every Siegel transformation based at (e₀,0). The four-dimensional
Plücker relation proves that every singular bivector is decomposable.
Symplectic contraction makes its two factors orthogonal, so the existing
alternating-frame theorem normalizes every nonzero singular vector.
Conjugation then lifts every literal Siegel generator, proving the exact
image equality over any field, with no order comparison.

This extends the CFSG port of ATLAS's `B2ExteriorCoordinates.lean` and
`B2ExteriorSymplectic.lean`. The explicit base lift and singular-vector
normalization replace the `B2ExteriorOrder.lean` surjectivity argument;
CFSG's original elementary group and quadratic-isometry carrier are retained.
Source: GLS3 §2.7, the B₂/C₂ comparison used in Aschbacher–Smith A.2.17.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.OddFiveComparison
open Matrix Atlas.Order20160A8.Bivectors
open ClassicalOrthogonal.Quadratic Atlas.Order20160A8
variable {F : Type} [Field F]

/-- An explicit symplectic matrix lifting every Siegel parameter at the base singular point. -/
def baseLift (w : VectorB 2 F) : Matrix.PSp4Three.Sp 2 F :=
  ⟨Matrix.fromBlocks 1 !![-w.1 (.inl 1), w.2; w.2, w.1 (.inr 1)] 0 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp only [transpose_one, transpose_zero, mul_zero, zero_mul, mul_one, one_mul,
      sub_zero, and_true, true_and]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩

private theorem baseLift_matrix (w : VectorB 2 F) :
    symplecticMatrix (baseLift w) =
      !![1,0,-w.1 (.inl 1),w.2; 0,1,w.2,w.1 (.inr 1); 0,0,1,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticMatrix, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply, baseLift, Matrix.fromBlocks,
      finSumFinEquiv, Fin.addCases]

/-- The literal five-space action of the displayed upper symplectic matrix. -/
theorem toOrthogonal_baseLift (w : VectorB 2 F)
    (hw : (formB 2 F).polarBilin (e 0, 0) w = 0) :
    toOrthogonal (baseLift w) =
      siegelElement (formB 2 F) (e 0, 0) w (by simp [e]) hw := by
  have hw0 : w.1 (.inr 0) = 0 := by
    simpa [-QuadraticMap.polarBilin_apply_apply, polarB_apply, polarD_apply, e] using hw
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply kernelEquiv.injective
  apply Subtype.ext
  change fromB (onB _ v) = fromB (siegel (formB 2 F) (e 0, 0) w v)
  have hv : fromB (onB (baseLift w) v) = exteriorMap (symplecticMatrix (baseLift w)) (fromB v) :=
    congrArg Subtype.val (kernelEquiv.apply_symm_apply (kernelAction _ (kernelEquiv v)))
  rw [hv, baseLift_matrix]
  ext i
  fin_cases i <;>
    simp [-QuadraticMap.polarBilin_apply_apply, exteriorMap, compound, first, second,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, fromB,
      siegel, polarB_apply, polarD_apply, formD_apply, e, hw0]
  all_goals ring

/-- The Plücker relation is sufficient for decomposability in four-space. -/
theorem exists_wedge_of_pfaffian_zero (w : Six F) (hw : pfaffian w = 0) :
    ∃ x y : Four F, wedge x y = w := by
  have hp : w 0 * w 5 - w 1 * w 4 + w 2 * w 3 = 0 := hw
  by_cases h0 : w 0 = 0
  · by_cases h1 : w 1 = 0
    · by_cases h2 : w 2 = 0
      · by_cases h3 : w 3 = 0
        · by_cases h4 : w 4 = 0
          · refine ⟨![0,0,1,0], ![0,0,0,w 5], ?_⟩
            ext i
            fin_cases i <;> simp [wedge, h0, h1, h2, h3, h4]
          · refine ⟨![0,1,w 5 / w 4,0], ![0,0,0,w 4], ?_⟩
            ext i
            fin_cases i <;> simp [wedge, h0, h1, h2, h3, h4]
        · refine ⟨![0,1,0,-w 5 / w 3], ![0,0,w 3,w 4], ?_⟩
          ext i
          fin_cases i <;> simp [wedge, h0, h1, h2, h3]
      · refine ⟨![1,w 4 / w 2,w 5 / w 2,0], ![0,w 0,w 1,w 2], ?_⟩
        ext i
        fin_cases i <;> simp [wedge, h0, h1, h2]
        · have hz : w 3 = 0 := by simpa [h0,h1,h2] using hp
          exact hz.symm
    · refine ⟨![1,w 3 / w 1,0,-w 5 / w 1], ![0,w 0,w 1,w 2], ?_⟩
      ext i
      fin_cases i <;> simp [wedge, h0, h1]
      all_goals field_simp
      simp only [h0, zero_mul, zero_sub] at hp
      linear_combination hp
  · refine ⟨![1,0,-w 3 / w 0,-w 4 / w 0], ![0,w 0,w 1,w 2], ?_⟩
    ext i
    fin_cases i <;> simp [wedge, h0]
    all_goals field_simp
    linear_combination -hp

/-- Normalize every nonzero singular vector using the actual exterior action. -/
theorem exists_normalize_singular (u : VectorB 2 F) (hu : u ≠ 0)
    (hqu : formB 2 F u = 0) :
    ∃ g : Matrix.PSp4Three.Sp 2 F, (toOrthogonal g).val u = (e 0, 0) := by
  have hfu : fromB u ≠ 0 := by
    intro h
    apply hu
    apply kernelEquiv.injective
    apply Subtype.ext
    change fromB u = (kernelEquiv (0 : VectorB 2 F)).val
    rw [map_zero]
    exact h
  obtain ⟨a,b,hab⟩ := exists_wedge_of_pfaffian_zero (fromB u) ((fromB_pfaffian u).trans hqu)
  obtain ⟨x,rfl⟩ := symplecticCoordinates_surjective a
  obtain ⟨y,rfl⟩ := symplecticCoordinates_surjective b
  have hx : x ≠ 0 := by
    intro h
    apply hfu
    rw [← hab, h]
    ext i
    fin_cases i <;> simp [wedge, symplecticCoordinates]
  have hy : y ∉ Submodule.span F {x} := by
    intro h
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp h
    apply hfu
    rw [← hab]
    ext i
    fin_cases i <;> simp [wedge, symplecticCoordinates] <;> ring
  have hxy : Matrix.PSp4Three.form x y = 0 := by
    rw [← contraction_wedge, hab, fromB_contraction]
  obtain ⟨k,hkx,hky⟩ := Matrix.PSp4Three.exists_isometry_orthogonal_pair 0
    (Matrix.PSp4Three.form (n := 2) (F := F)) Matrix.PSp4Three.form_alternating
    Matrix.PSp4Three.form_nondegenerate
    (by simp [Matrix.PSp4Three.Vector, Matrix.PSp4Three.Index]) x y hx hy hxy
  let g := Matrix.PSp4Three.ofLinear k.toLinearEquiv k.map_app'
  have hgx : g • x = Matrix.PSp4Three.e 0 := by
    simpa only [g, Matrix.PSp4Three.ofLinear_apply, LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using hkx
  have hgy : g • y = Matrix.PSp4Three.e 1 := by
    simpa only [g, Matrix.PSp4Three.ofLinear_apply, LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using hky
  refine ⟨g, ?_⟩
  apply kernelEquiv.injective
  apply Subtype.ext
  change fromB (onB g u) = fromB (e 0, 0)
  have hact : fromB (onB g u) = exteriorMap (symplecticMatrix g) (fromB u) :=
    congrArg Subtype.val (kernelEquiv.apply_symm_apply (kernelAction g (kernelEquiv u)))
  rw [hact, ← hab, exteriorMap_wedge, symplecticMatrix_mulVec, symplecticMatrix_mulVec]
  change wedge (symplecticCoordinates (g • x)) (symplecticCoordinates (g • y)) = _
  rw [hgx,hgy]
  ext i
  fin_cases i <;> simp [wedge, symplecticCoordinates, Matrix.PSp4Three.e, fromB, e]

/-- Every literal Siegel generator has a lift through the exterior action. -/
theorem siegelElement_mem_range (u v : VectorB 2 F)
    (hu : formB 2 F u = 0) (huv : (formB 2 F).polarBilin u v = 0) :
    siegelElement (formB 2 F) u v hu huv ∈ (toOrthogonal (F := F)).range := by
  by_cases hz : u = 0
  · subst u
    have hs : siegelElement (formB 2 F) 0 v hu huv = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel (formB 2 F) 0 v x = x
      simp [siegel]
    rw [hs]
    exact (toOrthogonal (F := F)).range.one_mem
  obtain ⟨g, hg⟩ := exists_normalize_singular u hz hu
  let t := toOrthogonal g
  let w := t.val v
  have hw : (formB 2 F).polarBilin (e 0, 0) w = 0 := by
    have hp := isometry_polar (formB 2 F) (isometryCarrierEquiv _ t) u v
    change (formB 2 F).polarBilin (t.val u) (t.val v) = _ at hp
    simpa only [t, hg] using hp.trans huv
  have heq : t * siegelElement (formB 2 F) u v hu huv * t⁻¹ = toOrthogonal (baseLift w) := by
    rw [toOrthogonal_baseLift w hw]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change t.val (siegel _ u v (t.val.symm x)) = siegel _ (e 0, 0) w x
    have hp := siegel_covariant (formB 2 F) (isometryCarrierEquiv _ t) u v (t.val.symm x)
    change t.val (siegel _ u v (t.val.symm x)) =
      siegel _ (t.val u) w (t.val (t.val.symm x)) at hp
    simpa only [LinearEquiv.apply_symm_apply, t, hg] using hp
  have ht : t ∈ (toOrthogonal (F := F)).range := ⟨g, rfl⟩
  have hb : t * siegelElement (formB 2 F) u v hu huv * t⁻¹ ∈
      (toOrthogonal (F := F)).range := by
    rw [heq]
    exact ⟨baseLift w, rfl⟩
  have hc := (toOrthogonal (F := F)).range.mul_mem
    ((toOrthogonal (F := F)).range.mul_mem ((toOrthogonal (F := F)).range.inv_mem ht) hb) ht
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hc

/-- The image is exactly the original Siegel-generated group, in every characteristic. -/
theorem toOrthogonal_range :
    (toOrthogonal (F := F)).range = elementarySubgroup (formB 2 F) := by
  apply le_antisymm range_le_elementary
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨u, v, hu, huv, rfl⟩
  exact siegelElement_mem_range u v hu huv

/-- Surjectivity uses explicit Siegel lifts, without a group-order comparison. -/
theorem toElementary_surjective : Function.Surjective (toElementary (F := F)) := by
  intro g
  have hg : g.val ∈ (toOrthogonal (F := F)).range := by
    rw [toOrthogonal_range]
    exact g.property
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, Subtype.ext hx⟩

end ClassicalOrthogonal.OddFiveComparison
