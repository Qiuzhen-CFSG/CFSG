module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Affine
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Planes

/-!
# Full linear action on the standard trio's plane space

Plane words are linear coordinate functions supported on octad zero. Pulling
such a word back along an affine lift with linear part `A` transforms its
coefficients by the inverse transpose of `A`. The translation term is a scalar
multiple of the octad word and therefore vanishes in the cocode. Every binary
invertible matrix has determinant one, so the native affine quotient's
surjectivity realizes every linear automorphism of these plane coefficients.

This calculation is independent of identifying the plane space with the
whole two-core fixed space; that equality is used by the chapter adapter.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.6(2),
printed p.401/PDF p.412, lower-action clause.
-/

@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open scoped BigOperators MatrixGroups
namespace MathieuCode.TrioCalculation
noncomputable section

/-- On the covectors supported in octad zero, a native affine lift acts by
inverse transpose. Its translation contributes only a Golay octad word. -/
lemma standardPlaneMap_action_of_affine (g : trioStabilizer standardTrio) (A : SL(3, ZMod 2))
    (hg : standardAffineHom g = (1, A)) (a : Vector) :
    cocodeRepresentation g.val (standardPlaneMap a) =
      standardPlaneMap (Matrix.SpecialLinearGroup.toLin' (A⁻¹).transpose a) := by
  obtain ⟨t, ht⟩ := affineQuotient_spec affineCoverage g⁻¹
  have hgi : affineQuotient affineCoverage g⁻¹ = (1, A⁻¹) := by
    change standardAffineHom g⁻¹ = _
    rw [map_inv, hg]
    rfl
  rw [hgi] at ht
  have ht' (i : Fin 3) (v : Vector) :
      (g⁻¹).val.val (point (i, v)) =
        point (i, Matrix.SpecialLinearGroup.toLin' A⁻¹ v + t i) := ht i v
  let b := Matrix.SpecialLinearGroup.toLin' (A⁻¹).transpose a
  have hd (v : Vector) : (∑ k, a k * (Matrix.SpecialLinearGroup.toLin' A⁻¹ v) k) =
      ∑ k, b k * v k := by
    simpa only [b, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      Matrix.SpecialLinearGroup.coe_transpose, Matrix.mulVec_transpose, dotProduct] using
      Matrix.dotProduct_mulVec a (A⁻¹).val v
  change codeInCore.mkQ (coreRepresentation g.val (standardPlaneCore a)) =
    codeInCore.mkQ (standardPlaneCore b)
  apply (Submodule.Quotient.eq codeInCore).mpr
  change (coreRepresentation g.val (standardPlaneCore a)).val -
    (standardPlaneCore b).val ∈ golay
  have he : (coreRepresentation g.val (standardPlaneCore a)).val -
      (standardPlaneCore b).val = (∑ k, a k * t 0 k) • wordOfSet (standardTrioOctad 0) := by
    funext x
    obtain ⟨⟨i, v⟩, rfl⟩ := point.surjective x
    change standardPlaneWord a ((g⁻¹).val.val (point (i, v))) -
      standardPlaneWord b (point (i, v)) = _
    rw [ht', standardPlaneWord_point, standardPlaneWord_point]
    simp only [Pi.smul_apply, smul_eq_mul, wordOfSet, point_mem_octad_iff]
    by_cases hi : i = 0
    · subst i
      simp only [ite_true, Pi.add_apply, mul_add, Finset.sum_add_distrib, hd,
        mul_one, add_sub_cancel_left]
    · simp [hi]
  rw [he]
  apply golay.smul_mem
  rw [golay_eq_span_octads]
  exact Submodule.subset_span ⟨standardTrioOctad 0, standardTrioOctad_mem 0, rfl⟩

/-- Every linear automorphism of the plane coefficients is induced by an
actual standard-trio stabilizer element on the native cocode. -/
lemma standardPlaneMap_full_action (f : Vector ≃ₗ[ZMod 2] Vector) :
    ∃ g : trioStabilizer standardTrio, ∀ a,
      cocodeRepresentation g.val (standardPlaneMap a) = standardPlaneMap (f a) := by
  let M := LinearMap.toMatrix' f.toLinearMap
  have hdet : M.det = 1 := by
    have hu : IsUnit M.det := by
      rw [LinearMap.det_toMatrix']
      exact f.isUnit_det'
    exact (show ∀ x : ZMod 2, x ≠ 0 → x = 1 by decide) _ hu.ne_zero
  let A : SL(3, ZMod 2) := ⟨M.transpose, by simpa only [Matrix.det_transpose] using hdet⟩
  obtain ⟨g, hg⟩ := standardAffineHom_surjective (1, A⁻¹)
  refine ⟨g, fun a => ?_⟩
  rw [standardPlaneMap_action_of_affine g A⁻¹ hg, inv_inv]
  congr 1
  change Matrix.toLin' M.transpose.transpose a = f a
  rw [Matrix.transpose_transpose, Matrix.toLin'_toMatrix']
  rfl


end
end MathieuCode.TrioCalculation
