module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
/-!
# The actual linear-three derived maximal parabolic

Maximality descends through SL₃→PSL₃. The scalar action on the original
fixed line identifies the derived subgroup with the perfect local affine
group, just as for the solvable residual. Both isomorphisms use the literal
projective parabolic and the same field.
Source: Aschbacher–Smith, Lemma 2.4.8(4), printed p.530.
-/
public section
noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

lemma pointParabolic_isCoatom : IsCoatom (pointParabolic F) := by
  have h := pointParabolicSL_isCoatom F
  rw [←pointParabolic_comap F] at h
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨?_,?_⟩
  · intro he
    exact h.1 (by rw [he,comap_top])
  · intro P hP hle
    have hp : P.comap (projection F) ≠ ⊤ := by
      intro he
      apply hP
      apply comap_injective (projection_surjective F)
      rw [he,comap_top]
    exact (comap_le_comap_of_surjective (projection_surjective F)).mp
      ((isCoatom_iff_ge_of_le.mp h).2 _ hp (comap_mono hle))

def pointParabolicResidualEquivAffine (hF : 4 ≤ Nat.card F) :
    solvableResidual (pointParabolic F) ≃* Matrix.SL2.Affine F :=
  ((equivMapOfInjective (solvableResidual (pointParabolic F))
    (pointParabolic F).subtype (pointParabolic F).subtype_injective).trans
    (MulEquiv.subgroupCongr (ParabolicResiduals.pointParabolic_residual F hF))).trans
    (pointLocalEquivAffine F)

lemma maximal_point_parabolic_residual_model (hF : 4 ≤ Nat.card F) :
    IsCoatom (pointParabolic F) ∧
      Nonempty (solvableResidual (pointParabolic F) ≃* Matrix.SL2.Affine F) :=
  ⟨pointParabolic_isCoatom F,⟨pointParabolicResidualEquivAffine F hF⟩⟩

private def pointScalarForDerived : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := by simp
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h).mp h.property
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]

lemma pointParabolicSL_derived (hF : 4 ≤ Nat.card F) :
    (commutator (pointParabolicSL F)).map (pointParabolicSL F).subtype = pointLocalSL F := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    have hh := Abelianization.commutator_subset_ker (pointScalarForDerived F).toHomUnits hx
    have hs : x.val.val 0 0 = 1 := congrArg (fun u : Fˣ => (u:F)) hh
    exact (mem_pointLocalSL_iff F x).mpr ⟨hs,(mem_pointParabolicSL_iff F x).mp x.property⟩
  · rw [←ParabolicResiduals.pointParabolicSL_residual F hF]
    exact map_mono ((solvableResidual_le_derivedSeries 1).trans (derivedSeries_one _).le)

lemma pointParabolic_derived (hF : 4 ≤ Nat.card F) :
    (commutator (pointParabolic F)).map (pointParabolic F).subtype = pointLocal F := by
  let f := (projection F).subgroupMap (pointParabolicSL F)
  have hf : Function.Surjective f := (projection F).subgroupMap_surjective _
  have hm : (commutator (pointParabolicSL F)).map f = commutator (pointParabolic F) := by
    rw [_root_.map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    rfl
  have hh := congrArg (Subgroup.map ((pointParabolicSL F).map (projection F)).subtype) hm
  rw [Subgroup.map_map] at hh
  have he : ((pointParabolicSL F).map (projection F)).subtype.comp f = (projection F).comp (pointParabolicSL F).subtype := rfl
  rw [he,←Subgroup.map_map,pointParabolicSL_derived F hF] at hh
  exact hh.symm

def pointParabolicDerivedEquivAffine (hF : 4 ≤ Nat.card F) :
    commutator (pointParabolic F) ≃* Matrix.SL2.Affine F :=
  ((equivMapOfInjective (commutator (pointParabolic F))
    (pointParabolic F).subtype (pointParabolic F).subtype_injective).trans
    (MulEquiv.subgroupCongr (pointParabolic_derived F hF))).trans (pointLocalEquivAffine F)

end Matrix.PSL3.LinearThree
