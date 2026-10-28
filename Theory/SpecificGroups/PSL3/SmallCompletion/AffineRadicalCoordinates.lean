module

public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourEndpointInclusions
public import Theory.SpecificGroups.SL2.Affine.OppositeRadical
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry

/-!
# Literal affine radical images in the native line parabolic

The existing affine equivalence sends translations to the line radical and
the elementary upper-root radical to the point radical. Consequently the
part of the line endpoint normalizing the opposite radical lies in the
whole original Borel.
-/

public noncomputable section
open Subgroup Matrix SemidirectProduct
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3Even.UnipotentGeometry Representation.SL2FourNatural

/-- Existing affine coordinates followed by the literal projective inclusion. -/
@[expose] def affineLineEmbedding : Matrix.SL2.Affine F →* PSL(3,F) :=
  (lineLocal F).subtype.comp (lineLocalEquivAffine F).symm.toMonoidHom

theorem affineLineEmbedding_injective : Function.Injective affineLineEmbedding :=
  Subtype.val_injective.comp (lineLocalEquivAffine F).symm.injective

private theorem line_affine_coordinates (u : U F) :
    lineLocalEquivAffine F (lineUnipotent u)=
      ⟨Multiplicative.ofAdd ![u.c,u.y],upper u.x⟩ := by
  rw [lineUnipotent,lineLocalEquivAffine_project]
  rfl

private theorem affineLineEmbedding_coordinates (u : U F) :
    affineLineEmbedding ⟨Multiplicative.ofAdd ![u.c,u.y],upper u.x⟩=projective F u := by
  rw [←line_affine_coordinates]
  change ((lineLocalEquivAffine F).symm (lineLocalEquivAffine F (lineUnipotent u)) : PSL(3,F))=_
  rw [MulEquiv.symm_apply_apply,lineUnipotent_val]

/-- The original translation radical has exactly its native projective image. -/
theorem affineLineEmbedding_translations :
    (Matrix.SL2.translations F).map affineLineEmbedding=projectivePlane₂ F := by
  rw [←Matrix.SL2.range_inl_eq_translations,←MonoidHom.range_comp]
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    have he : (inl v : Matrix.SL2.Affine F)=
        ⟨Multiplicative.ofAdd ![v.toAdd 0,v.toAdd 1],upper 0⟩ := by
      apply SemidirectProduct.ext
      · apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> rfl
      · apply Subtype.ext
        funext i j
        fin_cases i <;> fin_cases j <;> simp [upper]
    change affineLineEmbedding (inl v)∈_
    rw [he,affineLineEmbedding_coordinates (⟨0,v.toAdd 1,v.toAdd 0⟩ : U F)]
    exact mem_map_of_mem _ ((mem_V₂ F _).mpr rfl)
  · rintro _ ⟨u,hu,rfl⟩
    have hx := (mem_V₂ F u).mp hu
    refine ⟨Multiplicative.ofAdd ![u.c,u.y],?_⟩
    change affineLineEmbedding (inl (Multiplicative.ofAdd ![u.c,u.y]))=projective F u
    rw [←affineLineEmbedding_coordinates]
    congr 1
    apply SemidirectProduct.ext
    · rfl
    · apply Subtype.ext
      funext i j
      fin_cases i <;> fin_cases j <;> simp [upper,hx]

/-- The original elementary opposite radical has exactly the other native image. -/
theorem affineLineEmbedding_opposite :
    Matrix.SL2.oppositeRoot.map affineLineEmbedding=projectivePlane₁ F := by
  change Matrix.SL2.oppositeRootMap.range.map affineLineEmbedding=_
  rw [←MonoidHom.range_comp]
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    change affineLineEmbedding ⟨Multiplicative.ofAdd ![v.toAdd.1,0],upper v.toAdd.2⟩∈_
    rw [affineLineEmbedding_coordinates (⟨v.toAdd.2,0,v.toAdd.1⟩ : U F)]
    exact mem_map_of_mem _ ((mem_V₁ F _).mpr rfl)
  · rintro _ ⟨u,hu,rfl⟩
    have hy := (mem_V₁ F u).mp hu
    refine ⟨Multiplicative.ofAdd (u.c,u.x),?_⟩
    change affineLineEmbedding ⟨Multiplicative.ofAdd ![u.c,0],upper u.x⟩=projective F u
    rw [←hy,affineLineEmbedding_coordinates]

/-- Inside the original line endpoint, normalizing the opposite radical
forces membership in the complete native Borel. -/
theorem line_normalizer_opposite_le_borel :
    lineLocal F ⊓ normalizer (projectivePlane₁ F : Set PSL(3,F))≤borel F := by
  have he : Matrix.PSL3.RootPlaneGeometry.rootPlane F true=projectivePlane₁ F := by
    simp only [Matrix.PSL3.RootPlaneGeometry.rootPlane,
      Matrix.PSL3.RootPlaneGeometry.rootPlaneSL,if_true,projectivePlane₁,Subgroup.map_map]
    rfl
  rw [←he,Matrix.PSL3.RootPlaneGeometry.normalizer_rootPlane]
  change lineLocal F ⊓ pointParabolic F≤borel F
  intro x hx
  have hl : x∈lineParabolic F := by
    rw [lineParabolic_eq_sup]
    exact (show lineLocal F≤lineLocal F⊔borel F from le_sup_left) hx.1
  have heq : pointParabolic F ⊓ lineParabolic F=borel F := by
    apply comap_injective (projection_surjective F)
    rw [comap_inf,pointParabolic_comap,lineParabolic_comap,borel_comap]
    rfl
  rw [←heq]
  exact ⟨hx.2,hl⟩

end Matrix.PSL3.SmallCompletion
