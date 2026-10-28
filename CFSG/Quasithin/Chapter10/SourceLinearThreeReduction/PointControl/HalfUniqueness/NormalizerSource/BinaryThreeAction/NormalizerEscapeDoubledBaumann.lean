module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeDoubledThompson
public import CFSG.Quasithin.ChapterB.Section02.BaumannNormalizerImage
public import Theory.SpecificGroups.PSL3Two.Parabolics.ShearNormalizer

/-!
# The actual Baumann normalizer in the doubled MS component

The normalizer lifting theorem applies to the original Sylow subgroup,
with its full kernel retained. The simultaneously marked Baumann image
therefore identifies the component intersection with the line parabolic.
No extension of the complete core action to an outside normalizer is used.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open BinaryLinearThree BinaryLinearThree.DoubledOffenders
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
variable {J : Type*} [Group J] [Finite J] {κ : GroupClass} {L R : Subgroup J}
    {h : Input κ L R} {q : AbelianCore.NaturalQuotient h 2} {P : Sylow 2 J}

private theorem component_image (d : DoubledCoreAction h q P) :
    L.map d.actor = δ.range := by
  apply le_antisymm
  · rintro _ ⟨l,hl,rfl⟩
    exact ⟨_,(d.component ⟨l,hl⟩).symm⟩
  · rintro _ ⟨g,rfl⟩
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
    refine ⟨l,l.property,?_⟩
    rw [d.component,hl,MulEquiv.apply_symm_apply]

private theorem restricted_normalizer (A : Subgroup Matrix.PSL3Two.SL) :
    δ.range ⊓ normalizer (A.map δ : Set D) = (normalizer (A : Set _)).map δ := by
  have he : (normalizer (A.map δ : Set D)).comap δ = normalizer (A : Set _) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective δ_injective]
  rw [←he,map_comap_eq,inf_comm]

/-- The literal component intersection with the actual Baumann normalizer
maps onto the line parabolic in the same frame as the component Sylow. -/
theorem DoubledCoreAction.baumann_normalizer_image (d : DoubledCoreAction h q P)
    (hc : IsMulCommutative (commutatorCore L)) (hRP : R = (P : Subgroup J)) :
    (L ⊓ normalizer (ChapterB.baumann R : Set J)).map d.actor =
      ((Matrix.PSL3Two.lineParabolicSL.map (MulAut.conj d.frame).toMonoidHom).map δ) := by
  let := h.component_normal
  have hgen : L ⊔ (P : Subgroup J) = ⊤ := hRP ▸ h.sup_eq_top
  have himage := ChapterB.normal_baumann_normalizer_image P L hgen d.actor
  rw [←hRP,component_image d,(d.thompson_baumann_images hc hRP.le).2,
    restricted_normalizer,Matrix.PSL3Two.normalizer_shear_conjugate] at himage
  exact himage

end CFSG.Quasithin.ChapterC.BinaryMS
