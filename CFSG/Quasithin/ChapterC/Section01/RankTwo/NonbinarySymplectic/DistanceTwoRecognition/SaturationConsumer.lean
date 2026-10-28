module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.NormalizerComparison

/-!
# A conditional saturation consumer for the characteristic replacement

The replacement comparison already places the marked normalizer 2-core
between the replacement image and the original radical image.  Consequently,
the additional source premise that the replacement image is the original
radical image forces equality with that normalizer core.  The literal
projection kernel then transports this equality back to the characteristic
replacement.

This is deliberately conditional: the equality of the replacement and
original radical images is the unresolved original-radical source step in
the distance-two branch.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

omit [CharP F 2] in
/-- If the replacement image is the original marked radical image, the
replacement radical is saturated in its literal overgroup.  The premise is
the exact original-radical characteristic/saturation input still missing
from the unconditional distance-two source proof. -/
theorem replacement_radical_saturated_of_original_image_eq
    (f : d.overgroup →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 d.overgroup)
    (hmark : d.radical.map f =
      (d.ambient.subgroupOf K).map (componentProjection h))
    (horiginal : (d.ambient.subgroupOf K).map (componentProjection h) =
      (R.subgroupOf K).map (componentProjection h)) :
    (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical := by
  apply (replacement_radical_saturation_iff h d f hf hk).mpr
  have hbounds := replacement_marked_normalizer_core_bounds h d
  have hcore :
      (normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
        Set (Sp F))).pCoreIn 2 =
        (d.ambient.subgroupOf K).map (componentProjection h) := by
    apply le_antisymm
    · exact hbounds.2.trans_eq horiginal.symm
    · exact hbounds.1
  calc
    (normalizer (d.radical.map f : Set (Sp F))).pCoreIn 2 =
        (normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
          Set (Sp F))).pCoreIn 2 := by
      rw [hmark]
    _ = (d.ambient.subgroupOf K).map (componentProjection h) := hcore
    _ = d.radical.map f := hmark.symm

/-- The literal positive-distance source supplies the projection and its
kernel, so equality of the two original marked images alone suffices for
the saturation premise used by the independent field-restriction proof. -/
theorem replacement_radical_saturated_of_marked_image_eq
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    (horiginal : (d.ambient.subgroupOf K).map (componentProjection h) =
      (R.subgroupOf K).map (componentProjection h)) :
    (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical := by
  obtain ⟨f,hf,hk,_,hmark⟩ := exists_replacement_marked_projection h d g hb
  exact replacement_radical_saturated_of_original_image_eq h d f hf hk hmark horiginal

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
