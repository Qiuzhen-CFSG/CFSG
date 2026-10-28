module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.ExtensionBorels.Alignment

/-!
# Reading compatible Borel markings in the literal action quotient

The placement producer marks the whole overgroup K*Lᵥ* and the embedded
component compatibly. These equations recover the inverse component marking
of Tᵥ* ∩ K*, and the inverse whole-group marking of the relative Borel.
They let the root calculations use exactly the maps supplied by placement,
including nonsplit extensions, without a new alignment assumption.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
variable {G : Type*} [Group G] {L V : Subgroup G}
    {s : Marking L V} {T : Subgroup G} {K : Subgroup (Gv (markedV s))}
    {M H : Type*} [Group M] [Group H] {i : M →* H} {U : Subgroup M} {B : Subgroup H}

namespace ExtensionBorels.CompatibleBorelData

/-- The whole-model inverse marking restricts to the component inverse marking. -/
theorem inverse_compatible (d : CompatibleBorelData s T K i U B) :
    (((NormalizerAction.componentImage K ⊔ residualStar s K).subtype.comp
      d.overgroupEquiv.symm.toMonoidHom).comp i) =
        (NormalizerAction.componentImage K).subtype.comp d.componentEquiv.symm.toMonoidHom := by
  ext x
  have h := d.compatible (d.componentEquiv.symm x)
  rw [d.componentEquiv.apply_symm_apply] at h
  exact congrArg Subtype.val ((d.overgroupEquiv.symm_apply_apply _).symm.trans
    (congrArg d.overgroupEquiv.symm h)).symm

/-- The literal Sylow intersection is the image under the component marking. -/
theorem component_sylow_image (d : CompatibleBorelData s T K i U B) :
    U.map ((NormalizerAction.componentImage K).subtype.comp d.componentEquiv.symm.toMonoidHom) =
      NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K := by
  rw [← d.inverse_compatible, ← map_map, ← d.sylow_image, map_map]
  have he : ((NormalizerAction.componentImage K ⊔ residualStar s K).subtype.comp
      d.overgroupEquiv.symm.toMonoidHom).comp d.overgroupEquiv.toMonoidHom =
        (NormalizerAction.componentImage K ⊔ residualStar s K).subtype := by
    ext x
    exact congrArg Subtype.val (d.overgroupEquiv.symm_apply_apply x)
  rw [he, map_subgroupOf_eq_of_le (inf_le_right.trans le_sup_left)]

/-- The actual relative Borel is the image of the concrete whole-model Borel. -/
theorem whole_borel_image (d : CompatibleBorelData s T K i U B) :
    B.map ((NormalizerAction.componentImage K ⊔ residualStar s K).subtype.comp
      d.overgroupEquiv.symm.toMonoidHom) = borelCandidate s T K := by
  conv_lhs => arg 2; rw [← d.candidate_image]
  rw [map_map]
  have he : ((NormalizerAction.componentImage K ⊔ residualStar s K).subtype.comp
      d.overgroupEquiv.symm.toMonoidHom).comp d.overgroupEquiv.toMonoidHom =
        (NormalizerAction.componentImage K ⊔ residualStar s K).subtype := by
    ext x
    exact congrArg Subtype.val (d.overgroupEquiv.symm_apply_apply x)
  rw [he, map_subgroupOf_eq_of_le (show borelCandidate s T K ≤
    NormalizerAction.componentImage K ⊔ residualStar s K from inf_le_left)]

/-- In an inner presentation, the Borel image uses the same component map
as the root Sylow. No equality of the two equivalences is assumed. -/
theorem inner_borel_image {B₀ : Subgroup M}
    (d : CompatibleBorelData s T K (MonoidHom.id M) U B₀) :
    B₀.map ((NormalizerAction.componentImage K).subtype.comp d.componentEquiv.symm.toMonoidHom) =
      borelCandidate s T K := by
  rw [← d.inverse_compatible, MonoidHom.comp_id]
  exact d.whole_borel_image

end ExtensionBorels.CompatibleBorelData
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
