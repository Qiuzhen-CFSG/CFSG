module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups.Basic
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.Representation.G2BinaryFlagNormalization
public import Theory.GroupTheory.ConjugateSpanSylow
/-!
# The binary unitary cubic generates under the point parabolic

The actual plane cubic together with the derived point parabolic generates
G₂(2)′. Its span under that parabolic is therefore normal and nontrivial;
simplicity identifies it with the whole derived group. The point parabolic
preserves the literal three-space in the same natural coordinates.

Source application: Aschbacher–Smith 13.3.15(6), printed p.894.
-/
public section
open Subgroup Atlas.G2 Atlas.G2.BinaryParabolicPair Atlas.G2.BinaryCore
open Atlas.G2.Natural.BinaryPointFlag
namespace Atlas.G2.Natural.BinaryFlagGeneration
abbrev cubic : DerivedModel := ⟨cubicActor,cubicActor_mem_derived⟩
theorem cubic_span : conjugateSpanBy (zpowers cubic) derivedSecond = ⊤ := by
  let J := conjugateSpanBy (zpowers cubic) derivedSecond
  have hn : normalizer (J : Set DerivedModel) = ⊤ := by
    apply SevenSylowOvergroups.eq_top_of_actors
    · exact derivedSylow_le_second.trans (le_normalizer_conjugateSpanBy _ _)
    · exact J.le_normalizer (le_conjugateSpanBy _ _ (mem_zpowers cubic))
    · exact le_normalizer_conjugateSpanBy _ _ movingActor_mem_derivedSecond
  let : J.Normal := normalizer_eq_top_iff.mp hn
  let : IsSimpleGroup DerivedModel := Atlas.G2.isSimple_commutator_binary
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal J inferInstance with h|h
  · have hc : cubic∈J := le_conjugateSpanBy (zpowers cubic) derivedSecond (mem_zpowers cubic)
    rw [h,mem_bot] at hc
    have hh := congrArg (fun x:DerivedModel=>orderOf x.val) hc
    norm_num only [cubicActor_order,OneMemClass.coe_one,orderOf_one] at hh
  · exact h

theorem derivedSecond_preserves_seed (g:DerivedModel) (hg:g∈derivedSecond)
    (v:W) (hv:v∈seed) :
    Restricted.NaturalCoordinates.action F g.val v∈seed := by
  exact pointParabolic_preserves_seed g.val hg v hv
theorem cubic_span_ambient :
    conjugateSpanBy (zpowers cubicActor) derivedSecondAmbient =
      commutator (Model F) := by
  have h := congrArg (fun J:Subgroup DerivedModel=>J.map DerivedModel.subtype) cubic_span
  rw [map_conjugateSpanBy,MonoidHom.map_zpowers,derivedSecond_map_subtype,
    ←MonoidHom.range_eq_map,DerivedModel.range_subtype] at h
  exact h

end Atlas.G2.Natural.BinaryFlagGeneration
