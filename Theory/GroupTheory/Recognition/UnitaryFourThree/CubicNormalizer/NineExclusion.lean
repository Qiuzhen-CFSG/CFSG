module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.MarkedKernel
public import Theory.GroupTheory.NormalFourCentralizerSeparation
public import Theory.SpecificGroups.AlternatingSix.ThreeNormalizer.Section

/-!
# Excluding the collapsed cubic kernel

If the canonical odd kernel V equals the Sylow-nine image X, its normalizer
lies in the original involution centralizer. Local Sylow maximality therefore
promotes X to an ambient Sylow subgroup. The actual A₆ section then conflicts
with the square-centralizer action of the original local normalizer.

Combined with the reflected kernel theorem this gives V elementary of order81.
The remaining inputs are precisely the earlier binary-local A₆ section,
local normalizer action and reflected actors; their source producer is the
45.3–45.6 root-pair family. No cubic-kernel size is assumed.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma45.7, printed p.245.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}
namespace IsType
variable (h : IsType z)
include h in
theorem exists_ambient_sylow_of_cubic_collapse (P : Sylow 3 (centralizer z))
    (hcollapse : CubicNormalizer.oddKernel
      ((P:Subgroup (centralizer z)).map (centralizer z).subtype)=
      (P:Subgroup (centralizer z)).map (centralizer z).subtype) :
    ∃ S : Sylow 3 G, (S:Subgroup G)=(P:Subgroup (centralizer z)).map (centralizer z).subtype := by
  let H := centralizer z
  let X := (P:Subgroup H).map H.subtype
  have hX : Nat.card X=9 := h.cubic_sylow_image_card P
  have hXH : X≤H := map_subtype_le _
  have hp : IsPGroup 3 X := P.isPGroup'.map H.subtype
  have hn : normalizer (X:Set G)≤H := by
    rw [h.toCentralizerHypothesis.cubic_normalizer_split X hX hXH,hcollapse]
    exact sup_le hXH inf_le_right
  have hi : ¬3∣X.relIndex H := by
    have he := relIndex_map_map_of_injective (P:Subgroup H) ⊤ H.subtype_injective
    rw [←MonoidHom.range_eq_map,H.range_subtype,relIndex_top_right] at he
    change ¬3∣((P:Subgroup H).map H.subtype).relIndex H
    rw [he]
    exact P.not_dvd_index
  have hglobal := not_dvd_relIndex_of_normalizer_inf_le X H ⊤ hp le_top hi
    (inf_le_left.trans hn)
  rw [relIndex_top_right] at hglobal
  exact ⟨hp.toSylow hglobal,rfl⟩

include h in
theorem normalizer_squares_of_cubic_collapse (P : Sylow 3 (centralizer z))
    (hcollapse : CubicNormalizer.oddKernel
      ((P:Subgroup (centralizer z)).map (centralizer z).subtype)=
      (P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hsquares : ∀g∈normalizer (((P:Subgroup (centralizer z)).map
      (centralizer z).subtype):Set G)⊓centralizer z,
      g^2∈Subgroup.centralizer (((P:Subgroup (centralizer z)).map
        (centralizer z).subtype):Set G)) :
    ∀g∈normalizer (((P:Subgroup (centralizer z)).map
      (centralizer z).subtype):Set G),
      g^2∈Subgroup.centralizer (((P:Subgroup (centralizer z)).map
        (centralizer z).subtype):Set G) := by
  let X := (P:Subgroup (centralizer z)).map (centralizer z).subtype
  have hX : Nat.card X=9 := h.cubic_sylow_image_card P
  have hXH : X≤centralizer z := map_subtype_le _
  have hn : normalizer (X:Set G)≤centralizer z := by
    rw [h.toCentralizerHypothesis.cubic_normalizer_split X hX hXH,hcollapse]
    exact sup_le hXH inf_le_right
  exact fun g hg=>hsquares g ⟨hg,hn hg⟩

include h in
theorem cubic_oddKernel_ne_of_A6_section (P : Sylow 3 (centralizer z))
    (hsquares : ∀g∈normalizer (((P:Subgroup (centralizer z)).map
      (centralizer z).subtype):Set G)⊓centralizer z,
      g^2∈Subgroup.centralizer (((P:Subgroup (centralizer z)).map
        (centralizer z).subtype):Set G))
    (M : Subgroup G) (f : M→*alternatingGroup (Fin 6)) (hf : Function.Surjective f) :
    CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)≠
      (P:Subgroup (centralizer z)).map (centralizer z).subtype := by
  intro hc
  obtain ⟨S,hS⟩ := h.exists_ambient_sylow_of_cubic_collapse P hc
  apply AlternatingSix.ThreeNormalizer.no_section_of_sylow_nine_square_centralizers
    S ?_ ?_ M f hf
  · rw [hS]
    exact h.cubic_sylow_image_card P
  · change ∀g∈normalizer ((S:Subgroup G):Set G),g^2∈Subgroup.centralizer ((S:Subgroup G):Set G)
    rw [hS]
    exact h.normalizer_squares_of_cubic_collapse P hc hsquares

include h in
theorem reflected_kernel_card_eighty_one (P : Sylow 3 (centralizer z))
    (m : CubicNormalizer.ReflectedMarking z
      ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hsquares : ∀g∈normalizer (((P:Subgroup (centralizer z)).map
      (centralizer z).subtype):Set G)⊓centralizer z,
      g^2∈Subgroup.centralizer (((P:Subgroup (centralizer z)).map
        (centralizer z).subtype):Set G))
    (M : Subgroup G) (f : M→*alternatingGroup (Fin 6)) (hf : Function.Surjective f) :
    let V := CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    IsElementaryAbelian 3 V ∧ Nat.card V=81 := by
  obtain ⟨he,hc⟩ := h.reflected_kernel P m
  exact ⟨he,hc.resolve_left (h.cubic_oddKernel_ne_of_A6_section P hsquares M f hf)⟩
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
