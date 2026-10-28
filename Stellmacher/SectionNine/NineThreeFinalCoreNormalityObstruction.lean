module

public import Stellmacher.SectionNine.NineThreeFinalCoreHyperplaneSetup
public import Theory.GroupTheory.PGroup.CharacteristicTwoNormalClosure

/-!
# The actual mixed-core intersection cannot be assumed normal

An elementary two-subgroup whose commutator with the two-core lies in
their normal intersection is contained in the core of a characteristic-two
group. The intersection centralizes the elementary subgroup, so the proved
two-step normal-closure theorem applies.

In the original Section Nine configuration, the actual initial center is
not contained in the actual mixed centralizer's core. Consequently its
intersection with that core is not normal in the full mixed centralizer.
Only its previously proved Sylow and local-normalizer invariance may be used.
This obstruction does not prove the outstanding order-eight odd-layer
containment and does not invoke the opposite odd-layer containment theorem.

Source: Stellmacher (9.3), printed p.50/PDF p.40 of
`refs/files/stellmacher-n-group.pdf`, final R0,C0 paragraph. This module
audits the normality requirements of a possible normal-closure proof route.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem elementary_le_core_of_normal_core_intersection
    {K : Type*} [Group K] [Finite K]
    (vectors : Subgroup K) [IsElementaryAbelian 2 vectors]
    (hcharacteristic : Subgroup.centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcommutator : ⁅pCore 2 K, vectors⁆ ≤ vectors ⊓ pCore 2 K)
    (hnormal : (vectors ⊓ pCore 2 K : Subgroup K).Normal) :
    vectors ≤ pCore 2 K := by
  have hcentral : ⁅vectors ⊓ pCore 2 K, vectors⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro vector hvector
    rw [Subgroup.mem_centralizer_iff]
    intro other hother
    exact setLike_mul_comm (s := vectors) hother hvector.1
  have hp := normalClosure_isPGroup_of_characteristicTwo
    (vectors ⊓ pCore 2 K) vectors hcharacteristic hnormal
    hcommutator hcentral inferInstance
  exact Subgroup.le_normalClosure.trans (le_sSup ⟨inferInstance, hp⟩)

public theorem nine_three_final_core_intersection_not_normal
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hgeometry :
      let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
      let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
        ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
      Nat.card mixed = 2 ∧ ∃ conjugator : G,
        conjugator ∈ GAt ctx.Γ ctx.criticalPath.a ∧
        T.map (MulAut.conj conjugator).toMonoidHom ≤
          Subgroup.centralizer (mixed : Set G)) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    let core := (pCore 2 centralizer).map centralizer.subtype
    ¬ (((ZAt ctx.Γ ctx.criticalPath.a).map embedding ⊓ core).subgroupOf
      centralizer).Normal := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  let core := (pCore 2 centralizer).map centralizer.subtype
  let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
  let internal := vectors.subgroupOf centralizer
  have hvectors : vectors ≤ centralizer :=
    (nine_three_final_centralizer_center_core ctx hb hlarge first second config).1
  have hmap : internal.map centralizer.subtype = vectors :=
    Subgroup.map_subgroupOf_eq_of_le hvectors
  have hintersection : internal ⊓ pCore 2 centralizer =
      (vectors ⊓ core).subgroupOf centralizer := by
    apply Subgroup.map_injective centralizer.subtype_injective
    rw [Subgroup.map_inf _ _ _ centralizer.subtype_injective, hmap,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hvectors)]
  have hcommutator : ⁅pCore 2 centralizer, internal⁆ ≤
      internal ⊓ pCore 2 centralizer := by
    apply (Subgroup.map_le_map_iff_of_injective centralizer.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_inf _ _ _ centralizer.subtype_injective,
      hmap]
    exact (nine_three_final_core_intersection_normalizer_and_commutator
      ctx hb hlarge first second config hgeometry).2
  have hneighbor : ctx.criticalPath.firstStep ∈
      neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  let _ : IsElementaryAbelian 2 vectors := IsElementaryAbelian.map embedding
  let _ : IsElementaryAbelian 2 internal := IsElementaryAbelian.subgroupOf hvectors
  change ¬ ((vectors ⊓ core).subgroupOf centralizer).Normal
  intro hnormal
  have hnormalInternal : (internal ⊓ pCore 2 centralizer : Subgroup centralizer).Normal :=
    hintersection.symm ▸ hnormal
  have hle := elementary_le_core_of_normal_core_intersection internal
    (nine_three_final_centralizer_setup_of_mixed_sylow
      ctx first second config hgeometry).2.1 hcommutator hnormalInternal
  have hleMap := Subgroup.map_mono (f := centralizer.subtype) hle
  rw [hmap] at hleMap
  exact nine_three_initial_center_not_le_final_centralizer_core
    ctx hb hlarge first second config hleMap

end Stellmacher.SectionNine
