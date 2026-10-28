module

public import Stellmacher.SectionNine.NineThreeFinalCentralizerSetup
public import Stellmacher.SectionNine.NineThreeRankData

/-!
# Actual core-intersection invariance in the rank-three case of (9.3)

The mixed centralizer and the initial stabilizer normalize the intersection
of the initial center with the centralizer's two-core. The core commutator
with the initial center lies in that intersection. A Sylow of the original
ambient group lies in both normalizers, using the prescribed conjugator
and original embedding. When the intersection has order eight, its index
in the order-sixteen center and the latter's image in the core quotient
both have order two.

These are preparatory action inputs, not the missing odd-layer commutator
containment. In particular neither normalizer containment nor an order-two
quotient image alone establishes that the odd layer preserves that image.
Source: Stellmacher (9.3), printed p.50/PDF p.40 of
`refs/files/stellmacher-n-group.pdf`, the full final R0,C0 paragraph.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem core_intersection_normalizer_and_commutator
    {H : Type*} [Group H] (centralizer localGroup vectors : Subgroup H)
    (hlocal : localGroup ≤ Subgroup.normalizer (vectors : Set H))
    (hvectors : vectors ≤ centralizer)
    (hcore : (pCore 2 centralizer).map centralizer.subtype ≤ localGroup) :
    let core := (pCore 2 centralizer).map centralizer.subtype
    (centralizer ⊓ localGroup : Subgroup H) ≤
        Subgroup.normalizer (vectors ⊓ core : Set H) ∧
      ⁅core, vectors⁆ ≤ vectors ⊓ core := by
  let core := (pCore 2 centralizer).map centralizer.subtype
  have hnormal : centralizer ≤ Subgroup.normalizer (core : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      (SevenSix.twoCoreIn_normal centralizer)
  refine ⟨(le_inf (inf_le_right.trans hlocal) (inf_le_left.trans hnormal)).trans
    Subgroup.inf_normalizer_le_normalizer_inf, ?_⟩
  exact le_inf
    (Subgroup.le_normalizer_iff_commutator_le_right.mp (hcore.trans hlocal))
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hvectors.trans hnormal))

public theorem intersection_relIndex_two_of_card_sixteen_eight
    {H : Type*} [Group H] [Finite H] (vectors core : Subgroup H)
    (hvectors : Nat.card vectors = 16)
    (hintersection : Nat.card (vectors ⊓ core : Subgroup H) = 8) :
    (vectors ⊓ core : Subgroup H).relIndex vectors = 2 := by
  have hcard := ((vectors ⊓ core : Subgroup H).subgroupOf vectors).card_mul_index
  have hle : vectors ⊓ core ≤ vectors := inf_le_left
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    hintersection, hvectors] at hcard
  change 8 * (vectors ⊓ core : Subgroup H).relIndex vectors = 16 at hcard
  omega

public theorem quotient_image_card_two_of_core_intersection_card_eight
    {H : Type*} [Group H] [Finite H] (centralizer vectors : Subgroup H)
    (hle : vectors ≤ centralizer) (hcard : Nat.card vectors = 16)
    (hintersection : Nat.card
      (vectors ⊓ (pCore 2 centralizer).map centralizer.subtype : Subgroup H) = 8) :
    Nat.card ((vectors.subgroupOf centralizer).map
      (QuotientGroup.mk' (pCore 2 centralizer))) = 2 := by
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  rw [← Subgroup.relIndex_map_map_of_injective (pCore 2 centralizer)
    (vectors.subgroupOf centralizer) centralizer.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hle]
  rw [← Subgroup.inf_relIndex_left]
  exact intersection_relIndex_two_of_card_sixteen_eight vectors _ hcard hintersection

public theorem nine_three_final_core_intersection_normalizer_and_commutator
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
    let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
    (centralizer ⊓ (GAt ctx.Γ ctx.criticalPath.a).map embedding : Subgroup H) ≤
        Subgroup.normalizer (vectors ⊓ core : Set H) ∧
      ⁅core, vectors⁆ ≤ vectors ⊓ core := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
  have hlocal : (GAt ctx.Γ ctx.criticalPath.a).map embedding ≤
      Subgroup.normalizer (vectors : Set H) := by
    rintro element ⟨actor, hactor, rfl⟩
    exact Subgroup.le_normalizer_map embedding (Subgroup.mem_map_of_mem embedding
      (stabilizer_le_normalizer_z_public ctx.Γ ctx.criticalPath.a hactor))
  exact core_intersection_normalizer_and_commutator centralizer
    ((GAt ctx.Γ ctx.criticalPath.a).map embedding) vectors hlocal
    (nine_three_final_centralizer_center_core ctx hb hlarge first second config).1
    (nine_three_final_centralizer_setup_of_mixed_sylow ctx first second config hgeometry).2.2

public theorem nine_three_final_core_intersection_sylow_normalized
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
    let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
    ∃ sylow : Sylow 2 H,
      (sylow : Subgroup H) ≤ centralizer ⊓ (GAt ctx.Γ ctx.criticalPath.a).map embedding ∧
      (sylow : Subgroup H) ≤ Subgroup.normalizer (vectors ⊓ core : Set H) := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  have hnormalizer := (nine_three_final_core_intersection_normalizer_and_commutator
    ctx hb hlarge first second config hgeometry).1
  obtain ⟨_, conjugator, hconjugator, hcentral⟩ := hgeometry
  let sylow : Sylow 2 H := embedding conjugator • S0
  have hmap : (T.map (MulAut.conj conjugator).toMonoidHom).map embedding =
      (sylow : Subgroup H) := by
    change (T.map (MulAut.conj conjugator).toMonoidHom).map embedding =
      (S0 : Subgroup H).map (MulAut.conj (embedding conjugator)).toMonoidHom
    rw [← (nine_two_ambient_setup ctx).1, ← ctx.map_S,
      Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext element
    simp [MulAut.conj_apply]
  have hcentralizer : (sylow : Subgroup H) ≤ centralizer := by
    have hcomm := congrArg (Subgroup.map embedding)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral)
    rw [Subgroup.map_commutator, Subgroup.map_bot, hmap] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hlocal : (sylow : Subgroup H) ≤
      (GAt ctx.Γ ctx.criticalPath.a).map embedding := by
    rw [← hmap]
    apply Subgroup.map_mono
    rintro element ⟨member, hmember, rfl⟩
    have hstart := (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
    exact (GAt ctx.Γ ctx.criticalPath.a).mul_mem
      ((GAt ctx.Γ ctx.criticalPath.a).mul_mem hconjugator (hstart hmember))
      ((GAt ctx.Γ ctx.criticalPath.a).inv_mem hconjugator)
  exact ⟨sylow, le_inf hcentralizer hlocal,
    (le_inf hcentralizer hlocal).trans hnormalizer⟩

end Stellmacher.SectionNine
