module

public import Stellmacher.SectionNine.NineThreeNormalizedPairCentralizer
public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Stellmacher.SectionFiveToSeven.CentralizerCharacteristicTwoSylow

/-!
# Ambient setup for the final mixed centralizer in (9.3)

Transport a centralized conjugate of the graph Sylow through the original
embedding. The ambient Sylow equality from (9.2) permits Hypothesis One to
apply to the normalizer of the nontrivial mixed two-subgroup. Its normal
centralizer is consequently solvable and of characteristic two. The normal
two-core lies in the supplied Sylow and hence in the initial stabilizer.

These are conditional setup lemmas, not the final residual containment.
The order-two and centralized-Sylow hypotheses must still be established
from the actual mixed commutator and its canonical rank-two action.
Independently of those two hypotheses, the mixed subgroup lies in the
central two-core, the initial center lies in the centralizer, and the
prescribed first actor excludes that initial center from the two-core.

Source: Stellmacher (9.3), printed p.50/PDF p.40 of
`refs/files/stellmacher-n-group.pdf`, the final R₀,C₀ paragraph.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem nine_three_embedded_centralizer_of_centralized_sylow
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (mixed : Subgroup G) (hne : mixed ≠ ⊥) (hp : IsPGroup 2 mixed)
    (conjugator : G)
    (hcentral : T.map (MulAut.conj conjugator).toMonoidHom ≤
      Subgroup.centralizer (mixed : Set G)) :
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    Group.IsSolvable centralizer ∧ IsCharacteristicTwoType centralizer ∧
      (pCore 2 centralizer).map centralizer.subtype ≤
        (T.map (MulAut.conj conjugator).toMonoidHom).map embedding := by
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
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
  have hsylow : (sylow : Subgroup H) ≤ centralizer := by
    have hcomm := congrArg (Subgroup.map embedding)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral)
    rw [Subgroup.map_commutator, Subgroup.map_bot, hmap] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hneImage : mixed.map embedding ≠ ⊥ := by
    intro hbot
    apply hne
    exact Subgroup.map_injective ctx.embedding_injective (by simpa using hbot)
  obtain ⟨hsolvable, hcharacteristic⟩ :=
    centralizer_characteristicTwo_of_contains_sylow ctx.hypothesisTwo.hyp1
      (mixed.map embedding) hneImage (hp.map embedding) sylow hsylow
  refine ⟨hsolvable, hcharacteristic, ?_⟩
  rw [hmap]
  have hcore := (pCore_isPGroup (p := 2) (G := centralizer)).le_sylow_of_normal
    (sylow.subtype hsylow)
  rintro element ⟨member, hmember, rfl⟩
  exact hcore hmember

public theorem nine_three_final_centralizer_setup_of_mixed_sylow
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
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
    Group.IsSolvable centralizer ∧ IsCharacteristicTwoType centralizer ∧
      (pCore 2 centralizer).map centralizer.subtype ≤
        (GAt ctx.Γ ctx.criticalPath.a).map embedding := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  obtain ⟨hcard, conjugator, hconjugator, hcentral⟩ := hgeometry
  have hne : mixed ≠ ⊥ := by
    intro hbot
    change Nat.card mixed = 2 at hcard
    rw [hbot, Subgroup.card_bot] at hcard
    contradiction
  have hp : IsPGroup 2 mixed := IsPGroup.of_card (n := 1) (by simpa using hcard)
  obtain ⟨hsolvable, hcharacteristic, hcore⟩ :=
    nine_three_embedded_centralizer_of_centralized_sylow ctx mixed hne hp
      conjugator hcentral
  refine ⟨hsolvable, hcharacteristic, hcore.trans (Subgroup.map_mono ?_)⟩
  rintro element ⟨member, hmember, rfl⟩
  have hstart := (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  exact (GAt ctx.Γ ctx.criticalPath.a).mul_mem
    ((GAt ctx.Γ ctx.criticalPath.a).mul_mem hconjugator (hstart hmember))
    ((GAt ctx.Γ ctx.criticalPath.a).inv_mem hconjugator)

public theorem nine_three_final_centralizer_center_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    (ZAt ctx.Γ ctx.criticalPath.a).map embedding ≤ centralizer ∧
      (mixed.map embedding).subgroupOf centralizer ≤
        Subgroup.center centralizer ⊓ pCore 2 centralizer := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  have hneighbor : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  have hle : mixed ≤ ZAt ctx.Γ ctx.criticalPath.a :=
    (nine_three_normalized_pair_centralizer ctx hb hlarge first second config).1
  have hcentral : (ZAt ctx.Γ ctx.criticalPath.a).map embedding ≤ centralizer := by
    rintro element ⟨member, hmember, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro vector ⟨preimage, hpreimage, rfl⟩
    simpa only [map_mul] using congrArg embedding
      (setLike_mul_comm (s := z ctx.Γ ctx.criticalPath.a) (hle hpreimage) hmember)
  have hmixedCentralizer : mixed.map embedding ≤ centralizer :=
    (Subgroup.map_mono hle).trans hcentral
  have hcenter : (mixed.map embedding).subgroupOf centralizer ≤
      Subgroup.center centralizer := by
    intro member hmember
    rw [Subgroup.mem_center_iff]
    intro actor
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp actor.property member hmember).symm
  have hnormal : ((mixed.map embedding).subgroupOf centralizer).Normal := by
    constructor
    intro member hmember actor
    have hcomm := Subgroup.mem_center_iff.mp (hcenter hmember) actor
    simpa only [← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one] using hmember
  have hp := ((IsElementaryAbelian.isPGroup 2 (z ctx.Γ ctx.criticalPath.a)).to_le
    hle).map embedding
  have hpRestricted : IsPGroup 2 ((mixed.map embedding).subgroupOf centralizer) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hmixedCentralizer).symm
  exact ⟨hcentral, le_inf hcenter (le_sSup ⟨hnormal, hpRestricted⟩)⟩

public theorem nine_three_initial_center_not_le_final_centralizer_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    ¬ (ZAt ctx.Γ ctx.criticalPath.a).map embedding ≤
      (pCore 2 centralizer).map centralizer.subtype := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  let core := (pCore 2 centralizer).map centralizer.subtype
  let extracted := first.E.map (MulAut.conj config.g⁻¹).toMonoidHom
  have hextracted : extracted.map embedding ≤ centralizer := le_sup_left.trans
    (nine_three_normalized_pair_centralizer ctx hb hlarge first second config).2
  have hnormal : centralizer ≤ Subgroup.normalizer (core : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      (SevenSix.twoCoreIn_normal centralizer)
  change ¬ (ZAt ctx.Γ ctx.criticalPath.a).map embedding ≤ core
  intro hle
  have hcomm : ⁅(ZAt ctx.Γ ctx.criticalPath.a).map embedding,
      extracted.map embedding⁆ ≤ core :=
    (Subgroup.commutator_mono hle le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hextracted.trans hnormal))
  have hpImage : IsPGroup 2 ((⁅ZAt ctx.Γ ctx.criticalPath.a, extracted⁆ : Subgroup G).map
      embedding) := by
    rw [Subgroup.map_commutator]
    exact ((pCore_isPGroup (p := 2) (G := centralizer)).map centralizer.subtype).to_le
      hcomm
  have hp : IsPGroup 2 (⁅ZAt ctx.Γ ctx.criticalPath.a, extracted⁆ : Subgroup G) :=
    hpImage.of_equiv ((⁅ZAt ctx.Γ ctx.criticalPath.a, extracted⁆ : Subgroup G).equivMapOfInjective
      embedding ctx.embedding_injective).symm
  have hmodule := ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
    ctx.commutator_eq).longer_case hb).1.isPGroup
  exact geometric_actor_commutator_not_two ctx.Γ (ctx.Γ.act config.g ctx.criticalPath.a')
    (ctx.Γ.act config.g first.l) (VAt ctx.Γ ctx.criticalPath.firstStep) extracted
    (first.A0.map (MulAut.conj config.g⁻¹).toMonoidHom) config.first_actor
    config.first_geometry hmodule (ZAt ctx.Γ ctx.criticalPath.a)
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1
    config.first_actor_initial hp

end Stellmacher.SectionNine
