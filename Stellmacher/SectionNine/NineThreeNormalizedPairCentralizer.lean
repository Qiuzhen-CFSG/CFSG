module

public import Stellmacher.SectionNine.NineThreeNormalizedGeometry
public import Stellmacher.SectionNine.NineThreePairCenterCommutator
public import Stellmacher.SectionNine.NineThreeFirstResidualOddCoreExclusion

/-!
# The actual normalized extraction pair lies in its ambient mixed centralizer

Transport the four-center commutator relation through the normalization
actor and then through the original embedding. The mixed commutator lies
in the initial center, and both unchanged extracted groups lie in the
ambient centralizer of its image. This supplies the precise overgroup
premise of `nine_three_first_residual_not_le_odd_core_layer` for the final
centralizer used in (9.3). No characteristic-two property of that
centralizer is assumed or concluded here.

Source: Stellmacher (9.3), printed p.50/PDF p.40 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

/-- Normalize and embed the mixed-commutator containment and pair centralization. -/
public theorem nine_three_normalized_pair_centralizer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,
      ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    mixed ≤ ZAt ctx.Γ ctx.criticalPath.a ∧
      (first.E.map (MulAut.conj config.g⁻¹).toMonoidHom).map embedding ⊔
        (second.E.map (MulAut.conj config.g⁻¹).toMonoidHom).map embedding ≤
          Subgroup.centralizer (mixed.map embedding : Set H) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let conjugation := MulAut.conj config.g⁻¹
  let oldFirst := Γ.act first.extraction.x⁻¹ first.l
  let oldSecond := Γ.act second.extraction.x⁻¹ second.l
  let newFirst := Γ.act config.g oldFirst
  let oldMixed := (⁅ZAt Γ oldSecond ⊓ GAt Γ oldFirst,
    ZAt Γ oldFirst ⊓ GAt Γ oldSecond⁆ : Subgroup G)
  let mixed := (⁅ZAt Γ cp.a ⊓ GAt Γ newFirst,
    ZAt Γ newFirst ⊓ GAt Γ cp.a⁆ : Subgroup G)
  change mixed ≤ ZAt Γ cp.a ∧ _
  have hsecondCenter : (ZAt Γ oldSecond).map conjugation.toMonoidHom =
      ZAt Γ cp.a := by
    change (z Γ oldSecond).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act, config.maps_new_vertex]
  have hsecondGroup : (GAt Γ oldSecond).map conjugation.toMonoidHom =
      GAt Γ cp.a := by
    change conjugateBy (stabilizer Γ oldSecond) config.g⁻¹ = _
    rw [← stabilizer_act, config.maps_new_vertex]
  have hfirstCenter : (ZAt Γ oldFirst).map conjugation.toMonoidHom =
      ZAt Γ newFirst := by
    change (z Γ oldFirst).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act]
  have hfirstGroup : (GAt Γ oldFirst).map conjugation.toMonoidHom =
      GAt Γ newFirst := by
    change conjugateBy (stabilizer Γ oldFirst) config.g⁻¹ = _
    rw [← stabilizer_act]
  have hmixed : oldMixed.map conjugation.toMonoidHom = mixed := by
    change (⁅ZAt Γ oldSecond ⊓ GAt Γ oldFirst,
      ZAt Γ oldFirst ⊓ GAt Γ oldSecond⁆ : Subgroup G).map _ = _
    rw [Subgroup.map_commutator, Subgroup.map_inf _ _ _ conjugation.injective,
      Subgroup.map_inf _ _ _ conjugation.injective,
      hsecondCenter, hsecondGroup, hfirstCenter, hfirstGroup]
  have hpair := nine_three_pair_center_commutator ctx hb hlarge first second
  constructor
  · rw [← hmixed, ← hsecondCenter]
    exact Subgroup.map_mono
      (hpair.1.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  · have hcomm := congrArg (Subgroup.map conjugation.toMonoidHom)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hpair.2)
    rw [Subgroup.map_commutator, Subgroup.map_sup, Subgroup.map_bot, hmixed] at hcomm
    have hambient := congrArg (Subgroup.map embedding) hcomm
    rw [Subgroup.map_commutator, Subgroup.map_sup, Subgroup.map_bot] at hambient
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hambient

/-- The first residual cannot lie in the odd-core layer of the actual mixed centralizer. -/
public theorem nine_three_mixed_centralizer_residual_not_le
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,
      ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    ¬ (((twoResidualAmbient (first.E.map (MulAut.conj config.g⁻¹).toMonoidHom)).map
      embedding).subgroupOf centralizer).map (QuotientGroup.mk' (pCore 2 centralizer)) ≤
        pPrimeCore 2 (centralizer ⧸ pCore 2 centralizer) := by
  exact nine_three_first_residual_not_le_odd_core_layer ctx hb first second config _
    (nine_three_normalized_pair_centralizer ctx hb hlarge first second config).2

end Stellmacher.SectionNine
