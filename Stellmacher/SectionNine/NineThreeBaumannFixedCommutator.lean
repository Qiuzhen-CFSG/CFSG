module
public import Stellmacher.SectionNine.NineThreeCommonCentralizedTwoSubgroup
public import Stellmacher.SectionNine.NineThreePairCenterCommutator

/-!
# The mixed commutator has no Baumann fixed vectors

For the actual normalized pair from (9.3), the mixed center commutator has
trivial intersection with the centralizer of the Baumann subgroup. The pair
center theorem puts the commutator inside the elementary initial center and
shows that both extracted groups centralize it. Its intersection with the
Baumann centralizer therefore satisfies the common-centralized-two-subgroup
vanishing theorem. This strengthens the earlier intersection with the center
of the Baumann subgroup and provides fixed-space exclusion without identifying
native and canonical offenders.

Source: the common-centralizer argument in Stellmacher (9.3), Journal of
Algebra 190 (1997), pp.49–50, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_normalized_baumann_fixed_commutator_bot
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
    (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,
      ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) ⊓
      Subgroup.centralizer (baumannIn T : Set G) = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hbLocal : 1 < cp.length := hb
  let c := MulAut.conj config.g⁻¹
  let m0 := Γ.act first.extraction.x⁻¹ first.l
  let n0 := Γ.act second.extraction.x⁻¹ second.l
  let m := Γ.act config.g m0
  let d := Γ.act config.g cp.a'
  let r := Γ.act config.g second.l
  let V := VAt Γ cp.firstStep
  let E1 := first.E.map c.toMonoidHom
  let E2 := second.E.map c.toMonoidHom
  let R0 := (⁅ZAt Γ cp.a ⊓ GAt Γ m,ZAt Γ m ⊓ GAt Γ cp.a⁆ : Subgroup G)
  let R1 := R0 ⊓ Subgroup.centralizer (baumannIn T : Set G)
  let Rold := (⁅ZAt Γ n0 ⊓ GAt Γ m0,ZAt Γ m0 ⊓ GAt Γ n0⁆ : Subgroup G)
  change R1 = ⊥
  have hZnmap : (ZAt Γ n0).map c.toMonoidHom = ZAt Γ cp.a := by
    change (z Γ n0).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act,config.maps_new_vertex]
  have hGnmap : (GAt Γ n0).map c.toMonoidHom = GAt Γ cp.a := by
    change conjugateBy (stabilizer Γ n0) config.g⁻¹ = _
    rw [← stabilizer_act,config.maps_new_vertex]
  have hZmmap : (ZAt Γ m0).map c.toMonoidHom = ZAt Γ m := by
    change (z Γ m0).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act]
  have hGmmap : (GAt Γ m0).map c.toMonoidHom = GAt Γ m := by
    change conjugateBy (stabilizer Γ m0) config.g⁻¹ = _
    rw [← stabilizer_act]
  have hRmap : Rold.map c.toMonoidHom = R0 := by
    rw [show Rold = ⁅ZAt Γ n0 ⊓ GAt Γ m0,ZAt Γ m0 ⊓ GAt Γ n0⁆ from rfl,
      Subgroup.map_commutator,Subgroup.map_inf _ _ _ c.injective,
      Subgroup.map_inf _ _ _ c.injective,hZnmap,hGnmap,hZmmap,hGmmap]
  have hpair := nine_three_pair_center_commutator ctx hb hlarge first second
  have hRoldZn : Rold ≤ ZAt Γ n0 :=
    hpair.1.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hR0Za : R0 ≤ ZAt Γ cp.a := by
    rw [← hRmap,← hZnmap]
    exact Subgroup.map_mono hRoldZn
  have hEpair : E1 ⊔ E2 ≤ Subgroup.centralizer (R1 : Set G) := by
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hpair.2
    have hm := congrArg (Subgroup.map c.toMonoidHom) hc
    rw [Subgroup.map_commutator,Subgroup.map_sup,Subgroup.map_bot,hRmap] at hm
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hm).trans
      (Subgroup.centralizer_le inf_le_left)
  have hZaV : ZAt Γ cp.a ≤ V := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hVp : IsPGroup 2 V :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1.isPGroup
  have hR1p : IsPGroup 2 R1 := hVp.to_le (inf_le_left.trans (hR0Za.trans hZaV))
  exact nine_three_normalized_common_two_subgroup_bot ctx hb first second config R1 hR1p
    inf_le_right hEpair

end Stellmacher.SectionNine

