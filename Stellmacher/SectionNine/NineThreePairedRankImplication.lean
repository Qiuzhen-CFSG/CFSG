module
public import Stellmacher.SectionNine.NineThreePairedRankReduction
public import Stellmacher.SectionNine.NineThreeSourceMixedNontrivial

/-!
# The paired rank contradiction for native Thompson action

Under native Thompson centralization, the maximal-elementary argument and
Baumann-fixed commutator vanishing make the join of the actual normalized
center hyperplanes elementary abelian. Thus the restricted mixed commutator
vanishes. The independent paired-module theorem proves that this commutator
cannot vanish: the extracted modules and canonical rank-two action would
produce a Sylow-fixed displacement line in two disjoint factor supports.

Mixed nontriviality is proved by the imported theorem, not assumed as an
input. That theorem does not require native action, native/barred equality,
barred exclusion or generation, involution-plane transitivity, or final (9.3).
This supplies exactly False under the contrary native-centralization
hypothesis, without any additional rank or replacement assumption.

Source: Stellmacher (9.3), printed pp.49–50/PDF pp.39–40,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_paired_rank_implication
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hJ : elementaryAbelianMaxJ T ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)) : False := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let left := ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex
  let right := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
  let : IsElementaryAbelian 2 (left ⊔ right : Subgroup G) :=
    (nine_three_paired_join_strict_rank_deficit ctx hb hlarge first second config hJ).1
  have hcentral : (left ⊔ right : Subgroup G) ≤
      Subgroup.centralizer ((left ⊔ right : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hzero : ⁅left, right⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((le_sup_left.trans hcentral).trans
        (Subgroup.centralizer_le (show right ≤ left ⊔ right from le_sup_right)))
  exact nine_three_source_mixed_nontrivial ctx hb hlarge first second config hzero

end Stellmacher.SectionNine
