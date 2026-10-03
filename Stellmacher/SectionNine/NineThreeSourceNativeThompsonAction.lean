module
public import Stellmacher.SectionNine.NineThreePairedRankImplication

/-!
# The native Thompson action in (9.3)

The contrary native-centralization branch makes the actual normalized paired
commutator trivial by the paired rank argument, while the independent source
mixed-nontriviality theorem rules this out.

Source: Stellmacher (9.3), printed p.50/PDF p.40,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_source_native_thompson_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    ¬ elementaryAbelianMaxJ T ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G) := by
  intro hJ
  exact nine_three_paired_rank_implication ctx hb hlarge first second config hJ

end Stellmacher.SectionNine
