module
public import Stellmacher.SectionNine.LemmaNineTen

/-!
# The residual-core edge equality in the excluded distance-five case

This records the exact equality in Stellmacher (9.10)(10), printed p.58,
for the original critical path and the literal vertices at offsets two
and three. The first residual core is O₂(Efirst); the supplied terminal
classification packet is retained.

The final ambient theorem (9.10), proved by an independent residual
displacement argument, excludes length five. Thus the stated equality
follows from that impossibility. This corollary is downstream of (9.10)
and is not used in its proof; in particular, noncentral action of a normal
subgroup of the Sylow group is never substituted for full edge generation.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_residual_core_second_edge_generation
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 5)
    (_hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (_hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (_hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3) :
    let second := ctx.criticalPath.path ⟨2,by omega⟩
    let third := ctx.criticalPath.path ⟨3,by omega⟩
    (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ⊓ QAt ctx.Γ second) ⊔
      QAt ctx.Γ third = GAt ctx.Γ second ⊓ GAt ctx.Γ third := by
  have hbound := lemma_nine_ten_ambient ctx
  omega

end Stellmacher.SectionNine
