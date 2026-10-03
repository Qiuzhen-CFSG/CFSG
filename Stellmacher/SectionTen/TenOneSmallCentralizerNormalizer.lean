module
public import Stellmacher.SectionTen.TenOneSmallMixedClosureCenter
public import Stellmacher.SectionTen.TenOneSmallNormalizerTransfer

/-!
# The ambient Wstar normalizer in the small case

For the actual small first-module context of Stellmacher (10.1), the
ambient normalizer of the mapped middle-core centralizer Wstar is exactly
the mapped middle stabilizer. The original embedding, critical path and
first-step quotient model are retained, with no extra cardinality branch
or closure hypothesis.

The native quadratic-closure theorem places the terminal-center closure
under the lower mixed core and terminal edge in the middle plane. The
normalizer-transfer theorem then uses the plane's irreducibility, the
proved center-normalizer identity, lower mixed-core transfer and the exact
middle-core Frattini identity to give the required equality.

Source: Stellmacher (10.1)(a3), printed pp.61–62, assertion (9),
`refs/files/stellmacher-n-group.pdf`. This is the thin assembly of the
actual ambient closure and normalizer arguments.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_centralizer_normalizer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    Subgroup.normalizer (Wstar.map embedding : Set H) =
      (GAt ctx.Γ middle).map embedding := by
  exact ten_one_small_centralizer_normalizer_of_mixed_closure_le_center
    ctx middle hpath hsmall hmodel
      (ten_one_small_mixed_closure_le_center ctx middle hpath hsmall hmodel)

end Stellmacher.SectionTen

