module
public import Stellmacher.SectionTen.TenOneSmallOrder32Normalizer
public import Stellmacher.SectionTen.TenOneSmallOrder64Normalizer

/-!
# The small middle-center normalizer

In the order-eight first-module case with first quotient SL₂(2), the
ambient normalizer of the mapped middle center is precisely the mapped
middle stabilizer. This is the uniform assertion for the original ambient
context and embedding.

The established core-cardinality dichotomy gives order32 or order64.
The two proved normalizer branches respectively use the Frattini-eight
action bound and the characteristic elementary-four quotient action.
Applying the appropriate branch proves the common conclusion.

Source: Stellmacher (10.1)(a3), printed p.61, assertion (7),
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- The ambient middle-center normalizer in the small branch of (10.1). -/
public theorem ten_one_small_center_normalizer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    Subgroup.normalizer ((ZAt ctx.Γ middle).map embedding : Set H) =
      (GAt ctx.Γ middle).map embedding := by
  rcases ten_one_small_middle_core_card_cases ctx middle hpath hsmall hmodel with h32 | h64
  · exact ten_one_small_order32_center_normalizer ctx middle hpath hsmall hmodel h32.2
  · exact ten_one_small_order64_center_normalizer ctx middle hpath hsmall hmodel h64.2

end Stellmacher.SectionTen