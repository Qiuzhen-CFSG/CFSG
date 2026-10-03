module
public import Stellmacher.SectionTen.TenOneSmallCoreIndex
public import Stellmacher.SectionTen.TenOneSmallNeighborhoodCard
public import Stellmacher.SectionTen.GeneratedTenOneReduction

/-!
# The common conclusions in the small branch of Stellmacher (10.1)

Under the genuine source case that the first neighbor module has order eight
and its local core quotient is SL₂(2), the actual subgroups satisfy
|W₀/W|=2, |Wnext/W|=8, and Wnext'=Vfirst∩Vend. The ambient theorem preserves
the original three subgroup parameters and their defining equalities. The
legacy wrapper uses the identity-embedding context adapter.

The small derived theorem identifies W and the common intersection with the
middle center of order four. The three-neighbor cardinality theorem gives
|Wnext|=32, and the three-core parity theorem gives |Wnext/W₀|=4. These exact
orders yield the first quotient order; the other quotient and the derived
equality are the proved geometric conclusions. No alternative or common
conclusion record is assumed. The remaining local structures and the
nonsolvable-centralizer alternative of (10.1)(a) are separate tasks.

Source: Stellmacher, Journal of Algebra 190 (1997), (10.1), printed pp.59–60,
case (6), `refs/files/stellmacher-n-group.pdf`. These are precisely the
`index_conclusions` and `derived_intersection` fields of the ambient (10.1)
conclusion interface in the small case.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_common_conclusions
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex) (W W0 Wnext : Subgroup G)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hW : W = conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle))
    (hWnext : Wnext = GeneratedNeighborhoodV ctx.Γ middle)
    (hW0 : W0 = NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    (QuotientCardEq W0 W 2 ∧ QuotientCardEq Wnext W (2 ^ 3)) ∧
      DerivedAmbient Wnext =
        VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  have hnextCard : Nat.card Wnext = 32 := hWnext ▸
    ten_one_small_neighborhood_card ctx middle hpath hsmall
  have hzeroIndex : QuotientCardEq Wnext W0 4 := by
    rw [hW0, hWnext]
    exact ten_one_small_neighborhood_core_index ctx middle hpath hsmall hmodel
  have hWcenter : W = ZAt ctx.Γ middle :=
    hW.trans (ten_one_small_generated_eq_center ctx middle hpath hsmall)
  have hWcard : Nat.card W = 4 := hWcenter ▸
    (sectionTenOpeningData ctx middle hpath).center_card
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change Nat.card W0 = 2 * Nat.card W
    change Nat.card Wnext = 4 * Nat.card W0 at hzeroIndex
    rw [hWcard]
    omega
  · rw [hWnext, hW]
    exact ten_one_small_neighborhood_quotient ctx middle hpath hsmall
  · rw [hWnext]
    exact ten_one_small_derived ctx middle hpath hsmall

public theorem ten_one_small_common_conclusions_legacy
    (ctx : SectionTenContext H S0 S P1 P2)
    (middle : ctx.Γ.Vertex) (W W0 Wnext : Subgroup H)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hW : W = conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle))
    (hWnext : Wnext = GeneratedNeighborhoodV ctx.Γ middle)
    (hW0 : W0 = NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    (QuotientCardEq W0 W 2 ∧ QuotientCardEq Wnext W (2 ^ 3)) ∧
      DerivedAmbient Wnext =
        VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' :=
  ten_one_small_common_conclusions ctx.toAmbientContext middle W W0 Wnext
    hpath hW hWnext hW0 hsmall hmodel

end Stellmacher.SectionTen
