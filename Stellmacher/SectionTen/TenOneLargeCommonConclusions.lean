module
public import Stellmacher.SectionTen.TenOneLargeCoreIndex

/-!
# The common index chain in the large branch of Stellmacher (10.1)

The source-(12), (14), (15), and (19) case data imply the exact common
quotient orders W₀/W=2, Wnext/W=8, Wnext/W₀=4 and the derived-intersection
equality. W, W₀ and Wnext are the supplied ambient subgroups with their
literal geometric definitions. These common conclusions can therefore feed
the final (10.1) record directly.

The large neighborhood quotient theorem proves Wnext/W has order eight
from the first residual-core intersection index, intersection order, and
absence of quotient transvections. The Frobenius20 neighbor-core calculation
and three-kernel parity give Wnext/W₀ order four. Their cardinal equations
give W₀/W order two. The large derived theorem identifies Wnext' with the
endpoint-module intersection. Each constituent conclusion is proved by its
geometric producer, rather than included among this assembly's assumptions.

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed pp.63–65,
source (12), (14), (15), (19), and the ensuing common quotient calculation in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_common_index_chain
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (W W0 Wnext : Subgroup G)
    (hW : W = conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle))
    (hWnext : Wnext = GeneratedNeighborhoodV ctx.Γ middle)
    (hW0 : W0 = NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext)
    (hresidual : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) 2)
    (hlarge : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hmodel : QuotientIsFrobenius20 (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep)) :
    QuotientCardEq W0 W 2 ∧ QuotientCardEq Wnext W (2 ^ 3) ∧
      QuotientCardEq Wnext W0 4 ∧
      DerivedAmbient Wnext =
        VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  have hnextIndex : QuotientCardEq Wnext W 8 := by
    rw [hWnext, hW]
    exact ten_one_large_neighborhood_quotient ctx middle hpath hresidual hlarge hno
  have hzeroIndex : QuotientCardEq Wnext W0 4 := by
    rw [hW0, hWnext]
    exact ten_one_large_neighborhood_core_index ctx middle hpath hmodel
  refine ⟨?_, hnextIndex, hzeroIndex, ?_⟩
  · change Nat.card W0 = 2 * Nat.card W
    change Nat.card Wnext = 8 * Nat.card W at hnextIndex
    change Nat.card Wnext = 4 * Nat.card W0 at hzeroIndex
    omega
  · rw [hWnext]
    exact ten_one_large_derived ctx middle hpath hlarge hno

end Stellmacher.SectionTen
