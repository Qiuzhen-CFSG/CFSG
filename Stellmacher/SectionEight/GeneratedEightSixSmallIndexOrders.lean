module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCenter
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCounts
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCoreEquality
public import Stellmacher.SectionEight.GeneratedEightSixIntersectionCentralizer

/-!
# SmallIndexOrders in the small-index branch of (8.6)

The small-index branch of (8.6) has generated-core quotient of order four, center
intersection equal to the initial vertex center, center index at most two, and generated
core equal to the initial vertex core. The proof combines actual local centralizer
rigidity with the independently proved count and core-equality calculations.

The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.

Source: Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.42, paragraph ending in (6).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven
universe u

set_option linter.unusedVariables false in
public theorem eight_six_small_index_orders_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : Later.SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a) (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2) (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup G)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧ previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧ L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧ Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧ QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q := by
  have hintersectionCentralizer := eight_six_intersection_centralizer_of_rigidity
    ctx.sectionSeven ctx.Γ ctx.criticalPath hcenter previous D L Q hdefs.1 data (by
      intro U hU hUS
      have hUZ := eight_six_rigidity_le_initial_center ctx.sectionSeven ctx.Γ ctx.criticalPath
        hcenter hquot previous D L Q hdefs.1 hdefs.2.1 data U (hU.trans inf_le_left) hUS
      exact eight_six_rigidity_le_first_center_of_le_initial ctx hcenter hlength hcard
        previous D L Q data U hUZ (hU.trans inf_le_right))
  have hfirstcentralizer := eight_six_first_core_part_centralizer_of_intersection_centralizer
    ctx.sectionSeven ctx.Γ ctx.criticalPath hcenter hquot hcard previous D L Q hdefs.1 data
    hintersectionCentralizer
  have hcentralizer := eight_six_predecessor_core_part_centralizer_of_first_core_part
    ctx.sectionSeven ctx.Γ ctx.criticalPath previous hprev.1 D L Q data hfirstcentralizer
  have hcounts := eight_six_small_index_counts_local ctx hcenter hquot hlength hcard previous D L Q T
    hprev hdefs hbase hindex data hcentralizer
  have hintersection := eight_six_core_center_intersection_of_predecessor_centralizer
    ctx.sectionSeven ctx.Γ ctx.criticalPath previous D L Q data hbase.1 hbase.2.2 hcentralizer
  have hcore := eight_six_small_index_core_eq_local ctx hcenter hquot hlength hcard previous D L Q T
    hprev hdefs hbase hindex data hcounts.1 hintersection hcounts.2
  exact {
    quotient_card := hcounts.1
    center_intersection := hintersection
    center_index := hcounts.2
    core_eq := hcore }

public theorem generated_eight_six_small_index_orders
    {H : Type u} [Group H] [Finite H] {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : Later.GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a) (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2) (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧ previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧ L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧ Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧ QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q := by
  exact eight_six_small_index_orders_local ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data

end Stellmacher.SectionEight
