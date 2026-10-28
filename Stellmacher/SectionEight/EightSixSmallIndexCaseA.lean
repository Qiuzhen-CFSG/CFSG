module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexOrders
public import Stellmacher.SectionEight.GeneratedEightSixNextSmallModels
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInitialModels
public import Stellmacher.SectionEight.GeneratedEightSixCentralQuotientBounds
public import Stellmacher.SectionEight.GeneratedEightSixNextConjugateGeometry
public import Stellmacher.SectionEight.SmallNonabelianCoreQuotient

/-!
# The small-index case of Stellmacher (8.6)

For the actual graph-local distance-two configuration, an index-two predecessor
core part implies the complete case-A type data. The hypotheses retain the
central next vertex, the initial SL₂(2) quotient and order-four center, the
chosen predecessor and local subgroup definitions, the elementary intersection,
and the proved equation-one identities.

The local count and cyclic-center argument first identifies the generated core
with the initial core and bounds the edge Sylow order by sixty-four. The next
core is nonabelian of order at most thirty-two; in the largest case it contains
the actual elementary intersection of order eight. Small-core recognition gives
the next SL₂(2) quotient. Its three conjugate elementary planes then bound the
next neighbor-generated group by sixteen. The resulting quaternion central
products and initial C4-square model, together with the selected inverting
supplement, give every field of case A.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6), printed p.42,
the small-index paragraph ending in (6). This assembly uses the ordinary local
two-core and retains all previously generated-context APIs through their local
wrappers; it assumes no additional recognition or model witness.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_small_index_caseA_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a) (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2) (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup G)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧ previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧ L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧ Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧ QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    EightSixCaseATypeData ctx.Γ ctx.criticalPath previous D L Q T := by
  have orders := eight_six_small_index_orders_local ctx hcenter hquot hlength hcard
    previous D L Q T hprev hdefs hbase hindex data
  have hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two := by
    have hD : D ≤ QAt ctx.Γ ctx.criticalPath.firstStep := hdefs.1 ▸ inf_le_right
    obtain ⟨hS, hnoncomm, hbound, height⟩ :=
      eight_six_central_quotient_core_data_local ctx hcenter hquot hcard hlength
        orders hD hbase.2.2 data.first_commutator
    have hcore : QAt ctx.Γ ctx.criticalPath.firstStep =
        twoCoreIn (GAt ctx.Γ ctx.criticalPath.firstStep) :=
      ctx.Γ.twoCoreAt_def ctx.criticalPath.firstStep
    change ¬ IsMulCommutative (QAt ctx.Γ ctx.criticalPath.firstStep) at hnoncomm
    rw [hcore] at hnoncomm hbound height ⊢
    have hlocal := (SevenSix.edge_local_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
    exact small_nonabelian_core_quotient_sl2Two _ _ hlocal.1 hlocal.2
      (SevenSix.edge_characteristic_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
      hS hnoncomm hbound height
  have hsmall := eight_six_next_v_card_le_of_quotient_local ctx hcenter hlength
    hcard data.first_commutator hnext
  have next := eight_six_small_index_next_models_of_bound_local ctx hcenter hquot
    hlength hcard previous D L Q T hprev hdefs hbase hindex data orders hnext hsmall
  obtain ⟨hcore, hgenerated⟩ := eight_six_small_index_initial_models_local ctx hcenter
    hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders next
  exact eight_six_caseA_of_order_and_models ctx.sectionSeven ctx.Γ ctx.criticalPath
    previous D L Q T hprev hdefs hbase hquot hcard orders
    (eight_six_models_of_next_and_initial ctx.Γ ctx.criticalPath Q next hcore hgenerated)

end Stellmacher.SectionEight
