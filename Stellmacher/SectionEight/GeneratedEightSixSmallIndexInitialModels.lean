module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInitialCore
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInitialInverter
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInitialReduction

/-!
# SmallIndexInitialModels in the small-index branch of (8.6)

The initial model package in the small-index branch consists of a residual two-core C4 ×
C4 and a trivial or inverting supplement generating the initial core. The order-sixteen
branch needs no supplement; the order-thirty-two branch uses the actual inverter
selected from the elementary-eight action.

The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.

Source: Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.42, paragraph ending in (6).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

set_option linter.unusedVariables false in
public theorem eight_six_small_index_initial_models_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : Later.SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (D L Q T : Subgroup G)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D,L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (next : EightSixSmallIndexNextData ctx.Γ ctx.criticalPath) :
    IsModel (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) (C4 × C4) ∧
      ∃ actor : G,
        (actor = 1 ∨ IsInvertingOn actor (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a))) ∧
        Q = GeneratedWith (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) actor := by
  have hcore := eight_six_small_index_initial_core_local ctx hcenter hquot
    hlength hcard previous D L Q T hprev hdefs hbase hindex data orders next
  exact eight_six_initial_models_of_core_and_inverter ctx.Γ ctx.criticalPath orders
    hcard hcore (fun hQcard => eight_six_small_index_initial_inverter_local ctx
      hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders
      next hcore hQcard)

public theorem generated_eight_six_small_index_initial_models
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : Later.GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D,L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (next : EightSixSmallIndexNextData ctx.Γ ctx.criticalPath) :
    IsModel (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) (C4 × C4) ∧
      ∃ actor : (P1 ⊔ P2 : Subgroup H),
        (actor = 1 ∨ IsInvertingOn actor (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a))) ∧
        Q = GeneratedWith (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) actor := by
  exact eight_six_small_index_initial_models_local ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders next

end Stellmacher.SectionEight
