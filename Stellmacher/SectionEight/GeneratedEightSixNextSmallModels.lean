module

public import Stellmacher.SectionEight.GeneratedEightSixNextVModels
public import Stellmacher.SectionEight.GeneratedEightSixNextCoreModels

/-!
# NextSmallModels in the small-index branch of (8.6)

The next-vertex model package in the small-index branch combines the bounded neighbor-
generated group and intersection recognition with the small/large next-core
classification. Its explicit next quotient and group-order bound are supplied by the
canonical small-index assembly.

The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.

Source: Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.42, paragraph ending in (6).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

set_option linter.unusedVariables false in
public theorem eight_six_small_index_next_models_of_bound_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : Later.SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a) (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup G)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧ previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧ L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧ Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D,L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧ QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep) (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16) :
    EightSixSmallIndexNextData ctx.Γ ctx.criticalPath := by
  have hvsmall := hsmall
  have hvmodels := eight_six_next_v_intersection_models_of_bound_local ctx hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders hnext hvsmall
  have hcoremodels := eight_six_next_core_models_of_small_v_local ctx hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders hnext hvsmall hvmodels.1 hvmodels.2
  exact ⟨hnext, hvmodels.1, hvmodels.2, hcoremodels⟩

public theorem generated_eight_six_small_index_next_models_of_bound
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : Later.GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a) (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧ previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧ L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧ Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D,L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧ QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep) (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16) :
    EightSixSmallIndexNextData ctx.Γ ctx.criticalPath := by
  exact eight_six_small_index_next_models_of_bound_local ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders hnext hsmall


#print axioms generated_eight_six_small_index_next_models_of_bound
end Stellmacher.SectionEight
