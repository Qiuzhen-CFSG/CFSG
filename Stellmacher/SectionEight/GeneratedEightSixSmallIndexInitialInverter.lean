module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInverterSelection
public import Stellmacher.SectionEight.C4SquareElementaryEightAction

/-!
# SmallIndexInitialInverter in the small-index branch of (8.6)

If the initial core has order thirty-two, an element of that core inverts its residual
two-core C4 × C4. The elementary eight intersection and full initial-center action
supply the hypotheses of the C4-square action classification; the resulting element is
selected inside the actual core.

The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.

Source: Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.42, paragraph ending in (6).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

set_option linter.unusedVariables false in
public theorem eight_six_small_index_initial_inverter_local
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
    (next : EightSixSmallIndexNextData ctx.Γ ctx.criticalPath)
    (hcore : IsModel (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) (C4 × C4))
    (hQcard : Nat.card Q = 32) :
    ∃ actor : G, actor ∈ Q ∧
      IsInvertingOn actor (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) := by
  let _ := hquot
  let _ := hlength
  let _ := hprev
  let _ := hdefs
  let _ := hindex
  let _ := next
  let localCtx := ctx
  have hDcard : Nat.card D = 8 := by
    rcases eight_six_initial_order_cases localCtx.Γ localCtx.criticalPath orders hcard with hsmall | hlarge
    · omega
    · exact hlarge.1
  have hintersection := eight_six_initial_inverter_intersection_local localCtx hcenter hcard
    orders hbase.2.2 hcore
  have hfull := eight_six_initial_center_full_action_local localCtx hcard
  have hclassification := c4_square_elementary_eight_action
    (hcore := eight_six_initial_residual_core_normal_local localCtx)
    (hD := data.intersection_normal) (hmodel := hcore)
    (helementary := hbase.2.2) (hcardD := hDcard) (hcardZ := hcard)
    (hinter := hintersection) (hfull := hfull)
  exact eight_six_initial_inverter_of_elementary_action_local localCtx hcenter hcard
    previous D L Q data orders hbase.2.2 hcore hQcard hclassification

public theorem generated_eight_six_small_index_initial_inverter
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
    (next : EightSixSmallIndexNextData ctx.Γ ctx.criticalPath)
    (hcore : IsModel (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) (C4 × C4))
    (hQcard : Nat.card Q = 32) :
    ∃ actor : (P1 ⊔ P2 : Subgroup H), actor ∈ Q ∧
      IsInvertingOn actor (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) := by
  exact eight_six_small_index_initial_inverter_local ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders next hcore hQcard


#print axioms generated_eight_six_small_index_initial_inverter

end Stellmacher.SectionEight
