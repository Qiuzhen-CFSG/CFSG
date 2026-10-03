module

public import Stellmacher.SectionEight.GeneratedEightSixNextCoreEightPair

/-!
# NextCoreThirtyTwo in the small-index branch of (8.6)

A next core of order thirty-two in the small-index branch is the central product Q8 ∘
Q8. The two elementary eight subgroups obtained from the local commutator calculation
generate the core, and their normality and common center give the imported recognition
hypotheses.

The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.

Source: Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.42, paragraph ending in (6).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

set_option linter.unusedVariables false in
public theorem eight_six_next_core_quaternion_product_of_card_thirty_two_local
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
    (hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16)
    (hv : IsCentralProductModel (VAt ctx.Γ ctx.criticalPath.firstStep) C4 Q8)
    (hi : IsModel (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
      (C2 × C4))
    (hlarge : Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) = 32) :
    IsCentralProductQ8Q8 (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  obtain ⟨other, hOther, hOtherCard, hjoin, hcenterCard⟩ :=
    eight_six_next_core_second_eight_and_center_local ctx hcenter hquot
      hlength hcard previous D L Q T hprev hdefs hbase hindex data orders hnext
      hsmall hv hi hlarge
  obtain ⟨hDle, hDcard, hDelementary, hDnormal⟩ :=
    eight_six_next_core_normal_elementary_eight ctx.sectionSeven ctx.Γ
      ctx.criticalPath previous D L Q hdefs.1 hbase.2.2 data orders hquot hnext hlarge
  have hnativeCard : Nat.card (D.subgroupOf (QAt ctx.Γ ctx.criticalPath.firstStep)) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv).trans hDcard
  exact eight_six_quaternion_product_of_native_elementary_eights
    (QAt ctx.Γ ctx.criticalPath.firstStep) other
    (D.subgroupOf (QAt ctx.Γ ctx.criticalPath.firstStep))
    hOther hDelementary hOtherCard hnativeCard hjoin hDnormal hcenterCard

public theorem generated_eight_six_next_core_quaternion_product_of_card_thirty_two
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
    (hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16)
    (hv : IsCentralProductModel (VAt ctx.Γ ctx.criticalPath.firstStep) C4 Q8)
    (hi : IsModel (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
      (C2 × C4))
    (hlarge : Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) = 32) :
    IsCentralProductQ8Q8 (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  exact eight_six_next_core_quaternion_product_of_card_thirty_two_local ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders hnext hsmall hv hi hlarge


end Stellmacher.SectionEight
