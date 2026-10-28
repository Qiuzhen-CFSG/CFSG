module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexQuotientFour
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCenterCounts

/-!
# Quotient and center orders in the small-index branch of (8.6)

The two independent quotient generators give order four. The predecessor
commutator bound and its explicit centralizer identify the center index as
one or two. Equation-one data and the centralizer equality are supplied by
their separate producers; equality of the two cores is not used here.

Source: Stellmacher, printed p.42, paragraph between (5) and (6), using (1)
on printed p.41.
The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

set_option linter.unusedVariables false in
public theorem eight_six_small_index_counts_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : Later.SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup G)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hcentralizer : D ⊓ Subgroup.centralizer
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a :
        Set G) = ZAt ctx.Γ ctx.criticalPath.a) :
    QuotientCardEq Q D 4 ∧
      (QuotientCardEq D (ZAt ctx.Γ ctx.criticalPath.a) 1 ∨
        QuotientCardEq D (ZAt ctx.Γ ctx.criticalPath.a) 2) := by
  exact ⟨eight_six_small_index_quotient_four_local ctx hcenter hquot hlength
    hcard previous D L Q T hprev hdefs hbase hindex data,
    eight_six_small_index_center_counts ctx.sectionSeven ctx.Γ ctx.criticalPath
      hcenter hcard previous hprev.1 D L Q hdefs.1 hbase.2.2 hindex data hcentralizer⟩

public theorem generated_eight_six_small_index_counts
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : Later.GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hcentralizer : D ⊓ Subgroup.centralizer
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a :
        Set (P1 ⊔ P2 : Subgroup H)) = ZAt ctx.Γ ctx.criticalPath.a) :
    QuotientCardEq Q D 4 ∧
      (QuotientCardEq D (ZAt ctx.Γ ctx.criticalPath.a) 1 ∨
        QuotientCardEq D (ZAt ctx.Γ ctx.criticalPath.a) 2) := by
  exact eight_six_small_index_counts_local ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data hcentralizer

end Stellmacher.SectionEight
