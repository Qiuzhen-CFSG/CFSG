module
public import Stellmacher.SectionEight.EightSixDefs
public import Stellmacher.SectionEight.EightSixCanonicalStructure
public import Stellmacher.SectionEight.EightSixSmallIndexCaseA

/-!
# The canonical small-index branch of Stellmacher (8.6)

For the original Section Eight context, an index-two predecessor core part
gives the exact public conclusion of (8.6), through alternative A. The
original predecessor and D,L,Q,T are retained. The additional premise is
precisely the source's small-index branch |A : A intersect D| = 2.

The proved (8.5) supplies the initial quotient, length two and center order
four. The common-structure theorem yields the elementary and commutator data,
and the local small-index classification supplies all order bounds, local
quotients, quaternion central products and the inverting supplement. These
are inserted into the unchanged public alternative and conclusion types.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6), printed
pp.41–42, small-index paragraph and assertion (6).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven
universe u

public theorem lemma_eight_six_of_small_index
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (aPrev : ctx.Γ.Vertex) (D L Q T : Subgroup H)
    (hprev : aPrev ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      aPrev ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ aPrev ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ aPrev)
      (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hindex : QuotientCardEq (VAt ctx.Γ aPrev ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ aPrev ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2) :
    LemmaEightSixConclusion ctx aPrev D L Q T := by
  obtain ⟨equation, hbase⟩ := eight_six_common_structure ctx hcenter aPrev hprev D L Q hD hL hQ
  obtain ⟨hquot, hlength⟩ := lemma_eight_five ctx hcenter
  obtain ⟨w, _⟩ := (lemma_eight_one ctx).barred_decomposition
  have hcard := eight_five_center_card_four_of_fixed_normal ctx hcenter w
    (lemma_eight_four ctx hcenter w)
  have data := eight_six_small_index_caseA_local ctx.toLocalContext hcenter hquot hlength
    hcard aPrev D L Q T hprev ⟨hD,hL,hQ,hT⟩ hbase hindex equation
  exact ⟨hprev, ⟨hD,hL,hQ,hT⟩, hbase,
    .a data.card_S data.local_quotients data.Q_eq data.twoCore_model data.generated
      data.next_twoCore⟩

end Stellmacher.SectionEight
