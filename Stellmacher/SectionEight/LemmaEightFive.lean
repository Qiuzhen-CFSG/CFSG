module

public import Stellmacher.SectionEight.LemmaEightFour
public import Stellmacher.SectionEight.EightFiveCenterFour
public import Stellmacher.SectionEight.EightFiveQuotientFromFour
public import Stellmacher.SectionEight.EightFiveDistanceFromFour

/-!
# Stellmacher (8.5): the initial quotient and critical distance

In the noncommuting critical-pair context, centrality of the first-step center
forces the initial stabilizer modulo its ordinary two-core to be SL₂(2), and
the critical path has length two. The original ambient Hypothesis Two and
faithful initial-center action are retained throughout.

Choose the quotient-module witness supplied by (8.1). The fixed-center
normality of (8.4), combined with the canonical (6.4) centralizer criterion,
forces the initial center to have order four. The quotient-recognition leaf
then uses the odd-dihedral action and (7.7) centralizer argument to identify
the ordinary core quotient. Finally the independent backward-neighbor and
centralizer-core argument excludes every critical length greater than two.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.5), printed pp.40–41,
including the distance argument continuing on p.41 of the full journal scan.
-/

namespace Stellmacher.SectionEight

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (8.5).** If the first-step center is central, the initial
ordinary two-core quotient is SL₂(2) and the critical distance is two. -/
public theorem lemma_eight_five
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    QuotientIsModel
        (GAt ctx.Γ ctx.criticalPath.a)
        (QAt ctx.Γ ctx.criticalPath.a) SL2Two ∧
      ctx.criticalPath.length = 2 := by
  obtain ⟨w, _⟩ := (lemma_eight_one ctx).barred_decomposition
  have hfour := eight_five_center_card_four_of_fixed_normal ctx hcenter w
    (lemma_eight_four ctx hcenter w)
  have hquotient := eight_five_quotient_of_card_four ctx hcenter hfour
  exact ⟨hquotient, eight_five_length_of_card_four_and_quotient ctx hcenter hfour hquotient⟩

end Stellmacher.SectionEight
