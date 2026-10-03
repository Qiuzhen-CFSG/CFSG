module

public import Stellmacher.SectionEight.EightFourCentralizerCriterion
public import Stellmacher.SectionEight.EightFiveFixedCenterGeneration
public import Stellmacher.SectionEight.EightFiveCentralFixedRankOne

/-!
# The initial center has order four under the fixed-center normality of (8.4)

In the original Section Eight noncommuting critical-pair context, suppose the
first-step center is central and the fixed subgroup of the faithful initial
center action is normal in the first-step stabilizer. Then the initial center
has order four. The explicit normality premise is exactly the conclusion of
(8.4) for the supplied quotient-module witness; its action is unchanged.

The fixed-center generation theorem uses (8.3) and the normal-subgroup core
bound to show that every fixed vector's centralizer generates the next
stabilizer together with the initial edge. The canonical (6.4) graph criterion
therefore places the fixed subgroup in the next center. That center is central
in the next stabilizer, so the edge Sylow centralizes the fixed subgroup.
The rank-one theorem now forces the faithful center action to have just one
SL2(2) support and eliminates its fixed complement, giving order four.

This proves the first structural reduction of Stellmacher (8.5), Journal of
Algebra 190 (1997), journal p.40. The separate quotient and distance leaves
use this order to finish (8.5) when its parent supplies the normality from
(8.4). No unfinished numbered theorem is used here.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

/-- The source (8.4) normality of the actual barred fixed center forces the
initial center in (8.5) to have order four. -/
public theorem eight_five_center_card_four_of_fixed_normal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hnormal : NormalIn (w.oneJFixedPoints S)
      (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 := by
  have hFnext : w.oneJFixedPoints S ≤ ZAt ctx.Γ ctx.criticalPath.firstStep := by
    intro v hv
    exact eight_four_vector_centralizer_criterion ctx hcenter w v hv
      (eight_five_fixed_vector_centralizer_generation ctx hcenter w hnormal v hv)
  have hnextFix : GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.centralizer (w.oneJFixedPoints S : Set H) :=
    Subgroup.le_centralizer_iff.mp
      (hFnext.trans (hcenter.trans (SevenSix.centerAmbient_le_centralizer _)))
  exact eight_five_center_card_four_of_sylow_centralizes_fixed ctx hcenter w
    ((ctx.criticalPath.S_le_edge_stabilizers.trans inf_le_right).trans hnextFix)

end Stellmacher.SectionEight
