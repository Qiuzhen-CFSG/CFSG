module

public import Stellmacher.SectionEight.GeneratedEightSixFrattiniTools
public import Stellmacher.SectionEight.GeneratedEightSixIntersectionCommutator
public import Stellmacher.SectionEight.GeneratedEightSixIntersectionCentralizer

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

public theorem generated_eight_six_intersection_frattini_of_centralizer
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hcentralizer : D ⊓ Subgroup.centralizer
      (VAt ctx.Γ ctx.criticalPath.firstStep : Set (P1 ⊔ P2 : Subgroup H)) =
        ZAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧ FrattiniAmbient D = ⊥ := by
  have hfrattini := eight_six_intersection_frattini_eq_bot_of_centralizer
    ctx.sectionSeven ctx.Γ ctx.criticalPath hcenter previous D L Q hD data hcentralizer
  exact ⟨eight_six_intersection_full_commutator_of_frattini ctx.sectionSeven ctx.Γ
    ctx.criticalPath hcenter previous hprevious D L Q hD data hfrattini, hfrattini⟩

public theorem generated_eight_six_intersection_frattini
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = SectionsFiveToSeven.conjugateClosure
      (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧ FrattiniAmbient D = ⊥ := by
  exact generated_eight_six_intersection_frattini_of_centralizer ctx hcenter previous
    hprev.1 D L Q hD data (generated_eight_six_intersection_centralizer ctx hcenter
      hquot hlength hcard previous hprev D L Q hD hL hQ data)

end Stellmacher.SectionEight
