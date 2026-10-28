module

public import Stellmacher.SectionEight.GeneratedEightSixSubgroupForcingHelper

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

public theorem generated_eight_six_subgroup_forcing
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (equation : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    ∀ actor : (P1 ⊔ P2 : Subgroup H),
      actor ∈ QAt ctx.Γ ctx.criticalPath.firstStep → actor ∉ Q →
      ∀ U : Subgroup (P1 ⊔ P2 : Subgroup H),
        U ≤ QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
        ⁅U, Subgroup.zpowers actor⁆ ≤ D → U ≤ D := by
  exact generated_eight_six_quotient_action_forcing ctx hcenter hquot hlength hcard
    previous D L Q T hprev hdefs hbase equation

end Stellmacher.SectionEight
