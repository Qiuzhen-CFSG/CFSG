module

public import Stellmacher.SectionEight.GeneratedEightSixSylowIntersection
public import Stellmacher.SectionEight.GeneratedEightSixIntersectionNormality
public import Stellmacher.SectionEight.GeneratedEightSixResidualCommutator

/-!
# The four upstream action identities in generated (8.6)

Assemble the independently proved intersection normality, Sylow supplement,
first commutator, and residual commutator under the exact generated hypotheses.
The residual theorem's three action premises are discharged here, not retained
as new assumptions. The graph group remains the generated join, with Hypothesis
Two on the original ambient group.

Source: Stellmacher, printed p.41, paragraph before and equation (8.6)(1),
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem generated_eight_six_upstream_action_identities
    {H : Type u} [Group H] [Finite H] {S0 : Sylow 2 H}
    {S P1 P2 : Subgroup H}
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
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L) :
    NormalIn D (GAt ctx.Γ ctx.criticalPath.a) ∧
      L ⊓ S.subgroupOf (P1 ⊔ P2) = VAt ctx.Γ ctx.criticalPath.firstStep ⊔ Q ∧
      ⁅VAt ctx.Γ ctx.criticalPath.firstStep, QAt ctx.Γ ctx.criticalPath.firstStep⁆ =
        ZAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅D, twoResidualIn L⁆ = ZAt ctx.Γ ctx.criticalPath.a := by
  have hnormal : NormalIn D (GAt ctx.Γ ctx.criticalPath.a) := by
    rw [hD]
    exact generated_eight_six_intersection_normal ctx hcenter hquot hlength hcard previous hprev
  have hsylow := eight_six_sylow_intersection_local ctx.toLocalContext hcard hlength
    previous hprev.1 L Q hL hQ
  have hfirst := eight_six_first_commutator_local ctx.toLocalContext hcenter hcard hlength
  exact ⟨hnormal, hsylow, hfirst,
    generated_eight_six_residual_commutator ctx hcenter hquot hlength hcard
      previous hprev D L Q hD hL hQ hnormal hsylow hfirst⟩

end Stellmacher.SectionEight
