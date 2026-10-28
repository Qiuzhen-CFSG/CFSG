module

public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.JankoTwo
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.SmallRatio

/-!
# Removing J₂ from the unmarked F.9.18 source alternatives

The original B.4 action at quadratic ratio at most two cannot have a J₂
central quotient. The exclusion also transports along the actual isomorphism
from the source star image to the whole generalized Fitting subgroup, using
the literal induced map on central quotients.

The remaining source alternatives still belong to the small-quadratic
classification assembly; this file discharges precisely its J₂ branch.
Source: Aschbacher--Smith B.4.5, p.87, K.4.5, p.460, and F.9.18(4), pp.325--326.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
open ChapterB.SmallRatioClassification.UnmarkedQuadratic
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
universe u v w
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V)

/-- The remaining-model disjunction carries a proved exclusion of its J₂
constructor under the actual B.4 hypotheses, without an FF assumption. -/
theorem f918Models_or_nonFF_remaining_without_janko_two
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2) :
    Models.F918Models (generalizedFitting D) ∨
      (¬ IsFFModule ρ ∧ RemainingModel (generalizedFitting D) ∧
        ¬ Nonempty ((generalizedFitting D ⧸ center (generalizedFitting D)) ≃*
          KnownSimple.SporadicName.j2.Carrier)) := by
  rcases f918Models_or_nonFF_remaining ρ hyp hq with hm | ⟨hff, hr⟩
  · exact Or.inl hm
  · exact Or.inr ⟨hff, hr, JankoTwo.b4_exclusion hyp hq⟩

/-- The literal star-image central quotient cannot be J₂ when the supplied
source action identifies that image with its entire generalized Fitting group. -/
theorem source_starImage_not_janko_two
    {G : Type w} [Group G] (H K : Subgroup G)
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2)
    (e : Source.starImage H K ≃* generalizedFitting D) :
    ¬ Nonempty ((Source.starImage H K ⧸ center (Source.starImage H K)) ≃*
      KnownSimple.SporadicName.j2.Carrier) := by
  rintro ⟨a⟩
  exact JankoTwo.b4_exclusion hyp hq ⟨(centralQuotientEquiv e).symm.trans a⟩

end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
