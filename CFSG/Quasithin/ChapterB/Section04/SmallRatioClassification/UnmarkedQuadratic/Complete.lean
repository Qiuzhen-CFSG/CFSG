module

public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.JankoTwo
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu
public import CFSG.Quasithin.ChapterK.Section01To04.OddCharacteristic.SourceSmallLinearTwentyFive
public import CFSG.Quasithin.ChapterK.Section01To04.OddCharacteristic.SourceSmallLinearThree
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsTrialityComplete
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsReeComplete
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSource

/-!
# The complete unmarked small-quadratic group classification

The quotient sieve leaves ten marked families. The Chapter K cubic-source
exclusions remove PSL₂(25), PSL₃(3), triality, Ree F₄, M₁₁ and HS. The strict
quadratic bounds remove J₂, M₁₂, M₂₃ and M₂₄; native M₂₄ completeness supplies
the degree reduction in the last case. Every exclusion concerns the same
ambient action and the actual central quotient of its generalized Fitting
subgroup, so no module marking or displacement hypothesis is added.

The accepted branches of the sieve retain their actual quotient isomorphisms,
the simple or triple-cover M₂₂ alternatives, and the exclusion of 3.A₇.
This proves the group-model consequence needed from B.4.5 without requiring
the full module table. The non-FF specialization feeds `SourceModels.SmallRatio`,
which combines it with B.4.2 and applies it to the original source star image.

Source: Aschbacher--Smith B.4.5, printed p.87; Chapter K, pp.451--460;
F.9.18(4), pp.325--326.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic
open Chapter13.Section08.Components.Models
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- All ten residual central-quotient families are excluded on the original
source action when its quadratic ratio is at most two. -/
theorem remainingModel_false (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : quadraticRatio ρ ≤ 2) (hr : RemainingModel L) : False := by
  cases hr with
  | linear_two_twentyFive hm => exact ChapterK.OddCharacteristic.not_pslTwo_twentyFive h hm
  | linear_three_three hm => exact ChapterK.OddCharacteristic.not_pslThree_three h hm
  | triality r hr hm =>
    exact ChapterK.Exceptional.CubicSourceExclusions.triality_cubic_source_false h hr hm
  | ree m hm he =>
    exact ChapterK.Exceptional.CubicSourceExclusions.ree_cubic_source_false h hm he
  | mathieu_eleven he => exact ChapterK.SporadicCatalogue.not_m11_of_rankOne_source h he
  | mathieu_twelve he => exact Mathieu.no_m12 h hq he
  | mathieu_twentyThree he => exact Mathieu.no_m23 h hq he
  | mathieu_twentyFour he => exact Mathieu.no_m24 h hq he
  | janko_two he => exact JankoTwo.exclusion h hq he
  | higman_sims he => exact ChapterK.SporadicCatalogue.not_hs_of_rankOne_source h he

/-- The unmarked Chapter K source action has the exact F.9.18 group models
at quadratic ratio at most two, with every residual family discharged. -/
theorem models_of_quadratic (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : quadraticRatio ρ ≤ 2) : F918Models L :=
  (models_or_remaining h).resolve_right (remainingModel_false h hq)

open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases in
/-- The non-FF group-model consequence of B.4.5 on its literal finite action.
The group-level sieve in fact proves this consequence independently of non-FF. -/
theorem b4_models_of_nonFF [Finite V]
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2)
    (_hff : ¬ IsFFModule ρ) : F918Models (generalizedFitting G) :=
  models_of_quadratic ⟨h.sqtk, rfl, h.quasisimple, h.faithful, h.irreducible,
    (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩ hq

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic
