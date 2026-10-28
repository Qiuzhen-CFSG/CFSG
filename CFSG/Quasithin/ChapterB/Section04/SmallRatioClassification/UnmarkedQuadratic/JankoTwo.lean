module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Ratios
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.JankoTwoSource

/-!
# Excluding the unmarked J₂ quadratic source

The odd-primary multiplier bound makes the center of the original component
a two-group, and faithful binary irreducibility kills that center. The existing
source degree reduction now applies: four-conjugate generation and automorphism
two-rank four give degree at most 32, and the cubic displacement calculation
excludes degree 28. Degree twelve recognizes the whole ambient action, including
outer actors. The proved root and long-root module facts then give q > 2.

This discharges the J₂ branch of `UnmarkedQuadratic.RemainingModel` under the
actual B.4 hypotheses. Neither FF nor a module marking is assumed. The generic
degree reduction is reused from `TerminalContradiction.Ratio.JankoTwoSource`;
its statement has exactly the Chapter K source hypotheses.

Source: Aschbacher--Smith B.4.5, printed p.87, and K.4, pp.457--460;
Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.JankoTwo
open Chapter13.Section06.TerminalContradiction.Ratio
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The original cubic source has trivial component center and binary degree
twelve, with no FF or small-displacement premise. -/
theorem center_and_degree (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j2.Carrier)) :
    center L = ⊥ ∧ Module.finrank (ZMod 2) V = 12 := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  have hz2 := Theory.SpecificGroups.J2HSMultipliers.J2.center_isPGroup_of_quotient_equiv e
  have hk := normal_p_subgroup_le_ker (ρ.comp (generalizedFitting G).subtype)
    (center (generalizedFitting G)) hz2
  have hz : center (generalizedFitting G) = ⊥ := by
    apply bot_unique
    simpa only [(ρ.comp (generalizedFitting G).subtype).ker_eq_bot_iff.mpr
      (h.faithful.comp (generalizedFitting G).subtype_injective)] using hk
  let eL : generalizedFitting G ≃* _root_.Sporadic.LeechRelated.J2.Carrier :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e
  exact ⟨hz, JankoTwoSource.finrank_eq_twelve h hz eL⟩

/-- K.4.5's strict quadratic bound on the original unmarked ambient action. -/
theorem two_lt_quadraticRatio (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j2.Carrier)) :
    2 < quadraticRatio ρ := by
  obtain ⟨hz, hd⟩ := center_and_degree h he
  obtain ⟨D⟩ := ChapterK.SporadicCatalogue.SourceFF.j2_marked_of_center_and_degree
    ρ L h he hz hd
  exact D.two_lt_quadraticRatio (ChapterK.JankoTwo.NaturalLocalAction.b46RootFacts _)
    ChapterK.JankoTwo.NaturalLocalAction.b46LongRootModuleFacts_four

/-- The unmarked J₂ quotient is impossible at quadratic ratio at most two. -/
theorem exclusion (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : quadraticRatio ρ ≤ 2)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j2.Carrier)) : False :=
  (not_lt_of_ge hq) (two_lt_quadraticRatio h he)

open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases in
/-- Eliminate the model premise of `RemainingModel.janko_two` at the literal
B.4 generalized Fitting subgroup, retaining the entire original action. -/
theorem b4_exclusion [Finite V]
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2)
    (he : Nonempty ((generalizedFitting G ⧸ center (generalizedFitting G)) ≃*
      KnownSimple.SporadicName.j2.Carrier)) : False :=
  exclusion ⟨h.sqtk, rfl, h.quasisimple, h.faithful, h.irreducible,
    (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩ hq he

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.JankoTwo
