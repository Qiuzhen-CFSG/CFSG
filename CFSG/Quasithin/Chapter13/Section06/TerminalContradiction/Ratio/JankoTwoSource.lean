module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.JankoTwo
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.TwoRank
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace

/-!
# The J₂ strict ratio bound on the original terminal source action

The native automorphism two-rank bound four and four-conjugate generation put
an original cubic source action in degree at most 32. The complete binary
degree spectrum leaves 12 or 28. In degree 28 every ambient involution moves
at least ten dimensions, whereas a cubic actor of ratio at most two moves
at most eight. Thus the action has degree twelve and admits its genuine
whole-action natural marking, including outer field elements. The proved
J₂ actor calculation then gives quadratic ratio strictly greater than two.

All representations, component inclusions and actor subgroups in this argument
are literal. No universal B.4.5 or FF hypothesis is required.
Source: Aschbacher–Smith B.4.5 and K.4.5, pp.87,460; GM02 Proposition 5.1.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.JankoTwoSource
open _root_.Sporadic.LeechRelated.J2
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The cubic source action on a center-free J₂ component has binary degree twelve. -/
theorem finrank_eq_twelve
    (h : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting G))
    (hz : center (generalizedFitting G) = ⊥)
    (e : generalizedFitting G ≃* Carrier) : Module.finrank (ZMod 2) V = 12 := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsSimpleGroup (generalizedFitting G ⧸ center (generalizedFitting G)) := h.quasisimple.simple
  let eQ := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e
  let : IsSimpleGroup Carrier := eQ.symm.isSimpleGroup
  let : IsSimpleGroup (generalizedFitting G) := e.isSimpleGroup
  have hr : primeRank 2 G ≤ 4 :=
    (primeRank_le_central_quotient_automorphisms ρ (generalizedFitting G)
      h.faithful h.irreducible eQ).trans automorphism_primeRank_le_four
  have hfix : fixedSpace ρ (generalizedFitting G) = ⊥ :=
    invariants_eq_bot_of_faithful_irreducible (ρ.comp (generalizedFitting G).subtype)
      (h.faithful.comp (generalizedFitting G).subtype_injective) h.irreducible
  have hd : Module.finrank (ZMod 2) V ≤ 32 := by
    simpa using finrank_le_of_cubicRatio_le_of_conjugates ρ (generalizedFitting G) hfix
      (m := 2) (FourConjugateGeneration.involution_conjugate_generation_bound e) hr h.smallCubic
  let σ := (ρ.comp (generalizedFitting G).subtype).comp e.symm.toMonoidHom
  have hfσ : Function.Injective σ :=
    h.faithful.comp ((generalizedFitting G).subtype_injective.comp e.symm.injective)
  have hiσ : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  rcases Representation.JankoTwo.SmallBinaryDegrees.finrank_twelve_or_twentyEight σ hfσ hiσ hd
      with h12 | h28
  · exact h12
  exfalso
  obtain ⟨A,hA,_,hbound⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.smallCubic
  have hrA := hA.rank_le_of_primeRank_le hr
  let := hA.2
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hlo := Representation.JankoTwo.SmallBinaryDegrees.involution_displacement_of_cubic_bound
    ρ e h.faithful h.irreducible (fun τ hf hi =>
      Representation.JankoTwo.SmallBinaryDegrees.cubic_displacement_of_absolute_calculations
        Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.absoluteWindowCalculations_complete
        Representation.JankoTwo.SmallBinaryDegrees.cubicFixedSpaceCalculations τ hf hi h28)
    t ht1 ht2
  have hle := ChapterE.fixedCodim_mono ρ (zpowers_le.mpr ht)
  omega

/-- The original ambient J₂ source action satisfies the strict quadratic bound. -/
theorem quadraticRatio_gt_two
    (h : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting G))
    (hz : center (generalizedFitting G) = ⊥)
    (e : generalizedFitting G ≃* Carrier) : 2 < quadraticRatio ρ := by
  let eQ := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e
  obtain ⟨D⟩ := ChapterK.SporadicCatalogue.SourceFF.j2_marked_of_center_and_degree
    ρ (generalizedFitting G) h ⟨eQ⟩ hz (finrank_eq_twelve h hz e)
  exact D.two_lt_quadraticRatio (ChapterK.JankoTwo.NaturalLocalAction.b46RootFacts _)
    ChapterK.JankoTwo.NaturalLocalAction.b46LongRootModuleFacts_four

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.JankoTwoSource
