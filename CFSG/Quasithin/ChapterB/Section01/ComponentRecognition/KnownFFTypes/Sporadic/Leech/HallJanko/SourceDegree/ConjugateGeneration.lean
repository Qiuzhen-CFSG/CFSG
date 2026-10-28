module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko.SourceDegree.Reduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.FourConjugateGeneration

/-!
# Four-conjugate generation for the source Hall--Janko action

An explicit trivial-center hypothesis turns the source central-quotient marking
into an isomorphism of the actual generalized Fitting subgroup with J₂ and
supplies its simplicity. The intrinsic generation theorem then applies to all
ambient involutions, including outer ones, with conjugators in the original G.
This discharges the conjugate-generation premise of the degree estimate.
The source cover/degree owner retains the center and numerical rank obligations.

Source: Guralnick--Malle, Classification of 2F-modules I, (2.5)--(2.6) and
Proposition 5.1, J₂ paragraph; Aschbacher--Smith, Chapter K, pp.457--458.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] {ρ : Representation (ZMod 2) G W}

/-- The source action satisfies the four-conjugate bound once the cover is killed. -/
theorem SourceHypotheses.involution_conjugate_generation_of_center_eq_bot
    (h : SourceHypotheses ρ) (hc : center (generalizedFitting G) = ⊥) :
    InvolutionConjugateGenerationBound (generalizedFitting G) 4 := by
  let := h.fitting_simple_of_center_eq_bot hc
  obtain ⟨e⟩ := h.fitting_equiv_of_center_eq_bot hc
  exact _root_.Sporadic.LeechRelated.J2.FourConjugateGeneration.involution_conjugate_generation_bound e

/-- Actual application to the source degree estimate, retaining only the
independently produced center and automorphism-rank premises. -/
theorem SourceHypotheses.finrank_le_thirty_two_of_center_eq_bot_and_rank
    [FiniteDimensional (ZMod 2) W]
    (h : SourceHypotheses ρ) (hc : center (generalizedFitting G) = ⊥)
    (hr : primeRank 2 (MulAut _root_.Sporadic.LeechRelated.J2.Carrier) ≤ 4) :
    Module.finrank (ZMod 2) W ≤ 32 :=
  h.finrank_le_thirty_two_of_model_bounds hr
    (h.involution_conjugate_generation_of_center_eq_bot hc)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko
