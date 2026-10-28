module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.ReeF4.SourceFinite
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.Source

/-!
# Complete Ree exclusion for the original B.1 component action

The proved model and central-cover bounds supply the absolute gap on the
original component. The conclusion retains its original generalized Fitting
subgroup, representation and central quotient marking, with no auxiliary
representation-classification or algebraic-group premise.
Source: Aschbacher--Smith B.1; Guralnick--Malle II, Lemma 8.8.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.ReeF4
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
universe u v
variable {H : Type u} [Group H] [Finite H] (N : Subgroup H)
  [N.Normal] [IsQuasisimple N]

/-- The genuine Ree component has no FF module in the original source setting. -/
theorem not_ff {m : ℕ} (hm : 1 ≤ m)
    (hF : generalizedFitting H = N) (e : N ⧸ center N ≃* _root_.ReeF4.Model m)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ]
    [IsIrreducible (ρ.comp N.subtype)] (hf : Function.Injective ρ) : ¬ IsFFModule ρ :=
  not_ff_of_absoluteGap N ρ hf (absoluteGap_of_involution_bound N hm hF e
    (_root_.ReeF4.ElementaryTwoBound.card_le m hm)
    (_root_.ReeF4.FixedSpaceEstimate.coverInvolutionBound_source hm))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.ReeF4
