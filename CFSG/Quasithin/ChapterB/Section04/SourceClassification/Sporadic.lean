module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwentyFour
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.HigmanSims
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwentyTwo
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwelve

/-!
# The genuine sporadic branch of B.4.2

Every entry of the complete eleven-group Theorem C sporadic catalogue is
excluded on the original faithful binary representation. The native M24
small-FF theorem discharges the last representation input. All central covers,
outer actions, vector spaces, and quotient markings are retained by the source
transport. Thus the sporadic alternative is impossible, and its literal B.4.2
consumer follows without any additional model or representation premise.

Source: Aschbacher–Smith B.4.2, printed p.86, and Chapter K.4, p.457.
-/

public section
namespace CFSG.Quasithin.ChapterB.SourceClassification
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open ChapterK.RankOne
open ChapterA.Section02
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The exact two native representation calculations suffice for the full
sporadic source exclusion. All other catalogue branches are discharged. -/
theorem sporadic_false_of_native
    (hn12 : ¬ IsFFModule ChapterH.Section10To12.M12Calculations.Ambient.automorphismRepresentation)
    (hn24 : ∀ σ : Representation (ZMod 2) Sporadic.Mathieu.M24 V,
      Function.Injective σ → σ.IsIrreducible → Module.finrank (ZMod 2) V ≤ 24 →
      ¬ IsFFModule σ)
    (h : SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (hm : IsTheoremCSporadicModel (L ⧸ center L)) : False := by
  rcases remaining_four_central_quotient h hff hm with h12 | h22 | h24 | hhs
  · exact not_ff_m12_of_native hn12 h h12 hff
  · exact not_ff_m22 h h22 hff
  · exact not_ff_m24_of_native_small hn24 h h24 hff
  · exact not_ff_hs h hhs hff

/-- The original source hypotheses leave only the actual M24 carrier. -/
theorem sporadic_quotient_m24 (h : SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (hm : IsTheoremCSporadicModel (L ⧸ center L)) :
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier) := by
  rcases remaining_four_central_quotient h hff hm with h12 | h22 | h24 | hhs
  · exact (not_ff_m12 h h12 hff).elim
  · exact (not_ff_m22 h h22 hff).elim
  · exact h24
  · exact (not_ff_hs h hhs hff).elim

/-- Ten sporadic branches are discharged. The sole remaining callback is the
native M24 small-module exclusion, on the same binary vector space. -/
theorem sporadic_false_of_m24_native
    (hn24 : ∀ σ : Representation (ZMod 2) Sporadic.Mathieu.M24 V,
      Function.Injective σ → σ.IsIrreducible → Module.finrank (ZMod 2) V ≤ 24 →
      ¬ IsFFModule σ)
    (h : SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (hm : IsTheoremCSporadicModel (L ⧸ center L)) : False :=
  not_ff_m24_of_native_small hn24 h (sporadic_quotient_m24 h hff hm) hff

/-- All eleven actual sporadic models are excluded under the original source
hypotheses, including every allowed central cover and ambient outer action. -/
theorem sporadic_false (h : SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (hm : IsTheoremCSporadicModel (L ⧸ center L)) : False :=
  not_ff_m24 h (sporadic_quotient_m24 h hff hm) hff

/-- The complete sporadic alternative in the literal B.4.2 action conclusion. -/
theorem sporadic_case (h : SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (hm : IsTheoremCSporadicModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  (sporadic_false h hff hm).elim

/-- The original best-offender domain supplies every source input to the
sporadic branch; no classification callback remains. -/
theorem sporadic_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : IsTheoremCSporadicModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  sporadic_case (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    ⟨A,hA.isOffender ρ⟩ hm

end CFSG.Quasithin.ChapterB.SourceClassification
