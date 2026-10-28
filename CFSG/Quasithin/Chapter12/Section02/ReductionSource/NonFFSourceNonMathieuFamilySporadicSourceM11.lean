module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuFamily
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceM11

/-!
# Removing M₁₁ from the literal chosen-orbit family sieve

The original orbit representation is faithful and irreducible on its actual
component. Transporting the equality with the generalized Fitting subgroup
puts precisely that action in Chapter K's cubic source domain. The unconditional
M₁₁ exclusion then removes the Mathieu-eleven alternative; the J₂ and HS
alternatives remain marked on the same quotient.

Source: Aschbacher--Smith, K.4 and 12.2.2, printed pp.457 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.NonMathieuAssembly
universe u

private theorem sporadic_j2_or_hs
    {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] {ρ : Representation (ZMod 2) A E} {Q : Subgroup A}
    (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnm : ¬ HasMathieuCentralQuotient Q)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (Q ⧸ center Q)) :
    Nonempty (Q ⧸ center Q ≃* KnownSimple.SporadicName.j2.Carrier) ∨
      Nonempty (Q ⧸ center Q ≃* KnownSimple.SporadicName.hs.Carrier) := by
  rcases NonMathieuFamily.sporadic_reduction hs hnm hm with h11 | h2 | hhs
  · exact (ChapterK.SporadicCatalogue.not_m11_of_rankOne_source hs h11).elim
  · exact Or.inl h2
  · exact Or.inr hhs

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual chosen orbit component cannot have central quotient M₁₁.
This uses the cubic source hypotheses, with no FF premise. -/
theorem sourceOrbit_not_m11
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (he : Nonempty (D.orbitComponent ⧸ center D.orbitComponent ≃*
      KnownSimple.SporadicName.m11.Carrier)) : False := by
  exact ChapterK.SporadicCatalogue.not_m11_of_rankOne_source hs he

/-- After M₁₁ is excluded, the marked non-Mathieu sporadic alternatives on
the original chosen orbit are J₂ and HS. -/
theorem sourceOrbit_sporadic_j2_or_hs
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel
      (D.orbitComponent ⧸ center D.orbitComponent)) :
    Nonempty (D.orbitComponent ⧸ center D.orbitComponent ≃*
      KnownSimple.SporadicName.j2.Carrier) ∨
    Nonempty (D.orbitComponent ⧸ center D.orbitComponent ≃*
      KnownSimple.SporadicName.hs.Carrier) :=
  sporadic_j2_or_hs hs hnm hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
