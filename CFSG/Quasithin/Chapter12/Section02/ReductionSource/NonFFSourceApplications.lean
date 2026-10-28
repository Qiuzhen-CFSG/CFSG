module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesComplete
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitMarking

/-!
# The normalized source implication in the seven-case Chapter 12 consumer

The proved source 3.2.5 theorem supplies its literal marked alternatives.
Conditional normalized 7.0.1 and the original rank-one exit give FF on the
full orbit: the rank-one comparison recovers L/O2(L) from the same marked
orthogonal action, without identifying the seed and orbit. The complete
FF doubled marking then feeds 12.1.11. Only after excluding that case does
the existing module consumer identify the seed with the orbit and obtain
the seven original module alternatives.

The doubled non-FF and Mathieu source implications remain explicit with
`qt-d-1222-nonff-doubled` and `qt-d-1222-nonff-mathieu`. The rank-one,
nonbinary natural and ambient doubled-natural exits retain their owners
`qt-d-1222-rankone-module`, `qt-d-1222-nonbinary-natural` and
`qt-d-1222-double-natural`. Final discharge of all five inputs belongs to
`qt-d-1222-modules`, and final source assembly to `qt-d-1222-source`.

Source: Aschbacher--Smith, 3.2.5, 6.2.20, 7.0.1, 11.0.1, 12.1.11 and
12.2.2, printed pp.580, 691, 695, 759--760 and 794--796.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter12.Section01.DoubleNaturalSource

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Apply the normalized source implication and the exact rank-one exit
to the full chosen orbit. Source 3.2.5 is supplied by its proved producer. -/
theorem sourceOrbit_ff_of_normalized_inputs_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hdoubled : D.MarkedDoubled →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model))
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module) :
    IsFFModule D.sourceOrbitNormalizerRepresentation :=
  D.orbit_ff_of_normalized_source_and_rankOne h hrank
    (D.sourceOrbit_ff_or_orthogonal_of_source_inputs_of_many h hmany
      (D.source325_of_many h hmany) hdoubled hmathieu)

/-- The actual seven-case consumer, with source 3.2.5, non-Mathieu
classification, orbit transport and the FF doubled marking discharged.
Every remaining input is an independent earlier-source implication. -/
theorem alternatives_of_normalized_inputs_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hdoubled : D.MarkedDoubled →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model))
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False)
    (hdouble : ∀ n, DoubledBranch T L V n → False) : ModuleAlternatives1222 D :=
  D.alternatives_of_source_inputs_of_many h hmany (D.source325_of_many h hmany)
    (Or.inl (D.sourceOrbit_ff_of_normalized_inputs_of_many h hmany hdoubled hmathieu hrank))
    hrank hnonbinary hdouble

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
