module

public import CFSG.Quasithin.ChapterK.Section01To04.OddCharacteristic.SourceSmallLinearThree
public import CFSG.Quasithin.ChapterK.Section01To04.OddCharacteristic.SourceSmallLinearTwentyFive
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuFamily

/-!
# Odd linear exclusions on the literal chosen orbit

The K.2 exclusions apply to the unchanged orbit representation and component.
The applications under the original local hypotheses construct Chapter K's
source domain using the proved invariant-seed argument. They discharge both
small linear alternatives of the existing odd-family sieve.

Source: Aschbacher--Smith K.2, printed p.453, applied in 3.2.9 and 12.2.2.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original orbit component cannot have central quotient PSL₂(25). -/
theorem sourceOrbit_not_pslTwo_twentyFive
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent) :
    ¬ ClassicalGroup.IsPSL (D.orbitComponent ⧸ center D.orbitComponent) 2 25 :=
  ChapterK.OddCharacteristic.not_pslTwo_twentyFive hs

/-- The original orbit component cannot have central quotient PSL₃(3). -/
theorem sourceOrbit_not_pslThree_three
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent) :
    ¬ ClassicalGroup.IsPSL (D.orbitComponent ⧸ center D.orbitComponent) 3 3 :=
  ChapterK.OddCharacteristic.not_pslThree_three hs

/-- Discharge the Chapter K premises from the actual invariant-seed branch. -/
theorem sourceOrbit_not_pslThree_three_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hVW : V = D.sourceOrbit) :
    ¬ ClassicalGroup.IsPSL (D.orbitComponent ⧸ center D.orbitComponent) 3 3 :=
  D.sourceOrbit_not_pslThree_three (D.sourceOrbit_chapterK_of_many h hmany hnon hVW)

/-- The PSL₂(25) application also discharges every Chapter K source premise. -/
theorem sourceOrbit_not_pslTwo_twentyFive_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hVW : V = D.sourceOrbit) :
    ¬ ClassicalGroup.IsPSL (D.orbitComponent ⧸ center D.orbitComponent) 2 25 :=
  D.sourceOrbit_not_pslTwo_twentyFive (D.sourceOrbit_chapterK_of_many h hmany hnon hVW)

/-- The complete odd-catalogue branch of the sieve on this same chosen orbit. -/
theorem sourceOrbit_families_of_odd
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hm : ChapterA.Section02.IsTheoremCOddModel
      (D.orbitComponent ⧸ center D.orbitComponent)) :
    Chapter7.NormalizedSource.NonMathieuAssembly.SourceFamilies hs := by
  rcases Chapter7.NormalizedSource.NonMathieuFamily.families_or_small_odd hs hnon hm with
    hf | h25 | h3
  · exact hf
  · exact (D.sourceOrbit_not_pslTwo_twentyFive hs h25).elim
  · exact (D.sourceOrbit_not_pslThree_three hs h3).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
