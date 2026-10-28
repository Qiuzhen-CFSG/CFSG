module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.OriginalSource

/-!
# The source 37 input to rank-two cover reduction

The completed original source 37 supplies the uniform alternatives on every outside overgroup. The component orbit and conjugate span agree by their universal properties.
Source: Aschbacher–Smith, 15.3.38, printed p.1137.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open ChapterA.Section05To06 LocalCover LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]

/-- Uniform earlier data from the completed original37, with the orbit and
span conventions identified by their universal properties. -/
theorem source_inputs_of_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I) :
    SourceInputs d := by
  apply source_inputs_from_selection hG d hempty hM hu hmany h13 hI htwo
  intro J hJ K hKJ hK
  have h37 := Candidates.RankTwoSource.source_lemma_15_3_37_from_selection
    hG d hempty hM hu hmany h13 hI htwo hJ hKJ hK
  have he : componentOrbit K d.S = localSpan K d.S :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer K d.S _
      (le_conjugateSpanBy K d.S) (le_normalizer_conjugateSpanBy K d.S))
      (conjugateSpanBy_le (le_componentOrbit K d.S) (le_normalizer_componentOrbit K d.S))
  rw [he] at h37
  rcases h37 with hfirst | hsecond | hthird
  · exact Or.inl hfirst
  · exact Or.inr (Or.inl hsecond.centralizer_three_part)
  · exact Or.inr (Or.inr hthird)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
