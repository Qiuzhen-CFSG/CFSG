module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalRemainingLargeSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableNormalization
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialMarkedConsumer

/-!
# Original full large-action normalization with every source branch supplied

The extraspecial source is impossible and the original decomposable source
now supplies its own normalization. Together with the existing Nine producer,
these discharge the original full large-action normalization interface at the
actual singleton centralizer. Rank-two resolution, subsequent large-action
exclusion, and 15.3.13 are not asserted here.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- Both remaining original normalization duties are supplied by their actual source proofs. -/
theorem original_remaining_full_normalization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    OriginalRemainingFullNormalizationAt T Mc := by
  intro _ _ M hM hne hJ h
  let := h.elementary
  dsimp only
  intro _ _ hremaining
  rcases hremaining with hextra | ⟨hq,U,c,d,s,π,hd,hp,hs,hdec,hfive⟩
  · exact h.extraspecial_full_centralizer_normalizes_thompsonFixed
      hG T hempty hM hmany hJ hu hne rfl hextra
  · exact h.decomposable_five_normalization
      hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive

/-- All original large full-action normalization branches are now unconditional source outputs. -/
theorem original_large_full_normalization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    OriginalLargeFullNormalizationAt T Mc :=
  original_large_full_normalization_of_remaining hG T hmany hempty hu
    (original_remaining_full_normalization hG T hmany hempty hu)

end CFSG.Quasithin.Chapter15
