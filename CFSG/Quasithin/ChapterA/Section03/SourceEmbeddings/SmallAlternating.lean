module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.GroupTheory.SolvableSylowOvergroups

/-!
# The small alternating containing families in A.3.12

Proper full-Sylow overgroups in A₅ and A₆ are solvable. Perfect central
covers inherit this property through their literal central quotient, so
3.A₆ has the same non-enlargement conclusion. Restricting the original
full Sylow to the containing component then forces equality.

Source: Aschbacher–Smith A.3.12 and C.5.13, printed pp.47–48,162–163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

theorem eq_of_small_alternating_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hmodel : IsAlternating L 5 ∨ IsAlternating L 6 ∨ IsAlternatingCover L 6) : B = L := by
  apply eq_of_solvable_sylow_overgroups T hB hL hBL
  rcases hmodel with h | h | h
  · obtain ⟨e⟩ := h
    exact SolvableSylowOvergroups.of_equiv e (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP)
  · obtain ⟨e⟩ := h
    exact SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable
  · obtain ⟨hq, _, ⟨e⟩⟩ := h
    let := hq
    exact SolvableSylowOvergroups.of_central_quotient (QuotientGroup.mk' (center L))
      (QuotientGroup.mk'_surjective _) (by simp)
      (SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable)

/-- The full A.3.12 conclusion, including uniqueness, for these three
small alternating containing models. -/
theorem conclusion_of_small_alternating_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hmodel : IsAlternating L 5 ∨ IsAlternating L 6 ∨ IsAlternatingCover L 6) :
    Chapter1.Section02.A312Conclusion B := by
  have he := eq_of_small_alternating_containing_component T hB hL hBL hmodel
  refine ⟨L, hL, hBL, ?_, Chapter1.Section02.A312Embedding.one he⟩
  intro D hD hBD
  exact (hL.eq_of_le hD (he ▸ hBD)).symm
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
