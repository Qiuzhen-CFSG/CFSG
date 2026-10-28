module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockAlternatingFiveApplication

/-!
# The original rank-one Baumann normalizer bound

If the Baumann normalizer escapes N_G(L), the original reduced module
forces the alternating-five branch of 5.1.2. The source selection and
ordinary exclusion give a constrained nonblock configuration containing L.
The alternating-five layer theorem makes this same component a block,
contradicting that configuration. This proves the bound for the original
Input and its original W, with no additional uniqueness or module premise.

Source: Aschbacher--Smith 5.1.7(1), pp.633--634, using the preceding
5.1.2 analysis and the original 4.3.2 containing-component argument.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- Source 5.1.7(1) for the original reduced rank-one input. -/
theorem Input.baumann_normalizer_le
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨_, _, c, hf, hb⟩ := h.original_nonblock_of_baumann_escape hout
  exact h.original_nonblock_false hout c hf hb

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
