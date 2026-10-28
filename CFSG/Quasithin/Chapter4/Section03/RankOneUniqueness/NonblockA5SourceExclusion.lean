module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5StarIrreducibleRemainder
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5SymplecticExclusion
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5G2MovedExclusion
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceNaturalSevenStarTransport
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryComplete
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Baumann
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311

/-!
# Uniqueness over the original marked A₅ component

The actual C.2.7 moved section retains its action marking. Its symplectic
and G₂ rows contradict the original seed's cubic fixed vector. Its A₇ row
reconstructs a block on the original component. Thus the aligned nonblock
source is impossible. The proved source selection and ordinary/block
exclusions now give uniqueness over L itself, using the same chosen module
and original Sylow subgroup throughout.

Source: Aschbacher--Smith 4.3.2--10 and 13.3.2, pp.613--617,884--885.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The nonblock source is excluded from the actual original A₅ marking,
without a separate quotient or module-row selection hypothesis. -/
theorem Nonblock.false_of_original_a5_source
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (hb : ¬ ChapterC.IsBlock c.K) : False := by
  obtain ⟨hCO,s,hi,_,_,_,hs⟩ := Nonblock.a5_star_irreducible_remainder d c hf
  rcases hs with ⟨F,_,⟨a⟩⟩ | ⟨F,_,⟨a⟩⟩ | ⟨_,⟨a⟩,hr,hsplit,_⟩
  · exact Nonblock.not_symplectic_moved_action_of_a5 d c hf s.sectionData hi F a
  · exact Nonblock.not_g2_moved_cover_of_a5 d c hf s.sectionData hi F a
  · exact hb (c.block_of_natural_seven_star_row hf hCO s.sectionData a hr hsplit)

/-- Every maximal two-local overgroup of the original L is its full
normalizer. The genuine multiple-overgroup guard is retained. -/
theorem uniqueness_of_original_a5_context
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) := by
  have h := Chapter13.Section02.A5Outside.OriginalCentralization.rankOne_hypothesis d
  have hi := Chapter13.Section02.A5Outside.OriginalCentralization.rankOne_input_of_many d hmany
  exact uniqueness_of_nonblock_exclusion d.chosen
    (d.hypothesis.hypothesis1311.hypothesis1223 h.maximal_faithful h.quasisimple)
    hmany (by decide : 1 < 2) hi.linear
    (Nonblock.false_of_original_a5_source d)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
