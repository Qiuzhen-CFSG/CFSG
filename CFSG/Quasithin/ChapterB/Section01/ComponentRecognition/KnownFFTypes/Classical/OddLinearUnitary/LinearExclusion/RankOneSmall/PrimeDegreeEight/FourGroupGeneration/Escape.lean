module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.FourGroupGeneration.EscapeInput
public import Theory.SpecificGroups.PSL2.SmallPrimeFourGroup.NormalizerEscape

/-!
# Diagonal four-groups escape the low dihedral normalizer

For the four source primes, the centralizer of the marked inner involution
has more than eight elements. In the low dihedral normalizer its centralizer
has order at most four, so there is at most one four-group through that mark.
The actual automorphism four-group is self-centralizing; its normalizer fixing
the mark has at most eight elements. A centralizing inner conjugator therefore
moves it outside the dihedral normalizer.

This supplies exactly the geometric input consumed by
`fourGroupModelGeneration_of_normalizer_escape`; it imposes no additional
centralizer or generation hypothesis.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight

/-- The diagonal normalizer escape at all four small prime parameters. -/
theorem fourGroupNormalizerEscape (F : Type) [Field F] [Finite F] (p : ℕ)
    (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23) (hF : Nat.card F = p) :
    FourGroupNormalizerEscape F p := by
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  intro a b _ ha2 hb1 hb2 hmax hcard A hA hcardA _ hbA
  exact Theory.PSL2.SmallPrimeFourGroup.normalizer_escape
    F hp hF a b ha2 hb1 hb2 hmax hcard A hA hcardA hbA

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight
