module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.Sample
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordSeven
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordEight

/-!
# Certified products for the first two long HS words

Source word 7 needs gates 17--20, ending in identity candidate 22. Source word
8 needs gates 21--25, ending in identity candidate 27. Their numerical checks
are independent. Each imported branch certifies all 896 rows of its fixed
products. Splitting at gate 21 combines them into the unconditional
`first_products`, without interpreting earlier candidates as words.

The exact words and circuit are documented in `LongWords/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-- Combine the two independent source-word gate families. -/
theorem first_products_of_words
    (hseven : ∀ i : Fin 46, 17 ≤ i.val → i.val < 21 → ProductCheck i)
    (height : ∀ i : Fin 46, 21 ≤ i.val → i.val < 26 → ProductCheck i) :
    ∀ i : Fin 46, 17 ≤ i.val → i.val < 26 → ProductCheck i := by
  intro i hlo hhi
  by_cases h : i.val < 21
  · exact hseven i hlo h
  · exact height i (by omega) hhi

/-- All nine fixed matrix products completing source words 7 and 8. -/
theorem first_products :
    ∀ i : Fin 46, 17 ≤ i.val → i.val < 26 → ProductCheck i :=
  first_products_of_words FirstTwo.word_seven_products FirstTwo.word_eight_products

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
