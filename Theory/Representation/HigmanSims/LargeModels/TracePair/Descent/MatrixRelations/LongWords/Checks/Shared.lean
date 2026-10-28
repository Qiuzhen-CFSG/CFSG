module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Gate00
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.RightB
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.RightSquare
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.RightABSquare
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed

/-!
# Certification of the seventeen shared HS long-word products

Gate zero is the checked product of the literal second generator with itself.
The other sixteen fixed products are grouped by their right operand, allowing
coordinate-image certificates to be reused. Combining those four checked
families proves `shared_products` without any numerical or representation
premises. Every gate uses the literal candidate matrices in `Products.lean`.

The exact ordered circuit and the retained HSG1-f4r896aB0 source are documented
in `LongWords/source/README.md` and `TracePair/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-- The first shared gate is the literal B² candidate. -/
theorem shared_product_zero : ProductCheck 0 := Shared.Gate00.product_checked

/-- Assemble four fixed numerical families with the certified first gate. -/
theorem shared_products_of_remaining
    (hB : ∀ i : Fin 46, i = 2 ∨ i = 5 ∨ i = 12 → ProductCheck i)
    (hB2 : ∀ i : Fin 46, i = 1 ∨ i = 6 ∨ i = 9 ∨ i = 15 → ProductCheck i)
    (hAB2 : ∀ i : Fin 46, i = 3 ∨ i = 11 ∨ i = 13 ∨ i = 14 → ProductCheck i)
    (hmixed : ∀ i : Fin 46, i = 4 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 16 → ProductCheck i) :
    ∀ i : Fin 46, i.val < 17 → ProductCheck i := by
  intro i hi
  have h : i = 0 ∨ (i = 2 ∨ i = 5 ∨ i = 12) ∨
      (i = 1 ∨ i = 6 ∨ i = 9 ∨ i = 15) ∨
      (i = 3 ∨ i = 11 ∨ i = 13 ∨ i = 14) ∨
      (i = 4 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 16) := by omega
  rcases h with rfl | h | h | h | h
  · exact shared_product_zero
  · exact hB i h
  · exact hB2 i h
  · exact hAB2 i h
  · exact hmixed i h

/-- All seventeen shared products in the exact six-long-word circuit. -/
theorem shared_products : ∀ i : Fin 46, i.val < 17 → ProductCheck i :=
  shared_products_of_remaining shared_right_b_products shared_right_square_products
    shared_right_ab_square_products shared_mixed_products

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
