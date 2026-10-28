module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-!
# Literal consumer of the first two HS word branches

This applies the certified first-word products to `relations_of_batches`,
discharging its gates 17--25 premise. The other three numerical families remain
explicit, so the six source relators still require those independent checks.
The original conditional branch application is retained as a reusable interface.
Source words and multiplication order are documented in `LongWords/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
open Certificates

/-- The two source-word branches feed the exact six-relator circuit. -/
theorem relations_of_first_word_batches
    (hshared : ∀ i : Fin 46, i.val < 17 → ProductCheck i)
    (hseven : ∀ i : Fin 46, 17 ≤ i.val → i.val < 21 → ProductCheck i)
    (height : ∀ i : Fin 46, 21 ≤ i.val → i.val < 26 → ProductCheck i)
    (hmiddle : ∀ i : Fin 46, 26 ≤ i.val → i.val < 34 → ProductCheck i)
    (hlast : ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 :=
  relations_of_batches hshared (first_products_of_words hseven height) hmiddle hlast

/-- Discharge the first two word branches in the exact six-relator circuit. -/
theorem relations_of_remaining_batches
    (hshared : ∀ i : Fin 46, i.val < 17 → ProductCheck i)
    (hmiddle : ∀ i : Fin 46, 26 ≤ i.val → i.val < 34 → ProductCheck i)
    (hlast : ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 :=
  relations_of_batches hshared first_products hmiddle hlast

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
