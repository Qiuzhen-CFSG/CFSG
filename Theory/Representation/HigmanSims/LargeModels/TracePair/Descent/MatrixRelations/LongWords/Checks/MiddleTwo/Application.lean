module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-!
# Application of the certified middle products to the literal six-word circuit

`relations_of_middle_products` discharges all eight middle gates in the actual
`relations_of_batches` consumer. The other three batches remain explicit for
the long-relator assembly owner. The original conditional tail application is
preserved. Neither application asserts the unconditional six relators.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
open Certificates

/-- Apply the complete middle batch to the literal positive words, leaving
only the other three independently checked batches to the final assembly. -/
theorem relations_of_middle_products
    (hshared : ∀ i : Fin 46, i.val < 17 → ProductCheck i)
    (hfirst : ∀ i : Fin 46, 17 ≤ i.val → i.val < 26 → ProductCheck i)
    (hlast : ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 :=
  relations_of_batches hshared hfirst middle_products hlast

theorem relations_of_middle_remaining
    (hother : ∀ i : Fin 46, 26 ≤ i.val → i.val < 33 → ProductCheck i)
    (hhead : ∀ r : Fin 896, r.val < 880 →
      Packed.rowProduct (rows18.getD r.val (0,0)) rows18 =
        identityRows.getD r.val (0,0))
    (hshared : ∀ i : Fin 46, i.val < 17 → ProductCheck i)
    (hfirst : ∀ i : Fin 46, 17 ≤ i.val → i.val < 26 → ProductCheck i)
    (hlast : ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 :=
  relations_of_batches hshared hfirst (middle_products_of_remaining hother hhead) hlast

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
