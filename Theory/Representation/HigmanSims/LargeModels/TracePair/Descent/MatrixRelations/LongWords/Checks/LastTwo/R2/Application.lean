module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-!
# Discharge the R2 premise of the exact long-word assembly

The proved numerical R2 family supplies `last_products_of_r2_r3`. Its R3 premise
is retained explicitly, as are the shared, first and middle batches of
`relations_of_batches`. Their existing producers and the parent last-products
owner retain final discharge. This module does not assert the complete long
relator family before those independent numerical premises are proved.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
open Certificates

/-- R2 is certified; only the independent R3 branch remains in this assembly. -/
theorem last_products_of_r3
    (hr3 : ∀ i : Fin 46, 39 ≤ i.val → ProductCheck i) :
    ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i :=
  last_products_of_r2_r3 r2_products hr3

/-- Apply the exact source circuit with its R2 premise discharged. -/
theorem relations_of_r2_and_batches
    (hshared : ∀ i : Fin 46, i.val < 17 → ProductCheck i)
    (hfirst : ∀ i : Fin 46, 17 ≤ i.val → i.val < 26 → ProductCheck i)
    (hmiddle : ∀ i : Fin 46, 26 ≤ i.val → i.val < 34 → ProductCheck i)
    (hr3 : ∀ i : Fin 46, 39 ≤ i.val → ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 :=
  relations_of_batches hshared hfirst hmiddle (last_products_of_r3 hr3)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
