module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-!
# Discharge the R3 premise of the exact long-word assembly

The seven proved numerical products supply `last_products_of_r2_r3`.
R2 and the shared, first and middle batches remain explicit premises. The
parent last-products owner retains R2 discharge and final assembly, and the
long-word owner retains the other three batches. This application does not
assert the full relator family before those independent premises are proved.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
open Certificates

/-- R3 is certified; this assembly retains the independent R2 branch. -/
theorem last_products_of_r2
    (hr2 : ∀ i : Fin 46, 34 ≤ i.val → i.val < 39 → ProductCheck i) :
    ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i :=
  last_products_of_r2_r3 hr2 r3_products

/-- Apply the exact source circuit with its R3 premise discharged. -/
theorem relations_of_r3_and_batches
    (hshared : ∀ i : Fin 46, i.val < 17 → ProductCheck i)
    (hfirst : ∀ i : Fin 46, 17 ≤ i.val → i.val < 26 → ProductCheck i)
    (hmiddle : ∀ i : Fin 46, 26 ≤ i.val → i.val < 34 → ProductCheck i)
    (hr2 : ∀ i : Fin 46, 34 ≤ i.val → i.val < 39 → ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 :=
  relations_of_batches hshared hfirst hmiddle (last_products_of_r2 hr2)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
