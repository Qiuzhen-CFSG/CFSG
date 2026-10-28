module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-!
# Applying the R2 and R3 certificates to the six long HS words

The twelve numerical gates in `last_products` discharge the final batch in
`relations_of_batches`. The shared, first and middle batches stay explicit;
the full long-word assembly owner must supply them. This applies the literal
ordered circuit from `LongWords/source/circuit.json`, including both identity
outputs for R2 and R3 in `Descent/source/HSG1-P1.M`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
open Certificates

/-- The final numerical batch is discharged; only the other three batches
remain before the six long source words are certified. -/
theorem relations_of_last_and_batches
    (hshared : ∀ i : Fin 46, i.val < 17 → ProductCheck i)
    (hfirst : ∀ i : Fin 46, 17 ≤ i.val → i.val < 26 → ProductCheck i)
    (hmiddle : ∀ i : Fin 46, 26 ≤ i.val → i.val < 34 → ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 :=
  relations_of_batches hshared hfirst hmiddle last_products

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
