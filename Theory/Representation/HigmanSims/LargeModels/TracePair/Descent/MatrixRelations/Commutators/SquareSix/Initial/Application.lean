module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix

/-!
# Using the two initial HS commutator products

This application discharges exactly the first two numerical premises of
`square_commutator_six_of_products`. The three common generator-word products
and the two terminal numerical products remain explicit. Their assembly owner
supplies these independent certificates for the unconditional source relation.
Source: `Descent/source/HSG1-P1.M`, (a,b²)⁶.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates Commutators.SquareSix

/-- The initial products are certified; only the common and terminal gates remain. -/
theorem square_commutator_six_of_common_and_terminal_products
    (hb2 : LongWords.ProductCheck 0)
    (hab2 : LongWords.ProductCheck 1)
    (hab3 : LongWords.ProductCheck 5)
    (he : Commutators.SquareSix.ProductCheck 2)
    (hi : Commutators.SquareSix.ProductCheck 3) :
    positiveRelation (Packed.eval 896 generatorRowsA)
      (Packed.eval 896 generatorRowsB) 6 = 1 :=
  square_commutator_six_of_products hb2 hab2 hab3
    initial_products.1 initial_products.2 he hi

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
