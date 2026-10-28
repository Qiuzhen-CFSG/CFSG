module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Terminal
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix

/-!
# Application of the two certified terminal HS products

The fixed identities D C = E and E² = I discharge the last two premises of
`square_commutator_six_of_products`. The common generator products and the
initial products defining C and D remain explicit and belong to their existing
producers. This is the literal positive relation at index six for the retained
HSG1-f4r896aB0 matrices over Four. Source: HSG1-P1.M, (a,b²)⁶.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates

theorem square_commutator_six_of_common_and_initial_products
    (hb2 : LongWords.ProductCheck 0)
    (hab2 : LongWords.ProductCheck 1)
    (hab3 : LongWords.ProductCheck 5)
    (hc : Commutators.SquareSix.ProductCheck 0)
    (hd : Commutators.SquareSix.ProductCheck 1) :
    positiveRelation (Packed.eval 896 generatorRowsA)
      (Packed.eval 896 generatorRowsB) 6 = 1 :=
  square_commutator_six_of_products hb2 hab2 hab3 hc hd
    Commutators.SquareSix.terminal_products.1 Commutators.SquareSix.terminal_products.2

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
