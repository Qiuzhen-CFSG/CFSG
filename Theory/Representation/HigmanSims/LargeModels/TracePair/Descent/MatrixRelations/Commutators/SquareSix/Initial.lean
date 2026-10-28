module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Product.Rows000
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Product.Rows112
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Product.Rows224
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Product.Rows336
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Product.Rows448
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Product.Rows560
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Product.Rows672
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Product.Rows784
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Square.Rows000
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Square.Rows112
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Square.Rows224
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Square.Rows336
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Square.Rows448
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Square.Rows560
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Square.Rows672
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Initial.Square.Rows784
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Sample

/-!
# The initial two products for the HS squared-generator commutator

Kernel-checked row certificates prove the literal products rows07 · rows03 = C
and C · C = D over Four. The first square certificate covers rows 0–879 and
reuses `square_tail_checked` for rows 880–895. No interpretation of the input
matrices as generator words is assumed.

Source: the retained HSG1-f4r896aB0 matrices and `Descent/source/HSG1-P1.M`,
(a,b²)⁶. See `Initial/source/README.md` for the bounded checking procedure.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix
open Certificates.OrbitSpans.RowChecks

private theorem checked0 : CheckedRange (rowCheck 0) 0 896 :=
  checkedRange_append (rowCheck 0) 0 112 784 Initial.Product.rows000 (
  checkedRange_append (rowCheck 0) 112 112 672 Initial.Product.rows112 (
  checkedRange_append (rowCheck 0) 224 112 560 Initial.Product.rows224 (
  checkedRange_append (rowCheck 0) 336 112 448 Initial.Product.rows336 (
  checkedRange_append (rowCheck 0) 448 112 336 Initial.Product.rows448 (
  checkedRange_append (rowCheck 0) 560 112 224 Initial.Product.rows560 (
  checkedRange_append (rowCheck 0) 672 112 112 Initial.Product.rows672 (
  Initial.Product.rows784)))))))

private theorem checked1 : CheckedRange (rowCheck 1) 0 896 :=
  checkedRange_append (rowCheck 1) 0 112 784 Initial.Square.rows000 (
  checkedRange_append (rowCheck 1) 112 112 672 Initial.Square.rows112 (
  checkedRange_append (rowCheck 1) 224 112 560 Initial.Square.rows224 (
  checkedRange_append (rowCheck 1) 336 112 448 Initial.Square.rows336 (
  checkedRange_append (rowCheck 1) 448 112 336 Initial.Square.rows448 (
  checkedRange_append (rowCheck 1) 560 112 224 Initial.Square.rows560 (
  checkedRange_append (rowCheck 1) 672 112 112 Initial.Square.rows672 (
  checkedRange_append (rowCheck 1) 784 96 16 Initial.Square.rows784 (
  square_tail_checked))))))))

/-- Both fixed products, with every row and column certified over the original field. -/
theorem initial_products : ProductCheck 0 ∧ ProductCheck 1 :=
  ⟨productCheck_of_range 0 checked0, productCheck_of_range 1 checked1⟩

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix
