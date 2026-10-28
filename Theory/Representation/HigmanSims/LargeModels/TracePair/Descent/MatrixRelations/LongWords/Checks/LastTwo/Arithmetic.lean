module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Products
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.RowChecks.Checker

/-!
# Bounded numerical certificates for the last two HS relators

The existing division-based row checker computes precisely `Packed.rowProduct`.
Here it is applied to the actual operands and output of a long-word gate.
Consecutive checked ranges cover all 896 rows; `productCheck_of_checked` then
proves the required matrix equality with no word-interpretation assumptions.
Numerical range certificates are separate obligations, not supplied here.

Source: `LongWords/source/circuit.json` and the unchanged HSG1-f4r896aB0 rows.
The checker and its correctness theorem are reused from the completed
`Certificates.OrbitSpans.RowChecks.Checker` development.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.LastTwoArithmetic
open Certificates
open Certificates.OrbitSpans.RowChecks

/-- One Boolean equality, using the literal ordered operands of gate `i`. -/
def rowCheck (i : Fin 46) (r : ℕ) : Bool :=
  directProductFrom ((rowsAt (inputs i).1).getD r (0, 0))
    (rowsAt (inputs i).2) 0 == (rowsAt (i.val + 2)).getD r (0, 0)

/-- All rows of the numerical gate suffice for its exact matrix product. -/
theorem productCheck_of_checked (i : Fin 46)
    (h : CheckedRange (rowCheck i) 0 896) : ProductCheck i := by
  apply productCheck_of_rows i
  intro r
  have he := eq_of_beq (h r.val (Nat.zero_le _) r.isLt)
  simpa only [rowCheck, directProductFrom_eq, Packed.rowProduct] using he

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.LastTwoArithmetic
