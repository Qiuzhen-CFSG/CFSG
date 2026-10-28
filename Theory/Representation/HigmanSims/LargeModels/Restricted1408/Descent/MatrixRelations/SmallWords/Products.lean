module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.Checker
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.B2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ab
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ab2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ab4
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ab8
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ab10
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Abb
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Abb2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Abb4
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Abb5
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ai
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Comm
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Comm2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Comm4
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ai2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Mixed
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Mixed2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Aii
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.SquareComm
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.SquareComm2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.SquareComm3

/-!
# Shared finite products for the first seven source relations

Twenty-nine ordinary matrix products suffice for source clauses 0–6. Powers
of AB and AB² are shared, as are AI and its square, where I is the unchanged
candidate inverse matrix. These are raw matrix equations: no invertibility,
presentation relation, or density assertion is assumed.

The three structures below separate independent numerical certificate families.
Their fields are still proof obligations. `smallWords_of_products` in the parent
module uses every family to obtain the literal `Checker.matrixWord` statements.
See `source/README.md` and the retained ATLAS HSG1-P1.M.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts
open Thompson.BinaryMatrix

def b2 : Mat := decode 1408 b2Rows

def ab : Mat := decode 1408 abRows

def ab2 : Mat := decode 1408 ab2Rows

def ab4 : Mat := decode 1408 ab4Rows

def ab8 : Mat := decode 1408 ab8Rows

def ab10 : Mat := decode 1408 ab10Rows

def abb : Mat := decode 1408 abbRows

def abb2 : Mat := decode 1408 abb2Rows

def abb4 : Mat := decode 1408 abb4Rows

def abb5 : Mat := decode 1408 abb5Rows

def ai : Mat := decode 1408 aiRows

def comm : Mat := decode 1408 commRows

def comm2 : Mat := decode 1408 comm2Rows

def comm4 : Mat := decode 1408 comm4Rows

def ai2 : Mat := decode 1408 ai2Rows

def mixed : Mat := decode 1408 mixedRows

def mixed2 : Mat := decode 1408 mixed2Rows

def aii : Mat := decode 1408 aiiRows

def squareComm : Mat := decode 1408 squareCommRows

def squareComm2 : Mat := decode 1408 squareComm2Rows

def squareComm3 : Mat := decode 1408 squareComm3Rows

/-- Independent finite product obligations for this source-word family. -/
structure GeneratorProducts : Prop where
  a_a : matrixA * matrixA = 1
  b_b : matrixB * matrixB = b2
  b2_b2 : b2 * b2 = inverseMatrix
  inverse_b : inverseMatrix * matrixB = 1

/-- Independent finite product obligations for this source-word family. -/
structure AlternatingProducts : Prop where
  a_b : matrixA * matrixB = ab
  ab_ab : ab * ab = ab2
  ab2_ab2 : ab2 * ab2 = ab4
  ab4_ab4 : ab4 * ab4 = ab8
  ab8_ab2 : ab8 * ab2 = ab10
  ab10_ab : ab10 * ab = 1
  ab_b : ab * matrixB = abb
  abb_abb : abb * abb = abb2
  abb2_abb2 : abb2 * abb2 = abb4
  abb4_abb : abb4 * abb = abb5
  abb5_abb5 : abb5 * abb5 = 1

/-- Independent finite product obligations for this source-word family. -/
structure CommutatorProducts : Prop where
  a_inverse : matrixA * inverseMatrix = ai
  ai_ab : ai * ab = comm
  comm_comm : comm * comm = comm2
  comm2_comm2 : comm2 * comm2 = comm4
  comm4_comm : comm4 * comm = 1
  ai_ai : ai * ai = ai2
  ai2_ab2 : ai2 * ab2 = mixed
  mixed_mixed : mixed * mixed = mixed2
  mixed2_mixed : mixed2 * mixed = 1
  ai_inverse : ai * inverseMatrix = aii
  aii_abb : aii * abb = squareComm
  squareComm_squareComm : squareComm * squareComm = squareComm2
  squareComm2_squareComm : squareComm2 * squareComm = squareComm3
  squareComm3_squareComm3 : squareComm3 * squareComm3 = 1

/-- A literal row certificate gives exactly the corresponding matrix product. -/
theorem mul_of_rows (x y z : Array Nat) (hy : y.size = 1408)
    (h : ∀ i : Fin 1408, PackedBinaryRows.listProduct x[i.val]! 0 y.toList = z[i.val]!) :
    decode 1408 x * decode 1408 y = decode 1408 z := by
  apply decode_mul
  intro i
  rw [PackedBinaryRows.rowProduct_eq_listProduct _ _ _ hy]
  exact h i

/-- The identity endpoint is checked against every coordinate row. -/
theorem mul_one_of_rows (x y : Array Nat) (hy : y.size = 1408)
    (h : ∀ i : Fin 1408, PackedBinaryRows.listProduct x[i.val]! 0 y.toList = 2 ^ i.val) :
    decode 1408 x * decode 1408 y = 1 := by
  apply decode_mul_one
  intro i
  rw [PackedBinaryRows.rowProduct_eq_listProduct _ _ _ hy]
  exact h i

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts
