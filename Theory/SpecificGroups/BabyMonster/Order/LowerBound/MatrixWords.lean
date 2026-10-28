module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.DataA
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.DataB
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.Words
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# A shared matrix interface for the Baby Monster image certificates

The matrices are precisely the ATLAS data `BG1-f2r4370B0`, with provenance in
`source/README.md`. The ambient group is the unit group of the full binary
matrix algebra. The two standard generators become units once their square
and cube identities are proved; their inverses are then explicit.

This separates the two substantial calculations required for the order lower
bound. One must prove the two matrix power identities and every presentation
relation for `matrixGenerators`. Independently, one must bound the cardinality
of `matrixImage` below. The power identities are explicit premises here, to be
discharged by the concrete relation certificate when assembling the result.
There is no assumption identifying the matrix group with a named simple group.
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound

/-- The matrix algebra of the binary ATLAS representation. -/
abbrev AtlasMatrix := Matrix (Fin 4370) (Fin 4370) (ZMod 2)

/-- The first source matrix, with unchanged row and column convention. -/
def atlasA : AtlasMatrix := fun i j => if (atlasARow i).testBit j.val then 1 else 0

/-- The second source matrix, with unchanged row and column convention. -/
def atlasB : AtlasMatrix := fun i j => if (atlasBRow i).testBit j.val then 1 else 0

/-- The finite ambient group used for the two certificates. -/
abbrev MatrixGroup := AtlasMatrixˣ

instance matrixGroupFinite : Finite MatrixGroup := inferInstance

/-- The first generator with its explicit inverse, conditional on the square check. -/
def standardA (ha : atlasA ^ 2 = 1) : MatrixGroup where
  val := atlasA
  inv := atlasA
  val_inv := by simpa only [pow_two] using ha
  inv_val := by simpa only [pow_two] using ha

/-- The second generator with its explicit inverse, conditional on the cube check. -/
def standardB (hb : atlasB ^ 3 = 1) : MatrixGroup where
  val := atlasB
  inv := atlasB ^ 2
  val_inv := by simpa only [pow_succ'] using hb
  inv_val := by simpa only [pow_succ] using hb

@[simp] theorem standardA_val (ha : atlasA ^ 2 = 1) :
    (standardA ha : AtlasMatrix) = atlasA := rfl

@[simp] theorem standardB_val (hb : atlasB ^ 3 = 1) :
    (standardB hb : AtlasMatrix) = atlasB := rfl

/-- The eleven Table 1 words in the fixed source matrices. -/
def matrixGenerators (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    Generator → MatrixGroup := generatorWords (standardA ha) (standardB hb)

/-- The exact subgroup whose cardinality must be certified. -/
def matrixImage (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) : Subgroup MatrixGroup :=
  Subgroup.closure (Set.range (matrixGenerators ha hb))

/-- Transfer the two concrete certificates to the fixed presentation.
Both the relations and the image-size bound remain explicit obligations. -/
theorem card_ge_of_matrix_certificates [Finite Carrier]
    (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (hrelations : Relations (matrixGenerators ha hb))
    (hsize : expectedOrder ≤ Nat.card (matrixImage ha hb)) :
    expectedOrder ≤ Nat.card Carrier :=
  hsize.trans (card_generated_le hrelations)

end BabyMonster.OrderLowerBound
