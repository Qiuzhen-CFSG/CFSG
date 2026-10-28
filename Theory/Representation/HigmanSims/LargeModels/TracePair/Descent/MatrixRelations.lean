module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PositiveWords
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Trees
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Reencoding
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent

/-!
# Assembly of the finite degree-896 matrix relations

Positive matrix words give the two inverse witnesses and all thirteen literal
ATLAS group relators. The packed-row interpretation equations then preserve the
raw column matrices. This module applies that finite certificate to the actual
`markedActionOfRelators`, with presentation completeness still explicit.

The three checked word families and `Certificates.Reencoding` discharge every
finite matrix obligation in `certificate`. Its units have the raw published
matrices as values and satisfy all thirteen source relations, including R1--R3.
The marked-action application retains only `RelatorsPresentCarrier`; density
and trace are not used in this construction.

Source: HSG1-P1.M and HSG1-f4r896aB0, retained in the adjacent source directories.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates

/-- Finite packed identities and the two exact interpretation equations give
units on the published matrices, with all thirteen literal group relations. -/
def ofPackedRelations
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB)
    (hr : ∀ i : Fin 13, positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1) :
    MatrixRelatorCertificate :=
  ofPositiveRelations (by simpa only [hA, hB] using hr)

/-- Assemble three disjoint finite families. The order relations also supply
both inverse witnesses; no invertibility premise is retained. -/
def ofFamilies
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB)
    (hpower : ∀ i : Fin 13, i.val < 4 → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1)
    (hcomm : ∀ i : Fin 13, 4 ≤ i.val → i.val < 7 → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1)
    (hlong : ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1) :
    MatrixRelatorCertificate :=
  ofPackedRelations hA hB (by
    intro i
    by_cases hi : i.val < 4
    · exact hpower i hi
    · by_cases hj : i.val < 7
      · exact hcomm i (by omega) hj
      · exact hlong i (by omega))

/-- The literal degree-896 matrices are units satisfying all thirteen ATLAS
relators. The order checks construct their inverses, and the two re-encoding
theorems identify their values with the raw published matrices. -/
def certificate : MatrixRelatorCertificate :=
  ofFamilies generatorRowsA_eval generatorRowsB_eval
    power_relations commutator_relations long_relations

/-- Every finite matrix obligation for descent is discharged. -/
theorem nonempty_certificate : Nonempty MatrixRelatorCertificate :=
  ⟨certificate⟩

/-- Apply the complete matrix certificate to the actual carrier descent.
The independent carrier-presentation theorem remains explicit. -/
noncomputable def markedAction (hp : RelatorsPresentCarrier) : MarkedAction :=
  markedActionOfRelators hp certificate

/-- Presentation completeness is the only remaining premise for this marked
action; both generator markings are the original raw column matrices. -/
theorem markedAction_exists (hp : RelatorsPresentCarrier) : Nonempty MarkedAction :=
  ⟨markedAction hp⟩

/-- The balanced checker applied to the actual first generator. The Boolean
inverse certificate is a remaining numerical obligation, not an assumption
that the matrix is invertible. -/
theorem packedA_sq_of_check (h : Balanced.checkInverse treeA treeA = true) :
    (Packed.eval 896 generatorRowsA) ^ 2 = 1 := by
  simpa only [pow_two, treeA_rows] using
    Balanced.eval_inverse 896 treeA treeA treeA_length treeA_length
      treeA_valid treeA_valid h

/-- Checked multiplication, with the exact original ATLAS entries on both sides.
The two interpretation equations have the independent re-encoding producer. -/
theorem matrixA_mul_matrixB_of_check
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB)
    (c : Packed.Mat) (h : Balanced.checkProduct treeA treeB c = true) :
    matrixA * matrixB = Packed.eval 896 c := by
  simpa only [treeA_rows, treeB_rows, hA, hB] using
    Balanced.eval_product 896 treeA treeB c treeA_length treeB_length
      treeA_valid treeB_valid h

/-- Apply the computed units and their relations to the literal marked carrier.
Presentation completeness and the finite computations remain explicit here. -/
noncomputable def markedActionOfPackedRelations (hp : RelatorsPresentCarrier)
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB)
    (hr : ∀ i : Fin 13, positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1) :
    MarkedAction :=
  markedActionOfRelators hp (ofPackedRelations hA hB hr)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
