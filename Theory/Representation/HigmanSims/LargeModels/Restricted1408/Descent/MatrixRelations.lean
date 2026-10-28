module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Contracts
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.Checker
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.RightInverse
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.LongWords

/-!
# The thirteen sourced relations on the literal degree-1408 matrices

The three kernel-checked certificates supply a right inverse for B, the first
seven source words, and the final six words (including R1--R3). Source word
zero makes A its own inverse; finiteness supplies the reverse inverse identity
for B. Their assembly constructs units with exactly the original matrices and
proves every signed word, in the original multiplication order.

Source: the retained ATLAS HSG1-P1.M, with matrices HSd2G1-f2r1408B0 restricted
by HSd2G1-max1W1; see `MatrixRelations/source/README.md`. Presentation
faithfulness and density are separate from this unconditional finite certificate.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408
open RelationCertificate

/-- Assemble all thirteen source clauses; no presentation faithfulness or
density hypothesis is used to establish these finite matrix identities. -/
theorem matrixRelations_of_finite_certificates
    (hb : matrixB * inverseMatrix = 1)
    (hsmall : ∀ i : Fin 7, matrixWord ⟨i.val, by omega⟩ = 1)
    (hlarge : ∀ i : Fin 6, matrixWord ⟨i.val + 7, by omega⟩ = 1) : MatrixRelations := by
  apply matrixRelations_of_identities hb
  intro i
  by_cases hi : i.val < 7
  · exact hsmall ⟨i.val, hi⟩
  · have h := hlarge ⟨i.val - 7, by omega⟩
    have he : (⟨i.val - 7 + 7, by omega⟩ : Fin 13) = i := by
      apply Fin.ext
      change i.val - 7 + 7 = i.val
      omega
    rwa [he] at h

/-- The literal matrices lift to units satisfying all thirteen signed ATLAS
relations, including R1--R3, with no additional hypotheses. -/
theorem matrixRelations : MatrixRelations :=
  matrixRelations_of_finite_certificates matrixB_mul_inverse smallWords largeWords

end Representation.HigmanSims.LargeModels.Restricted1408
