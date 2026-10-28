module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Data
/-! Exact decodings of the two restricted forms and the transported exterior
functional. Packed row products are checked by the kernel before use as matrix
identities. Source and column conventions: `../source/README.md`. -/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

private theorem matrix_eq_checked {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : @decide (∀ i j, A i j = B i j)
      (@Nat.decidableForallFin m _ (fun _ => @Nat.decidableForallFin n _
        (fun _ => ZMod.decidableEq 2 _ _))) = true) : A = B :=
  funext fun i => funext fun j =>
    @of_decide_eq_true _ (@Nat.decidableForallFin m _ (fun _ =>
      @Nat.decidableForallFin n _ (fun _ => ZMod.decidableEq 2 _ _))) h i j

theorem j_decode : decodeRows 50 jRows = restrictionPairing := rfl

theorem j_transpose : restrictionPairingᵀ = restrictionPairing := by
  apply matrix_eq_checked
  decide +kernel

theorem embedding_decode : decodeRows 50 embeddingRows = restrictionEmbedding := by
  apply matrix_eq_checked
  decide +kernel

theorem embedding_transpose_decode :
    decodeRows 112 restrictionColumns = restrictionEmbeddingᵀ := rfl

theorem fj_decode : decodeRows 50 fjRows = (decode functionalJBits : RestrictionMatrix) := by
  apply matrix_eq_checked
  decide +kernel

theorem fe_decode : decodeRows 50 feRows = (decode functionalEBits : RestrictionMatrix) := by
  apply matrix_eq_checked
  decide +kernel

private theorem ambientE0_decode : decodeRows 112 ambientE0Rows = exteriorBasisForm 0 := by
  apply matrix_eq_checked
  decide +kernel

private theorem e_left_check : ∀ i : Fin 50,
    rowProduct (restrictionColumns.get i) ambientE0Rows = restrictionLeftRows.get i := by
  decide +kernel

private theorem e_right_check : ∀ i : Fin 50,
    rowProduct (restrictionLeftRows.get i) embeddingRows = eRows.get i := by
  decide +kernel

theorem e_decode : decodeRows 50 eRows = restrictionTestForm 0 := by
  change _ = restrictionEmbeddingᵀ * exteriorBasisForm 0 * restrictionEmbedding
  rw [← embedding_transpose_decode, ← embedding_decode, ← ambientE0_decode,
    decodeRows_product _ _ _ e_left_check, decodeRows_product _ _ _ e_right_check]

theorem e_transpose : (restrictionTestForm 0)ᵀ = restrictionTestForm 0 := by
  rw [← e_decode]
  apply matrix_eq_checked
  decide +kernel

private theorem phi_left_check : ∀ i : Fin 112,
    rowProduct (embeddingRows.get i) feRows = phiLeftRows.get i := by
  decide +kernel

private theorem phi_right_check : ∀ i : Fin 112,
    rowProduct (phiLeftRows.get i) restrictionColumns = phiRows.get i := by
  decide +kernel

theorem phi_decode :
    decodeRows 112 phiRows =
      restrictionEmbedding * decode functionalEBits * restrictionEmbeddingᵀ := by
  rw [← embedding_transpose_decode, ← embedding_decode, ← fe_decode,
    decodeRows_product _ _ _ phi_left_check, decodeRows_product _ _ _ phi_right_check]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
