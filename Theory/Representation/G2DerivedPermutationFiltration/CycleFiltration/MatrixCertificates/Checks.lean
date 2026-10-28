module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.FiniteBasis
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.FiniteActions
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.FiniteBlocks
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.FinitePair
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.FiniteAmbient0
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.FiniteAmbient1

/-!
# Kernel-checked cycle and block matrices

Packed XOR identities prove a left inverse for the saved cycle embedding and
an explicit splitting of the boundary sequence. They also prove both change
of basis identities, the two factor actions, and the ambient preserved/swapped
pair of halves. All finite calculations use `decide +kernel`.
Source: Aschbacher–Smith G.7.2(3), printed p.348/PDF p.359; witness provenance
and conventions are in `Data` and `MatrixData`.
-/

@[expose] public section
namespace G2DerivedPermutationFiltration.CycleData.Certificate

set_option maxRecDepth 16384

theorem packed_ambient_flags (a : Fin 8) (j : Fin 64) :
    combine cycleEmbeddingRows (fun k => (ambientColumns a j).testBit k.val) =
      pack (fun x : Fin 189 =>
        (cycleEmbeddingRows j).testBit (ambientFlagPermutation a x).val) := by
  fin_cases a
  · exact packed_ambient_flags_0 j
  · exact packed_ambient_flags_1 j
  · exact packed_ambient_flags_2 j
  · exact packed_ambient_flags_3 j
  · exact packed_ambient_flags_4 j
  · exact packed_ambient_flags_5 j
  · exact packed_ambient_flags_6 j
  · exact packed_ambient_flags_7 j

theorem adapted_top_block (a : Fin 2) (i j : Fin 32) :
    adaptedAction a (first i) (first j) = factorMatrix 0 a i j := by
  unfold adaptedAction columns factorMatrix bit
  rw [packed_adapted_top_block]

theorem adapted_bottom_block (a : Fin 2) (i j : Fin 32) :
    adaptedAction a (last i) (last j) = factorMatrix 1 a i j := by
  unfold adaptedAction columns factorMatrix bit
  rw [packed_adapted_bottom_block]

theorem adapted_mul_inverse : adaptedBasis.transpose * adaptedInverse.transpose = 1 := by
  ext i j
  change (columns (m := 64) adaptedRows * columns (m := 64) adaptedInverseRows) i j = _
  rw [columns_mul_apply, packed_adapted_inverse, bit_power]
  simp only [Matrix.one_apply, Fin.val_inj, eq_comm]

theorem inverse_mul_adapted : adaptedInverse.transpose * adaptedBasis.transpose = 1 :=
  (mul_eq_one_comm (a := adaptedBasis.transpose) (b := adaptedInverse.transpose)).mp
    adapted_mul_inverse

theorem extraction_embedding : extraction * cycleEmbedding = 1 := by
  ext i j
  change (columns (m := 64) extractionColumns * columns (m := 189) cycleEmbeddingRows) i j = _
  rw [columns_mul_apply, packed_extraction, bit_power]
  simp only [Matrix.one_apply, Fin.val_inj, eq_comm]

theorem boundary_embedding : boundaryMatrix * cycleEmbedding = 0 := by
  ext i j
  change (columns (m := 126) boundaryColumns * columns (m := 189) cycleEmbeddingRows) i j = _
  rw [columns_mul_apply, packed_boundary, bit_zero]
  rfl

theorem boundary_splitting : cycleEmbedding * extraction + retraction * boundaryMatrix = 1 := by
  ext i j
  have h := congrArg (fun r => bit r i.val) (packed_splitting j)
  rw [bit_xor, bit_power] at h
  change (columns (m := 189) cycleEmbeddingRows * columns (m := 64) extractionColumns) i j +
    (columns (m := 189) retractionColumns * columns (m := 126) boundaryColumns) i j = _
  rw [columns_mul_apply, columns_mul_apply, h]
  simp only [Matrix.one_apply, Fin.val_inj, eq_comm]

theorem adapted_action (a : Fin 2) :
    adaptedBasis.transpose * adaptedAction a = actionMatrix a * adaptedBasis.transpose := by
  ext i j
  change (columns (m := 64) adaptedRows * columns (m := 64) (adaptedActionColumns a)) i j =
    (columns (m := 64) (actionColumns a) * columns (m := 64) adaptedRows) i j
  rw [columns_mul_apply, columns_mul_apply, packed_action]

theorem embedding_action (a : Fin 2) :
    cycleEmbedding * actionMatrix a = fun i j => cycleEmbedding (flagInverse a i) j := by
  ext i j
  change (columns (m := 189) cycleEmbeddingRows * columns (m := 64) (actionColumns a)) i j = _
  rw [columns_mul_apply, packed_flags, bit_pack]
  rfl

theorem embedding_ambient (a : Fin 8) :
    cycleEmbedding * ambientMatrix a =
      fun i j => cycleEmbedding (ambientFlagPermutation a i) j := by
  ext i j
  change (columns (m := 189) cycleEmbeddingRows * columns (m := 64) (ambientColumns a)) i j = _
  rw [columns_mul_apply, packed_ambient_flags, bit_pack]
  rfl

theorem pair_mul_inverse : pairBasis * pairInverse = 1 := by
  ext i j
  change (columns (m := 64) pairColumns * columns (m := 64) pairInverseColumns) i j = _
  rw [columns_mul_apply, packed_pair_inverse, bit_power]
  simp only [Matrix.one_apply, Fin.val_inj, eq_comm]

theorem inverse_mul_pair : pairInverse * pairBasis = 1 := (mul_eq_one_comm (a := pairBasis) (b := pairInverse)).mp pair_mul_inverse

theorem pair_action (a : Fin 8) :
    pairBasis * pairAction a = ambientMatrix a * pairBasis := by
  ext i j
  change (columns (m := 64) pairColumns * columns (m := 64) (pairActionColumns a)) i j =
    (columns (m := 64) (ambientColumns a) * columns (m := 64) pairColumns) i j
  rw [columns_mul_apply, columns_mul_apply, packed_pair_action]

theorem pair_last (i : Fin 64) (j : Fin 32) :
    pairBasis i (last j) = (ambientMatrix 5 * adaptedBasis.transpose) i (first j) := by
  change bit (pairColumns (last j)) i.val =
    (columns (m := 64) (ambientColumns 5) * columns (m := 64) adaptedRows) i (first j)
  rw [columns_mul_apply, packed_pair_last]

end G2DerivedPermutationFiltration.CycleData.Certificate
