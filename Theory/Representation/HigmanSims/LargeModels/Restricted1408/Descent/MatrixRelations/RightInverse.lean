module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.Checker
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.RightInverse.Certificate

/-!
# The literal degree-1408 B matrix has the published right inverse

The complete kernel-checked row certificates cover all 1408 coordinates.
The block-layout equalities identify their entries with the original B and
inverse tables. Packed XOR soundness then gives ordinary matrix multiplication,
with exactly the row convention used by `matrixRelations_of_finite_certificates`.
The finite-ring argument in that consumer supplies the reverse inverse identity.

Source: ATLAS HSd2G1-f2r1408B0 restricted by HSd2G1-max1W1;
see Restricted1408/source/README.md and RightInverse/source/README.md.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate

namespace RightInverse

private theorem allBlocks (j : Fin 44) :
    checkRows inverseBlocks (32 * j.val) bBlocks[j.val]! = true := by
  fin_cases j
  · exact checked00
  · exact checked01
  · exact checked02
  · exact checked03
  · exact checked04
  · exact checked05
  · exact checked06
  · exact checked07
  · exact checked08
  · exact checked09
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
  · exact checked29
  · exact checked30
  · exact checked31
  · exact checked32
  · exact checked33
  · exact checked34
  · exact checked35
  · exact checked36
  · exact checked37
  · exact checked38
  · exact checked39
  · exact checked40
  · exact checked41
  · exact checked42
  · exact checked43

private theorem row_certificate (i : Fin 1408) :
    PackedBinaryRows.listProduct bRows[i.val]! 0 inverseRows.toList = 2 ^ i.val := by
  let j : Fin 44 := ⟨i.val / 32, by omega⟩
  let k : Fin 32 := ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩
  have h := checkRows_sound inverseBlocks bBlocks[j.val]! (32 * j.val) (allBlocks j)
    k.val (by rw [bBlocks_length]; exact k.isLt)
  rw [blockProduct_sound, inverseBlocks_eq, ← bBlocks_entries j k] at h
  have he : 32 * j.val + k.val = i.val := by dsimp [j, k]; omega
  rwa [he] at h

end RightInverse

/-- The candidate inverse table is an actual right inverse of the literal B matrix. -/
theorem matrixB_mul_inverse : matrixB * inverseMatrix = 1 := by
  change Thompson.BinaryMatrix.decode 1408 bRows *
    Thompson.BinaryMatrix.decode 1408 inverseRows = 1
  apply Thompson.BinaryMatrix.decode_mul_one
  intro i
  rw [PackedBinaryRows.rowProduct_eq_listProduct _ _ _ (by decide +kernel)]
  exact RightInverse.row_certificate i

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate
