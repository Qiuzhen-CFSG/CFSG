module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Generation.Decoder

/-!
# Checked separation of the 2048 max4 products

The two-point decoder is a left inverse on all eleven-bit products. These
kernel checks use only point evaluation and the small packed decoder;
they do not compare full permutations or repeat square/commutator checks.
`Generation.lean` transfers this certificate to the literal model words.

Source application: GLS3 Table 5.3r, pp.291--292; Aschbacher--Smith I.2.2(7),
printed pp.412--413. Data attribution and convention: see `Decoder.lean`.
-/

namespace Rudvalis.CoveringIncidence.Max4Special.Generation

-- Sequential 256-entry checks keep the kernel reduction cache bounded.
-- The monolithic check peaked at 6.0 GiB; these blocks peaked at 3.6 GiB.
set_option Elab.async false

private def chunkIndex (b : Fin 8) (i : Fin 256) : Fin 2048 :=
  ⟨256 * b.val + i.val, by omega⟩

set_option maxRecDepth 2000 in
private theorem decode_block_0 : ∀ i : Fin 256,
    decode (binaryMap (chunkIndex 0 i) 0) (binaryMap (chunkIndex 0 i) 1) =
      (chunkIndex 0 i).val := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 2000 in
private theorem decode_block_1 : ∀ i : Fin 256,
    decode (binaryMap (chunkIndex 1 i) 0) (binaryMap (chunkIndex 1 i) 1) =
      (chunkIndex 1 i).val := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 2000 in
private theorem decode_block_2 : ∀ i : Fin 256,
    decode (binaryMap (chunkIndex 2 i) 0) (binaryMap (chunkIndex 2 i) 1) =
      (chunkIndex 2 i).val := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 2000 in
private theorem decode_block_3 : ∀ i : Fin 256,
    decode (binaryMap (chunkIndex 3 i) 0) (binaryMap (chunkIndex 3 i) 1) =
      (chunkIndex 3 i).val := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 2000 in
private theorem decode_block_4 : ∀ i : Fin 256,
    decode (binaryMap (chunkIndex 4 i) 0) (binaryMap (chunkIndex 4 i) 1) =
      (chunkIndex 4 i).val := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 2000 in
private theorem decode_block_5 : ∀ i : Fin 256,
    decode (binaryMap (chunkIndex 5 i) 0) (binaryMap (chunkIndex 5 i) 1) =
      (chunkIndex 5 i).val := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 2000 in
private theorem decode_block_6 : ∀ i : Fin 256,
    decode (binaryMap (chunkIndex 6 i) 0) (binaryMap (chunkIndex 6 i) 1) =
      (chunkIndex 6 i).val := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 2000 in
private theorem decode_block_7 : ∀ i : Fin 256,
    decode (binaryMap (chunkIndex 7 i) 0) (binaryMap (chunkIndex 7 i) 1) =
      (chunkIndex 7 i).val := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem decode_block (b : Fin 8) : ∀ i : Fin 256,
    decode (binaryMap (chunkIndex b i) 0) (binaryMap (chunkIndex b i) 1) =
      (chunkIndex b i).val := by
  fin_cases b
  · exact decode_block_0
  · exact decode_block_1
  · exact decode_block_2
  · exact decode_block_3
  · exact decode_block_4
  · exact decode_block_5
  · exact decode_block_6
  · exact decode_block_7

public theorem decode_binaryMap (n : Fin 2048) :
    decode (binaryMap n 0) (binaryMap n 1) = n.val := by
  let b : Fin 8 := ⟨n.val / 256, by omega⟩
  let i : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hi : chunkIndex b i = n := by
    apply Fin.ext
    dsimp [chunkIndex, b, i]
    omega
  simpa only [hi] using decode_block b i

end Rudvalis.CoveringIncidence.Max4Special.Generation
