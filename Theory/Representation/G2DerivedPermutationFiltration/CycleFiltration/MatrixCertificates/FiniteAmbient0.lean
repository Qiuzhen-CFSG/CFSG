module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.Packed

/-!
# Finite binary cycle certificates

These packed identities are checked by Lean's kernel and decoded in `Checks`.
They certify the witnesses and matrix conventions documented in `Data`.
Source application: Aschbacher–Smith G.7.2(3), printed p.348/PDF p.359.
-/

@[expose] public section
namespace G2DerivedPermutationFiltration.CycleData.Certificate

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_ambient_flags_0 : ∀ (j : Fin 64),
    combine cycleEmbeddingRows (fun k => (ambientColumns 0 j).testBit k.val) =
      pack (fun x : Fin 189 =>
        (cycleEmbeddingRows j).testBit (ambientFlagPermutation 0 x).val) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_ambient_flags_1 : ∀ (j : Fin 64),
    combine cycleEmbeddingRows (fun k => (ambientColumns 1 j).testBit k.val) =
      pack (fun x : Fin 189 =>
        (cycleEmbeddingRows j).testBit (ambientFlagPermutation 1 x).val) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_ambient_flags_2 : ∀ (j : Fin 64),
    combine cycleEmbeddingRows (fun k => (ambientColumns 2 j).testBit k.val) =
      pack (fun x : Fin 189 =>
        (cycleEmbeddingRows j).testBit (ambientFlagPermutation 2 x).val) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_ambient_flags_3 : ∀ (j : Fin 64),
    combine cycleEmbeddingRows (fun k => (ambientColumns 3 j).testBit k.val) =
      pack (fun x : Fin 189 =>
        (cycleEmbeddingRows j).testBit (ambientFlagPermutation 3 x).val) := by
  decide +kernel

end G2DerivedPermutationFiltration.CycleData.Certificate
