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
theorem packed_adapted_inverse : ∀ j : Fin 64,
    combine adaptedRows (fun k => (adaptedInverseRows j).testBit k.val) = 2 ^ j.val := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_extraction : ∀ j : Fin 64,
    combine extractionColumns (fun k => (cycleEmbeddingRows j).testBit k.val) = 2 ^ j.val := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_boundary : ∀ j : Fin 64,
    combine boundaryColumns (fun k => (cycleEmbeddingRows j).testBit k.val) = 0 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_splitting : ∀ j : Fin 189,
    combine cycleEmbeddingRows (fun k => (extractionColumns j).testBit k.val) ^^^
      combine retractionColumns (fun k => (boundaryColumns j).testBit k.val) = 2 ^ j.val := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem boundary_endpoints : ∀ (a : Fin 2) (i : Fin 63) (j : Fin 189),
    boundaryMatrix ⟨63 * a.val + i.val, by omega⟩ j =
      if endpoint a j = i then 1 else 0 := by decide +kernel

end G2DerivedPermutationFiltration.CycleData.Certificate
