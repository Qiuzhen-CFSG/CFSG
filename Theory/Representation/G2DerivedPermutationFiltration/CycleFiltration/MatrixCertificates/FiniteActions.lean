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
theorem packed_action : ∀ (a : Fin 2) (j : Fin 64),
    combine adaptedRows (fun k => (adaptedActionColumns a j).testBit k.val) =
      combine (actionColumns a) (fun k => (adaptedRows j).testBit k.val) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_flags : ∀ (a : Fin 2) (j : Fin 64),
    combine cycleEmbeddingRows (fun k => (actionColumns a j).testBit k.val) =
      pack (fun x : Fin 189 => (cycleEmbeddingRows j).testBit (flagInverse a x).val) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem adapted_lower_left : ∀ (a : Fin 2) (i j : Fin 32),
    adaptedAction a (last i) (first j) = 0 := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem flag_inverse_left : ∀ (a : Fin 2) (i : Fin 189),
    flagInverse a (flagPermutation a i) = i := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem flag_inverse_right : ∀ (a : Fin 2) (i : Fin 189),
    flagPermutation a (flagInverse a i) = i := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem ambient_flag_involution : ∀ (a : Fin 8) (i : Fin 189),
    ambientFlagPermutation a (ambientFlagPermutation a i) = i := by decide +kernel

end G2DerivedPermutationFiltration.CycleData.Certificate
