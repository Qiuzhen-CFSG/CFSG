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
theorem packed_pair_inverse : ∀ j : Fin 64,
    combine pairColumns (fun k => (pairInverseColumns j).testBit k.val) = 2 ^ j.val := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_pair_action : ∀ (a : Fin 8) (j : Fin 64),
    combine pairColumns (fun k => (pairActionColumns a j).testBit k.val) =
      combine (ambientColumns a) (fun k => (pairColumns j).testBit k.val) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem pair_first : ∀ (i : Fin 64) (j : Fin 32),
    pairBasis i (first j) = adaptedBasis.transpose i (first j) := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_pair_last : ∀ j : Fin 32,
    pairColumns (last j) =
      combine (ambientColumns 5) (fun k => (adaptedRows (first j)).testBit k.val) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem pair_zero_blocks : ∀ (a : Fin 8) (i j : Fin 32),
    (if swaps a then pairAction a (first i) (first j) = 0 ∧
      pairAction a (last i) (last j) = 0
    else pairAction a (last i) (first j) = 0 ∧
      pairAction a (first i) (last j) = 0) := by decide +kernel

end G2DerivedPermutationFiltration.CycleData.Certificate
