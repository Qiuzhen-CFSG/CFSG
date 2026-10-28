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
theorem packed_adapted_top_block : ∀ (a : Fin 2) (i j : Fin 32),
    (adaptedActionColumns a (first j)).testBit (first i).val =
      (factorRows 0 a i).testBit j.val := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem packed_adapted_bottom_block : ∀ (a : Fin 2) (i j : Fin 32),
    (adaptedActionColumns a (last j)).testBit (last i).val =
      (factorRows 1 a i).testBit j.val := by decide +kernel

end G2DerivedPermutationFiltration.CycleData.Certificate
