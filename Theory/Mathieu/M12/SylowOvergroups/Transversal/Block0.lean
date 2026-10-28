module

public import Theory.Mathieu.M12.SylowOvergroups.Transversal.FastKey

/-! Kernel-checked coset keys, block 1 of five. -/

public section
namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem key_block_0 : ∀ b : Fin 297,
    explicitKey (transversalPerm (blockIndex 0 b)) = keyTable[(blockIndex 0 b).val]! := by
  decide +kernel

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
