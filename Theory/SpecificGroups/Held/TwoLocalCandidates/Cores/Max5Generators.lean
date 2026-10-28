module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Tables2

/-!
# Two relations in the literal Held max5 generators

The second ATLAS generator has order dividing three, and the first times
its inverse has order dividing four. The existing checked lookup tables
make these short word checks independent of a structure identification of
max5. Together with the core conjugation relations they prove perfection,
as needed for the binary-three point-component comparison.

Source: ATLAS HeG1-max5W1; GLS3 Table 5.3p.
-/

namespace Held.TwoLocalCandidates.Cores
open Tables2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
public theorem max5_second_cube : localGenerator 2 1 ^ 3 = 1 := by
  apply embedding_injective 2
  rw [map_pow, map_one, ← p1_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
public theorem max5_alternate_fourth :
    (localGenerator 2 0 * (localGenerator 2 1)⁻¹) ^ 4 = 1 := by
  apply embedding_injective 2
  rw [map_pow, map_mul, map_inv, map_one, ← p0_eq, ← p1_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

end Held.TwoLocalCandidates.Cores
