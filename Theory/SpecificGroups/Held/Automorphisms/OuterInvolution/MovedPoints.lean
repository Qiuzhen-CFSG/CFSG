module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Representative

/-!
# The concrete outer representative moves every letter

The fifth power of the checked ATLAS implementer is fixed-point-free on the
2058-point action. Its 1029 transpositions will give its negative sign.
The calculation uses the literal tables from ATLAS `HeG1-p2058B0` and the
intertwining permutation for `HeG1-a2W1`.
-/

public section
namespace Held.OuterInvolution

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem representative_no_fixed_points :
    ∀ x : Fin 2058, (representative : Equiv.Perm (Fin 2058)) x ≠ x := by
  decide +kernel

end Held.OuterInvolution
