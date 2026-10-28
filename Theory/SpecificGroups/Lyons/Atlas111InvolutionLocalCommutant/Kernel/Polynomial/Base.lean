module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Data

/-!
# Initial words of the binary word tree

The first three words are the identity and the two literal local generators.

Candidate generation and source attribution: `Kernel/source/GenerateKernel.py`
and `Kernel/source/README.md`. Every numerical assertion is checked in Lean.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Kernel

open Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem identity_small_check : allRows (fun i => small 111 (oneRows i)) = true := by
  decide +kernel

public theorem identity_small (i : Fin 111) : small 111 (oneRows i) = true :=
  allRows_sound identity_small_check i

public theorem word000 : localWord abMatrix Words.localBMatrix 0 = oneMatrix := by
  rw [localWord]
  exact oneMatrix_eq.symm

public theorem word001 : localWord abMatrix Words.localBMatrix 1 = abMatrix := by
  simp [localWord]

public theorem word002 : localWord abMatrix Words.localBMatrix 2 = Words.localBMatrix := by
  simp [localWord]

end Lyons.SimplicityCertificate.LocalCommutant.Kernel
