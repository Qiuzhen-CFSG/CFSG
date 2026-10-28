module

public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Data

/-!
# Point-orbit checks for representative rows 3072–3327

A bounded slice of the witness table; all permutation computations are reduced
by Lean's kernel. See `Data` for the mathematical interpretation and source.
-/

namespace Tits.ThreeSylowContainment.Certificate

set_option maxRecDepth 30000 in
set_option maxHeartbeats 16000000 in
public theorem check3072 : List.Forall₂ (fun w row => testRow w row = true)
    (R1Certificate.input.reps.toList.drop 3072 |>.take 256)
    (rows.drop 3072 |>.take 256) := by
  decide +kernel

end Tits.ThreeSylowContainment.Certificate
