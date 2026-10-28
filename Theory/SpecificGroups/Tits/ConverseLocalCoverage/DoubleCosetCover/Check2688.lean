module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Rows

/-!
# Kernel checks for double-coset rows 2688 through 2815

This slice compares the candidate factorizations at the certified base 0, 1, 2.
Source: Parrott (1972), section 5, p.683; see `Rows` for the input tables.
-/

namespace Tits.ConverseLocalCoverage.DoubleCosetCertificate

set_option maxRecDepth 30000 in
set_option maxHeartbeats 16000000 in
public theorem check2688 : List.Forall₂ (fun w row => testRow w row = true)
    (R1Certificate.input.reps.toList.drop 2688 |>.take 128)
    (rows.drop 2688 |>.take 128) := by
  decide +kernel

end Tits.ConverseLocalCoverage.DoubleCosetCertificate
