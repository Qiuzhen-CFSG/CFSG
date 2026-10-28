module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Basic

/-!
# Mask 8: a finite color certificate for the Held sextet

The sextet is exactly the size-2 color class, so the initial coloring suffices.
All finite assertions are kernel checked against the published graph and colors.
Source: ATLAS HeG1-p2058B0/max3; GLS3 Table 5.3p.
Reproduce the data with `ColoredSextet/Source/generate.py`.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
open Held.NormalizerGraph


set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sextet_spec : ∀ x : Fin 2058,
    x ∈ sextet ↔ orbitSizeLabel 3 x = 2 := by
  decide +kernel

public theorem coloredGraphGroup_3_le_sextet :
    coloredGraphGroup 3 ≤ sextetPermutationStabilizer := by
  intro σ hσ
  apply stabilizes_of_invariant
  intro x
  rw [sextet_spec, sextet_spec, hσ.2 x]

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
