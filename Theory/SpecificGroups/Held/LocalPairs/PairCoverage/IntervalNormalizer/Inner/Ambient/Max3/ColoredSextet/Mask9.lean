module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Basic

/-!
# Mask 9: a finite color certificate for the Held sextet

The sextet is the size-2 class together with those size-4 vertices having
128 neighbors in the size-256 class. Neighbor-count transport proves invariance.
All finite assertions are kernel checked against the published graph and colors.
Source: ATLAS HeG1-p2058B0/max3; GLS3 Table 5.3p.
Reproduce the data with `ColoredSextet/Source/generate.py`.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
open Held.NormalizerGraph


set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private def countingClass : Finset (Fin 2058) :=
  Finset.univ.filter (fun x => orbitSizeLabel 4 x = 256)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem countingClass_spec : ∀ x : Fin 2058,
    x ∈ countingClass ↔ orbitSizeLabel 4 x = 256 := by
  intro x
  simp only [countingClass, Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sextet_spec : ∀ x : Fin 2058,
    x ∈ sextet ↔ orbitSizeLabel 4 x = 2 ∨
      orbitSizeLabel 4 x = 4 ∧ neighborCount countingClass x = 128 := by
  decide +kernel

public theorem coloredGraphGroup_4_le_sextet :
    coloredGraphGroup 4 ≤ sextetPermutationStabilizer :=
  colored_le_of_neighbor_count 4 countingClass 256 128 countingClass_spec sextet_spec

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
