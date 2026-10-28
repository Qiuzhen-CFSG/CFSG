module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Basic

/-!
# Mask 5: a finite color certificate for the Held sextet

Among size-8 vertices, 40 neighbors in the size-64 class distinguish an
eight-point class. Counting neighbors in that new class separates the desired
four-point class. Together with the size-2 class it is exactly the sextet.
All finite assertions are kernel checked against the published graph and colors.
Source: ATLAS HeG1-p2058B0/max3; GLS3 Table 5.3p.
Reproduce the data with `ColoredSextet/Source/generate.py`.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
open Held.NormalizerGraph


set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private def seedClass : Finset (Fin 2058) :=
  Finset.univ.filter (fun x => orbitSizeLabel 2 x = 64)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem seedClass_spec : ∀ x : Fin 2058,
    x ∈ seedClass ↔ orbitSizeLabel 2 x = 64 := by
  intro x
  simp only [seedClass, Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private def countingClass : Finset (Fin 2058) :=
  ⟨([352, 368, 593, 973, 1241, 1484, 1564, 2034] : List (Fin 2058)), by decide +kernel⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem countingClass_spec : ∀ x : Fin 2058,
    x ∈ countingClass ↔ orbitSizeLabel 2 x = 8 ∧ neighborCount seedClass x = 40 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem sextet_spec : ∀ x : Fin 2058,
    x ∈ sextet ↔ orbitSizeLabel 2 x = 2 ∨
      orbitSizeLabel 2 x = 4 ∧ neighborCount countingClass x = 4 := by
  decide +kernel

public theorem coloredGraphGroup_2_le_sextet :
    coloredGraphGroup 2 ≤ sextetPermutationStabilizer := by
  intro σ hσ
  have hseed := colorClass_invariant 2 seedClass 64 seedClass_spec σ hσ
  have hc : ∀ x, σ x ∈ countingClass ↔ x ∈ countingClass := by
    intro x
    rw [countingClass_spec, countingClass_spec, hσ.2 x,
      neighborCount_invariant seedClass σ hσ.1 hseed x]
  apply stabilizes_of_invariant
  intro x
  rw [sextet_spec, sextet_spec, hσ.2 x,
    neighborCount_invariant countingClass σ hσ.1 hc x]

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
