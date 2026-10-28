module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Basic
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.Data

/-!
# Mask 12: a finite color certificate for the Held sextet

Counts into the size-1 and size-8 classes recover the representative
coloring. Thus every symmetry here lies in the representative colored graph
group, retaining parity. This is a refinement inclusion, not an order claim.
All finite assertions are kernel checked against the published graph and colors.
Source: ATLAS HeG1-p2058B0/max3; GLS3 Table 5.3p.
Reproduce the data with `ColoredSextet/Source/generate.py`.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
open Held.NormalizerGraph


set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private def unitClass : Finset (Fin 2058) :=
  Finset.univ.filter (fun x => orbitSizeLabel 5 x = 1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem unitClass_spec : ∀ x : Fin 2058,
    x ∈ unitClass ↔ orbitSizeLabel 5 x = 1 := by
  intro x
  simp only [unitClass, Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private def eightClass : Finset (Fin 2058) :=
  Finset.univ.filter (fun x => orbitSizeLabel 5 x = 8)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem eightClass_spec : ∀ x : Fin 2058,
    x ∈ eightClass ↔ orbitSizeLabel 5 x = 8 := by
  intro x
  simp only [eightClass, Finset.mem_filter, Finset.mem_univ, true_and]

private def recoveredColor (x : Fin 2058) : ℕ :=
  let c := orbitSizeLabel 5 x
  if c = 1 then 2
  else if c = 16 then (if neighborCount unitClass x = 1 then 32 else 16)
  else if c = 32 then (if neighborCount eightClass x = 2 then 32 else 64)
  else if c = 64 then (if neighborCount unitClass x = 0 then 128 else 64)
  else if c = 256 then (if neighborCount unitClass x = 1 then 512 else 256)
  else c

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem recoveredColor_spec : ∀ x : Fin 2058,
    SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x = recoveredColor x := by
  decide +kernel

public theorem coloredGraphGroup_5_le_representative_colored :
    coloredGraphGroup 5 ≤ SylowGeometry.Calculations.InnerNormalizer.coloredGraphGroup := by
  intro σ hσ
  refine ⟨hσ.1, ?_⟩
  intro x
  rw [recoveredColor_spec, recoveredColor_spec]
  unfold recoveredColor
  rw [hσ.2 x,
    neighborCount_invariant unitClass σ hσ.1
      (colorClass_invariant 5 unitClass 1 unitClass_spec σ hσ) x,
    neighborCount_invariant eightClass σ hσ.1
      (colorClass_invariant 5 eightClass 8 eightClass_spec σ hσ) x]

public theorem evenColoredGraphGroup_5_le_representative_even :
    evenColoredGraphGroup 5 ≤ SylowGeometry.Calculations.InnerNormalizer.evenColoredGraphGroup :=
  fun _ h => ⟨coloredGraphGroup_5_le_representative_colored h.1, h.2⟩

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
