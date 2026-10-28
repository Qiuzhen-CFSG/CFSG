module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Reduction
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Structure

/-!
# A concrete element of each local Held two-core

The existing word-defined core is a normal two-subgroup of the literal
local overgroup. It therefore lies in its actual two-core. Its first
generator is the sixth power of the max3 word, or the fifth power of the
max4 word. These elements can exclude Schreier entries which do not
contain the required lower endpoint, without identifying the whole core.

Sources: GLS3 Table 5.3p; ATLAS max3/max4, as checked in
TwoLocalCandidates.Cores.Structure and its relation modules.
-/

public section
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient
open Subgroup
open Held.TwoLocalCandidates

/-- A certified word in the actual embedded two-core of either local. -/
theorem localWord_power_mem_localTwoCore (i : Bool) :
    localWord i ^ (if i then 5 else 6) ∈ localTwoCore i := by
  have hc (j : Fin 3) : Cores.core j ≤ pCore 2 (subgroup j) :=
    le_sSup ⟨Cores.core_normal j, Cores.core_isPGroup j⟩
  cases i
  · refine ⟨Cores.coreGenerator 0 0, hc 0 (Cores.coreGenerator_mem 0 0), ?_⟩
    simp [Cores.coreGenerator, Cores.coreWord, Cores.localGenerator]
  · refine ⟨Cores.coreGenerator 1 0, hc 1 (Cores.coreGenerator_mem 1 0), ?_⟩
    simp [Cores.coreGenerator, Cores.coreWord, Cores.localGenerator]

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient
