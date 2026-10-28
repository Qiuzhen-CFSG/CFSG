module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.Words

/-!
# Full-degree commutator checks for Held pair (1, 0)

These seven generator equations certify the discovered commutator expressions
on all 2058 letters. Separating the four pairs bounds elaboration and kernel
checking per module. Source: unchanged ATLAS words; GLS3 Table 5.3p.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.CommutatorChecks10
open Held.TwoLocalCandidates
open scoped commutatorElement
set_option maxRecDepth 8192

set_option maxHeartbeats 2400000 in
public theorem check (k : Fin 7) :
    ((commutatorWord true 0 k).map (fun t =>
      ⁅(coreGenerator true t.1).val, (oddGenerator true 0 t.2).val⁆)).prod =
        (coreGenerator true k).val := by
  apply representation_injective
  simp only [map_list_prod, List.map_map, Function.comp_def, commutatorElement_def,
    map_mul, map_inv, representation_coreGenerator, representation_oddGenerator]
  fin_cases k <;> apply Equiv.ext <;> apply Cores.allLetters <;> decide +kernel

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.CommutatorChecks10
