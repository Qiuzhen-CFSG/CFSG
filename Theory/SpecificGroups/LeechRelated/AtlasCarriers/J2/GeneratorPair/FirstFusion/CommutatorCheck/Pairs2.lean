module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck.Check
import Mathlib.Tactic.FinCases

/-!
# Kernel certificate for a third of the J₂ product representatives

Each theorem verifies a bounded batch of products of the unchanged
centralizer words and coset representatives. The Boolean test and its
interpretation are specified in `Check` and `Soundness`. Every reduction
uses Lean's kernel. Source: ATLAS `J2G1-p100B0`.
-/

public section
set_option Elab.async false
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs40 : checkRange rowCheck 1280 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs41 : checkRange rowCheck 1312 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs42 : checkRange rowCheck 1344 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs43 : checkRange rowCheck 1376 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs44 : checkRange rowCheck 1408 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs45 : checkRange rowCheck 1440 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs46 : checkRange rowCheck 1472 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs47 : checkRange rowCheck 1504 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs48 : checkRange rowCheck 1536 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs49 : checkRange rowCheck 1568 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs50 : checkRange rowCheck 1600 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs51 : checkRange rowCheck 1632 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs52 : checkRange rowCheck 1664 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs53 : checkRange rowCheck 1696 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs54 : checkRange rowCheck 1728 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs55 : checkRange rowCheck 1760 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs56 : checkRange rowCheck 1792 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs57 : checkRange rowCheck 1824 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs58 : checkRange rowCheck 1856 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs59 : checkRange rowCheck 1888 32 = true := by
  decide +kernel

theorem pairs_part2 (k : Fin 20) :
    checkRange rowCheck ((k.val + 40) * 32) 32 = true := by
  fin_cases k
  · exact pairs40
  · exact pairs41
  · exact pairs42
  · exact pairs43
  · exact pairs44
  · exact pairs45
  · exact pairs46
  · exact pairs47
  · exact pairs48
  · exact pairs49
  · exact pairs50
  · exact pairs51
  · exact pairs52
  · exact pairs53
  · exact pairs54
  · exact pairs55
  · exact pairs56
  · exact pairs57
  · exact pairs58
  · exact pairs59

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck
