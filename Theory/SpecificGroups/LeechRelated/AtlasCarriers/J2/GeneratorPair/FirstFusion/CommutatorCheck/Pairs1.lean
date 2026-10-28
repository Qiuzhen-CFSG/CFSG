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
private theorem pairs20 : checkRange rowCheck 640 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs21 : checkRange rowCheck 672 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs22 : checkRange rowCheck 704 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs23 : checkRange rowCheck 736 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs24 : checkRange rowCheck 768 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs25 : checkRange rowCheck 800 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs26 : checkRange rowCheck 832 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs27 : checkRange rowCheck 864 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs28 : checkRange rowCheck 896 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs29 : checkRange rowCheck 928 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs30 : checkRange rowCheck 960 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs31 : checkRange rowCheck 992 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs32 : checkRange rowCheck 1024 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs33 : checkRange rowCheck 1056 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs34 : checkRange rowCheck 1088 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs35 : checkRange rowCheck 1120 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs36 : checkRange rowCheck 1152 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs37 : checkRange rowCheck 1184 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs38 : checkRange rowCheck 1216 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs39 : checkRange rowCheck 1248 32 = true := by
  decide +kernel

theorem pairs_part1 (k : Fin 20) :
    checkRange rowCheck ((k.val + 20) * 32) 32 = true := by
  fin_cases k
  · exact pairs20
  · exact pairs21
  · exact pairs22
  · exact pairs23
  · exact pairs24
  · exact pairs25
  · exact pairs26
  · exact pairs27
  · exact pairs28
  · exact pairs29
  · exact pairs30
  · exact pairs31
  · exact pairs32
  · exact pairs33
  · exact pairs34
  · exact pairs35
  · exact pairs36
  · exact pairs37
  · exact pairs38
  · exact pairs39

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck
