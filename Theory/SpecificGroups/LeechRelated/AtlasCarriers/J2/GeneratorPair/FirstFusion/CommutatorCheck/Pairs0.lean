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
private theorem pairs00 : checkRange rowCheck 0 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs01 : checkRange rowCheck 32 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs02 : checkRange rowCheck 64 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs03 : checkRange rowCheck 96 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs04 : checkRange rowCheck 128 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs05 : checkRange rowCheck 160 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs06 : checkRange rowCheck 192 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs07 : checkRange rowCheck 224 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs08 : checkRange rowCheck 256 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs09 : checkRange rowCheck 288 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs10 : checkRange rowCheck 320 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs11 : checkRange rowCheck 352 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs12 : checkRange rowCheck 384 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs13 : checkRange rowCheck 416 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs14 : checkRange rowCheck 448 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs15 : checkRange rowCheck 480 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs16 : checkRange rowCheck 512 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs17 : checkRange rowCheck 544 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs18 : checkRange rowCheck 576 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pairs19 : checkRange rowCheck 608 32 = true := by
  decide +kernel

theorem pairs_part0 (k : Fin 20) :
    checkRange rowCheck ((k.val + 0) * 32) 32 = true := by
  fin_cases k
  · exact pairs00
  · exact pairs01
  · exact pairs02
  · exact pairs03
  · exact pairs04
  · exact pairs05
  · exact pairs06
  · exact pairs07
  · exact pairs08
  · exact pairs09
  · exact pairs10
  · exact pairs11
  · exact pairs12
  · exact pairs13
  · exact pairs14
  · exact pairs15
  · exact pairs16
  · exact pairs17
  · exact pairs18
  · exact pairs19

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck
