module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Evaluator
import Mathlib.Tactic.FinCases

/-!
# Held ClassB closure rows 1024–1279

Each sixteen-row certificate checks the original four-point trajectories.
Serial declaration elaboration bounds memory; the late-row sample used
2.5 GB including import preparation. The last block wraps around.
Source: the retained HeG1-P1.M and HeG1-p2058B0 tables.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Part04

set_option Elab.async false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block00 : Fast.block 1024 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block01 : Fast.block 1040 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block02 : Fast.block 1056 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block03 : Fast.block 1072 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block04 : Fast.block 1088 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block05 : Fast.block 1104 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block06 : Fast.block 1120 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block07 : Fast.block 1136 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block08 : Fast.block 1152 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block09 : Fast.block 1168 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block10 : Fast.block 1184 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block11 : Fast.block 1200 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block12 : Fast.block 1216 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block13 : Fast.block 1232 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block14 : Fast.block 1248 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block15 : Fast.block 1264 16 = true := by
  decide +kernel

/-- Every original representative in this bounded interval is closed. -/
public theorem closedAt (i : Fin 11025)
    (hi : 1024 ≤ i.val ∧ i.val < 1280) : ClosedAt i := by
  have h : ∀ j : Fin 16, Fast.block (1024 + j.val * 16) 16 = true := by
    intro j
    fin_cases j
    · exact block00
    · exact block01
    · exact block02
    · exact block03
    · exact block04
    · exact block05
    · exact block06
    · exact block07
    · exact block08
    · exact block09
    · exact block10
    · exact block11
    · exact block12
    · exact block13
    · exact block14
    · exact block15
  have hj : (i.val - 1024) / 16 < 16 := by omega
  exact Fast.block_sound (h ⟨(i.val - 1024) / 16, hj⟩) i (by dsimp only; omega)

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Part04
