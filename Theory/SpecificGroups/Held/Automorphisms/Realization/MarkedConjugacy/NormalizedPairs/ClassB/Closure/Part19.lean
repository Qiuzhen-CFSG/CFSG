module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Evaluator
import Mathlib.Tactic.FinCases

/-!
# Held ClassB closure rows 4864–5119

Each sixteen-row certificate checks the original four-point trajectories.
Serial declaration elaboration bounds memory; the late-row sample used
2.5 GB including import preparation. The last block wraps around.
Source: the retained HeG1-P1.M and HeG1-p2058B0 tables.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Part19

set_option Elab.async false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block00 : Fast.block 4864 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block01 : Fast.block 4880 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block02 : Fast.block 4896 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block03 : Fast.block 4912 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block04 : Fast.block 4928 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block05 : Fast.block 4944 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block06 : Fast.block 4960 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block07 : Fast.block 4976 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block08 : Fast.block 4992 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block09 : Fast.block 5008 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block10 : Fast.block 5024 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block11 : Fast.block 5040 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block12 : Fast.block 5056 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block13 : Fast.block 5072 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block14 : Fast.block 5088 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block15 : Fast.block 5104 16 = true := by
  decide +kernel

/-- Every original representative in this bounded interval is closed. -/
public theorem closedAt (i : Fin 11025)
    (hi : 4864 ≤ i.val ∧ i.val < 5120) : ClosedAt i := by
  have h : ∀ j : Fin 16, Fast.block (4864 + j.val * 16) 16 = true := by
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
  have hj : (i.val - 4864) / 16 < 16 := by omega
  exact Fast.block_sound (h ⟨(i.val - 4864) / 16, hj⟩) i (by dsimp only; omega)

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Part19
