module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Evaluator
import Mathlib.Tactic.FinCases

/-!
# Held ClassB closure rows 11008–11024

Each sixteen-row certificate checks the original four-point trajectories.
Serial declaration elaboration bounds memory; the late-row sample used
2.5 GB including import preparation. The last block wraps around.
Source: the retained HeG1-P1.M and HeG1-p2058B0 tables.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Part43

set_option Elab.async false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block00 : Fast.block 11008 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem block01 : Fast.block 11024 16 = true := by
  decide +kernel

/-- Every original representative in this bounded interval is closed. -/
public theorem closedAt (i : Fin 11025)
    (hi : 11008 ≤ i.val ∧ i.val < 11264) : ClosedAt i := by
  have h : ∀ j : Fin 2, Fast.block (11008 + j.val * 16) 16 = true := by
    intro j
    fin_cases j
    · exact block00
    · exact block01
  have hj : (i.val - 11008) / 16 < 2 := by omega
  exact Fast.block_sound (h ⟨(i.val - 11008) / 16, hj⟩) i (by dsimp only; omega)

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Part43
