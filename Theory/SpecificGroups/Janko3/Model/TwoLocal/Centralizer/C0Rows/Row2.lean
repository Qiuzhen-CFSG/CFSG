module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Tables

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 0 of the C chain

Finite permutation certificates for the fixed word-generated J₃ two-local
candidates. The retained ATLAS action is on 6156 letters. Packed maps are
checked against words in the preceding generators; all transition identities
are checked by the Lean kernel on every letter. The generating Python script
is discovery and code generation only, and contributes no proof premise.

Source: GLS, volume 3, Table 5.3h, printed p.269; ATLAS J3G1-p6156B0.
-/

namespace Sporadic.Janko3.TwoLocal.CentralizerCertificate
open Theory.GroupTheory OrderCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

private theorem C0Step_2_0 :
    C0Gen 2 * C0Rep 0 =
      C0Rep (C0Act 2 0) * evalWord C1Gen (C0Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_1 :
    C0Gen 2 * C0Rep 1 =
      C0Rep (C0Act 2 1) * evalWord C1Gen (C0Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_2 :
    C0Gen 2 * C0Rep 2 =
      C0Rep (C0Act 2 2) * evalWord C1Gen (C0Factor 2 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_3 :
    C0Gen 2 * C0Rep 3 =
      C0Rep (C0Act 2 3) * evalWord C1Gen (C0Factor 2 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_4 :
    C0Gen 2 * C0Rep 4 =
      C0Rep (C0Act 2 4) * evalWord C1Gen (C0Factor 2 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_5 :
    C0Gen 2 * C0Rep 5 =
      C0Rep (C0Act 2 5) * evalWord C1Gen (C0Factor 2 5) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_6 :
    C0Gen 2 * C0Rep 6 =
      C0Rep (C0Act 2 6) * evalWord C1Gen (C0Factor 2 6) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_7 :
    C0Gen 2 * C0Rep 7 =
      C0Rep (C0Act 2 7) * evalWord C1Gen (C0Factor 2 7) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_8 :
    C0Gen 2 * C0Rep 8 =
      C0Rep (C0Act 2 8) * evalWord C1Gen (C0Factor 2 8) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_9 :
    C0Gen 2 * C0Rep 9 =
      C0Rep (C0Act 2 9) * evalWord C1Gen (C0Factor 2 9) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_10 :
    C0Gen 2 * C0Rep 10 =
      C0Rep (C0Act 2 10) * evalWord C1Gen (C0Factor 2 10) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_11 :
    C0Gen 2 * C0Rep 11 =
      C0Rep (C0Act 2 11) * evalWord C1Gen (C0Factor 2 11) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_12 :
    C0Gen 2 * C0Rep 12 =
      C0Rep (C0Act 2 12) * evalWord C1Gen (C0Factor 2 12) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_13 :
    C0Gen 2 * C0Rep 13 =
      C0Rep (C0Act 2 13) * evalWord C1Gen (C0Factor 2 13) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_14 :
    C0Gen 2 * C0Rep 14 =
      C0Rep (C0Act 2 14) * evalWord C1Gen (C0Factor 2 14) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_2_15 :
    C0Gen 2 * C0Rep 15 =
      C0Rep (C0Act 2 15) * evalWord C1Gen (C0Factor 2 15) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem C0Step_row2 (r : Fin 16) :
    C0Gen 2 * C0Rep r = C0Rep (C0Act 2 r) * evalWord C1Gen (C0Factor 2 r) := by
  fin_cases r
  · exact C0Step_2_0
  · exact C0Step_2_1
  · exact C0Step_2_2
  · exact C0Step_2_3
  · exact C0Step_2_4
  · exact C0Step_2_5
  · exact C0Step_2_6
  · exact C0Step_2_7
  · exact C0Step_2_8
  · exact C0Step_2_9
  · exact C0Step_2_10
  · exact C0Step_2_11
  · exact C0Step_2_12
  · exact C0Step_2_13
  · exact C0Step_2_14
  · exact C0Step_2_15

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
