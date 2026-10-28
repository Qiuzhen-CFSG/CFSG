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

private theorem C0Step_3_0 :
    C0Gen 3 * C0Rep 0 =
      C0Rep (C0Act 3 0) * evalWord C1Gen (C0Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_1 :
    C0Gen 3 * C0Rep 1 =
      C0Rep (C0Act 3 1) * evalWord C1Gen (C0Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_2 :
    C0Gen 3 * C0Rep 2 =
      C0Rep (C0Act 3 2) * evalWord C1Gen (C0Factor 3 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_3 :
    C0Gen 3 * C0Rep 3 =
      C0Rep (C0Act 3 3) * evalWord C1Gen (C0Factor 3 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_4 :
    C0Gen 3 * C0Rep 4 =
      C0Rep (C0Act 3 4) * evalWord C1Gen (C0Factor 3 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_5 :
    C0Gen 3 * C0Rep 5 =
      C0Rep (C0Act 3 5) * evalWord C1Gen (C0Factor 3 5) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_6 :
    C0Gen 3 * C0Rep 6 =
      C0Rep (C0Act 3 6) * evalWord C1Gen (C0Factor 3 6) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_7 :
    C0Gen 3 * C0Rep 7 =
      C0Rep (C0Act 3 7) * evalWord C1Gen (C0Factor 3 7) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_8 :
    C0Gen 3 * C0Rep 8 =
      C0Rep (C0Act 3 8) * evalWord C1Gen (C0Factor 3 8) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_9 :
    C0Gen 3 * C0Rep 9 =
      C0Rep (C0Act 3 9) * evalWord C1Gen (C0Factor 3 9) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_10 :
    C0Gen 3 * C0Rep 10 =
      C0Rep (C0Act 3 10) * evalWord C1Gen (C0Factor 3 10) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_11 :
    C0Gen 3 * C0Rep 11 =
      C0Rep (C0Act 3 11) * evalWord C1Gen (C0Factor 3 11) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_12 :
    C0Gen 3 * C0Rep 12 =
      C0Rep (C0Act 3 12) * evalWord C1Gen (C0Factor 3 12) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_13 :
    C0Gen 3 * C0Rep 13 =
      C0Rep (C0Act 3 13) * evalWord C1Gen (C0Factor 3 13) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_14 :
    C0Gen 3 * C0Rep 14 =
      C0Rep (C0Act 3 14) * evalWord C1Gen (C0Factor 3 14) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_3_15 :
    C0Gen 3 * C0Rep 15 =
      C0Rep (C0Act 3 15) * evalWord C1Gen (C0Factor 3 15) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem C0Step_row3 (r : Fin 16) :
    C0Gen 3 * C0Rep r = C0Rep (C0Act 3 r) * evalWord C1Gen (C0Factor 3 r) := by
  fin_cases r
  · exact C0Step_3_0
  · exact C0Step_3_1
  · exact C0Step_3_2
  · exact C0Step_3_3
  · exact C0Step_3_4
  · exact C0Step_3_5
  · exact C0Step_3_6
  · exact C0Step_3_7
  · exact C0Step_3_8
  · exact C0Step_3_9
  · exact C0Step_3_10
  · exact C0Step_3_11
  · exact C0Step_3_12
  · exact C0Step_3_13
  · exact C0Step_3_14
  · exact C0Step_3_15

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
