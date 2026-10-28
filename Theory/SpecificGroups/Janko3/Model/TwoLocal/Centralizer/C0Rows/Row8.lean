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

private theorem C0Step_8_0 :
    C0Gen 8 * C0Rep 0 =
      C0Rep (C0Act 8 0) * evalWord C1Gen (C0Factor 8 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_1 :
    C0Gen 8 * C0Rep 1 =
      C0Rep (C0Act 8 1) * evalWord C1Gen (C0Factor 8 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_2 :
    C0Gen 8 * C0Rep 2 =
      C0Rep (C0Act 8 2) * evalWord C1Gen (C0Factor 8 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_3 :
    C0Gen 8 * C0Rep 3 =
      C0Rep (C0Act 8 3) * evalWord C1Gen (C0Factor 8 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_4 :
    C0Gen 8 * C0Rep 4 =
      C0Rep (C0Act 8 4) * evalWord C1Gen (C0Factor 8 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_5 :
    C0Gen 8 * C0Rep 5 =
      C0Rep (C0Act 8 5) * evalWord C1Gen (C0Factor 8 5) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_6 :
    C0Gen 8 * C0Rep 6 =
      C0Rep (C0Act 8 6) * evalWord C1Gen (C0Factor 8 6) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_7 :
    C0Gen 8 * C0Rep 7 =
      C0Rep (C0Act 8 7) * evalWord C1Gen (C0Factor 8 7) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_8 :
    C0Gen 8 * C0Rep 8 =
      C0Rep (C0Act 8 8) * evalWord C1Gen (C0Factor 8 8) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_9 :
    C0Gen 8 * C0Rep 9 =
      C0Rep (C0Act 8 9) * evalWord C1Gen (C0Factor 8 9) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_10 :
    C0Gen 8 * C0Rep 10 =
      C0Rep (C0Act 8 10) * evalWord C1Gen (C0Factor 8 10) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_11 :
    C0Gen 8 * C0Rep 11 =
      C0Rep (C0Act 8 11) * evalWord C1Gen (C0Factor 8 11) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_12 :
    C0Gen 8 * C0Rep 12 =
      C0Rep (C0Act 8 12) * evalWord C1Gen (C0Factor 8 12) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_13 :
    C0Gen 8 * C0Rep 13 =
      C0Rep (C0Act 8 13) * evalWord C1Gen (C0Factor 8 13) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_14 :
    C0Gen 8 * C0Rep 14 =
      C0Rep (C0Act 8 14) * evalWord C1Gen (C0Factor 8 14) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_8_15 :
    C0Gen 8 * C0Rep 15 =
      C0Rep (C0Act 8 15) * evalWord C1Gen (C0Factor 8 15) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem C0Step_row8 (r : Fin 16) :
    C0Gen 8 * C0Rep r = C0Rep (C0Act 8 r) * evalWord C1Gen (C0Factor 8 r) := by
  fin_cases r
  · exact C0Step_8_0
  · exact C0Step_8_1
  · exact C0Step_8_2
  · exact C0Step_8_3
  · exact C0Step_8_4
  · exact C0Step_8_5
  · exact C0Step_8_6
  · exact C0Step_8_7
  · exact C0Step_8_8
  · exact C0Step_8_9
  · exact C0Step_8_10
  · exact C0Step_8_11
  · exact C0Step_8_12
  · exact C0Step_8_13
  · exact C0Step_8_14
  · exact C0Step_8_15

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
