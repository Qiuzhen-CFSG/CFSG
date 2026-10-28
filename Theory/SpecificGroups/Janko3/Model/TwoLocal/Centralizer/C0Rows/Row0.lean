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

private theorem C0Step_0_0 :
    C0Gen 0 * C0Rep 0 =
      C0Rep (C0Act 0 0) * evalWord C1Gen (C0Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_1 :
    C0Gen 0 * C0Rep 1 =
      C0Rep (C0Act 0 1) * evalWord C1Gen (C0Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_2 :
    C0Gen 0 * C0Rep 2 =
      C0Rep (C0Act 0 2) * evalWord C1Gen (C0Factor 0 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_3 :
    C0Gen 0 * C0Rep 3 =
      C0Rep (C0Act 0 3) * evalWord C1Gen (C0Factor 0 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_4 :
    C0Gen 0 * C0Rep 4 =
      C0Rep (C0Act 0 4) * evalWord C1Gen (C0Factor 0 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_5 :
    C0Gen 0 * C0Rep 5 =
      C0Rep (C0Act 0 5) * evalWord C1Gen (C0Factor 0 5) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_6 :
    C0Gen 0 * C0Rep 6 =
      C0Rep (C0Act 0 6) * evalWord C1Gen (C0Factor 0 6) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_7 :
    C0Gen 0 * C0Rep 7 =
      C0Rep (C0Act 0 7) * evalWord C1Gen (C0Factor 0 7) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_8 :
    C0Gen 0 * C0Rep 8 =
      C0Rep (C0Act 0 8) * evalWord C1Gen (C0Factor 0 8) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_9 :
    C0Gen 0 * C0Rep 9 =
      C0Rep (C0Act 0 9) * evalWord C1Gen (C0Factor 0 9) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_10 :
    C0Gen 0 * C0Rep 10 =
      C0Rep (C0Act 0 10) * evalWord C1Gen (C0Factor 0 10) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_11 :
    C0Gen 0 * C0Rep 11 =
      C0Rep (C0Act 0 11) * evalWord C1Gen (C0Factor 0 11) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_12 :
    C0Gen 0 * C0Rep 12 =
      C0Rep (C0Act 0 12) * evalWord C1Gen (C0Factor 0 12) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_13 :
    C0Gen 0 * C0Rep 13 =
      C0Rep (C0Act 0 13) * evalWord C1Gen (C0Factor 0 13) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_14 :
    C0Gen 0 * C0Rep 14 =
      C0Rep (C0Act 0 14) * evalWord C1Gen (C0Factor 0 14) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C0Step_0_15 :
    C0Gen 0 * C0Rep 15 =
      C0Rep (C0Act 0 15) * evalWord C1Gen (C0Factor 0 15) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem C0Step_row0 (r : Fin 16) :
    C0Gen 0 * C0Rep r = C0Rep (C0Act 0 r) * evalWord C1Gen (C0Factor 0 r) := by
  fin_cases r
  · exact C0Step_0_0
  · exact C0Step_0_1
  · exact C0Step_0_2
  · exact C0Step_0_3
  · exact C0Step_0_4
  · exact C0Step_0_5
  · exact C0Step_0_6
  · exact C0Step_0_7
  · exact C0Step_0_8
  · exact C0Step_0_9
  · exact C0Step_0_10
  · exact C0Step_0_11
  · exact C0Step_0_12
  · exact C0Step_0_13
  · exact C0Step_0_14
  · exact C0Step_0_15

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
