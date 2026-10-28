module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Q0
import Mathlib.Tactic.FinCases

/-!
# Relative normality of the order-32 core candidate

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

@[expose] public def QConjWord : Fin 10 → Fin 10 → List (Fin 10)
  | 0, 0 => [0]
  | 0, 1 => [1]
  | 0, 2 => [2]
  | 0, 3 => [3]
  | 0, 4 => [4]
  | 0, 5 => [0]
  | 0, 6 => [1]
  | 0, 7 => [2]
  | 0, 8 => [3]
  | 0, 9 => [4]
  | 1, 0 => [0]
  | 1, 1 => [1]
  | 1, 2 => [2]
  | 1, 3 => [3]
  | 1, 4 => [4]
  | 1, 5 => [0]
  | 1, 6 => [1]
  | 1, 7 => [2]
  | 1, 8 => [3]
  | 1, 9 => [4]
  | 2, 0 => [0]
  | 2, 1 => [2]
  | 2, 2 => [1]
  | 2, 3 => [4]
  | 2, 4 => [3]
  | 2, 5 => [0]
  | 2, 6 => [2]
  | 2, 7 => [1]
  | 2, 8 => [4]
  | 2, 9 => [3]
  | 3, 0 => [0]
  | 3, 1 => [1]
  | 3, 2 => [3, 4, 2, 1]
  | 3, 3 => [4]
  | 3, 4 => [3, 0]
  | 3, 5 => [0]
  | 3, 6 => [1]
  | 3, 7 => [3, 4, 2, 1]
  | 3, 8 => [4]
  | 3, 9 => [3, 0]
  | 4, 0 => [0]
  | 4, 1 => [3, 4, 2, 1]
  | 4, 2 => [4, 0]
  | 4, 3 => [1]
  | 4, 4 => [3]
  | 4, 5 => [0]
  | 4, 6 => [3, 4, 2, 1]
  | 4, 7 => [4, 0]
  | 4, 8 => [1]
  | 4, 9 => [3]
  | 5, 0 => [0]
  | 5, 1 => [1]
  | 5, 2 => [2]
  | 5, 3 => [3]
  | 5, 4 => [4]
  | 5, 5 => [0]
  | 5, 6 => [1]
  | 5, 7 => [2]
  | 5, 8 => [3]
  | 5, 9 => [4]
  | 6, 0 => [0]
  | 6, 1 => [1]
  | 6, 2 => [2]
  | 6, 3 => [3]
  | 6, 4 => [4]
  | 6, 5 => [0]
  | 6, 6 => [1]
  | 6, 7 => [2]
  | 6, 8 => [3]
  | 6, 9 => [4]
  | 7, 0 => [0]
  | 7, 1 => [2]
  | 7, 2 => [1]
  | 7, 3 => [4]
  | 7, 4 => [3]
  | 7, 5 => [0]
  | 7, 6 => [2]
  | 7, 7 => [1]
  | 7, 8 => [4]
  | 7, 9 => [3]
  | 8, 0 => [0]
  | 8, 1 => [1]
  | 8, 2 => [4, 3, 2, 1]
  | 8, 3 => [4, 0]
  | 8, 4 => [3]
  | 8, 5 => [0]
  | 8, 6 => [1]
  | 8, 7 => [4, 3, 2, 1]
  | 8, 8 => [4, 0]
  | 8, 9 => [3]
  | 9, 0 => [0]
  | 9, 1 => [3]
  | 9, 2 => [4, 3, 2, 1]
  | 9, 3 => [4]
  | 9, 4 => [2, 0]
  | 9, 5 => [0]
  | 9, 6 => [3]
  | 9, 7 => [4, 3, 2, 1]
  | 9, 8 => [4]
  | 9, 9 => [2, 0]

private theorem QConj_0_0 :
    C0Gen 0 * Q0Gen 0 * (C0Gen 0)⁻¹ = evalWord Q0Gen (QConjWord 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_0_1 :
    C0Gen 0 * Q0Gen 1 * (C0Gen 0)⁻¹ = evalWord Q0Gen (QConjWord 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_0_2 :
    C0Gen 0 * Q0Gen 2 * (C0Gen 0)⁻¹ = evalWord Q0Gen (QConjWord 0 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_0_3 :
    C0Gen 0 * Q0Gen 3 * (C0Gen 0)⁻¹ = evalWord Q0Gen (QConjWord 0 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_0_4 :
    C0Gen 0 * Q0Gen 4 * (C0Gen 0)⁻¹ = evalWord Q0Gen (QConjWord 0 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_0_5 :
    C0Gen 0 * Q0Gen 5 * (C0Gen 0)⁻¹ = evalWord Q0Gen (QConjWord 0 5) := QConj_0_0

private theorem QConj_0_6 :
    C0Gen 0 * Q0Gen 6 * (C0Gen 0)⁻¹ = evalWord Q0Gen (QConjWord 0 6) := QConj_0_1

private theorem QConj_0_7 :
    C0Gen 0 * Q0Gen 7 * (C0Gen 0)⁻¹ = evalWord Q0Gen (QConjWord 0 7) := QConj_0_2

private theorem QConj_0_8 :
    C0Gen 0 * Q0Gen 8 * (C0Gen 0)⁻¹ = evalWord Q0Gen (QConjWord 0 8) := QConj_0_3

private theorem QConj_0_9 :
    C0Gen 0 * Q0Gen 9 * (C0Gen 0)⁻¹ = evalWord Q0Gen (QConjWord 0 9) := QConj_0_4

private theorem QConj_1_0 :
    C0Gen 1 * Q0Gen 0 * (C0Gen 1)⁻¹ = evalWord Q0Gen (QConjWord 1 0) := QConj_0_0

private theorem QConj_1_1 :
    C0Gen 1 * Q0Gen 1 * (C0Gen 1)⁻¹ = evalWord Q0Gen (QConjWord 1 1) := QConj_0_1

private theorem QConj_1_2 :
    C0Gen 1 * Q0Gen 2 * (C0Gen 1)⁻¹ = evalWord Q0Gen (QConjWord 1 2) := QConj_0_2

private theorem QConj_1_3 :
    C0Gen 1 * Q0Gen 3 * (C0Gen 1)⁻¹ = evalWord Q0Gen (QConjWord 1 3) := QConj_0_3

private theorem QConj_1_4 :
    C0Gen 1 * Q0Gen 4 * (C0Gen 1)⁻¹ = evalWord Q0Gen (QConjWord 1 4) := QConj_0_4

private theorem QConj_1_5 :
    C0Gen 1 * Q0Gen 5 * (C0Gen 1)⁻¹ = evalWord Q0Gen (QConjWord 1 5) := QConj_0_0

private theorem QConj_1_6 :
    C0Gen 1 * Q0Gen 6 * (C0Gen 1)⁻¹ = evalWord Q0Gen (QConjWord 1 6) := QConj_0_1

private theorem QConj_1_7 :
    C0Gen 1 * Q0Gen 7 * (C0Gen 1)⁻¹ = evalWord Q0Gen (QConjWord 1 7) := QConj_0_2

private theorem QConj_1_8 :
    C0Gen 1 * Q0Gen 8 * (C0Gen 1)⁻¹ = evalWord Q0Gen (QConjWord 1 8) := QConj_0_3

private theorem QConj_1_9 :
    C0Gen 1 * Q0Gen 9 * (C0Gen 1)⁻¹ = evalWord Q0Gen (QConjWord 1 9) := QConj_0_4

private theorem QConj_2_0 :
    C0Gen 2 * Q0Gen 0 * (C0Gen 2)⁻¹ = evalWord Q0Gen (QConjWord 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_2_1 :
    C0Gen 2 * Q0Gen 1 * (C0Gen 2)⁻¹ = evalWord Q0Gen (QConjWord 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_2_2 :
    C0Gen 2 * Q0Gen 2 * (C0Gen 2)⁻¹ = evalWord Q0Gen (QConjWord 2 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_2_3 :
    C0Gen 2 * Q0Gen 3 * (C0Gen 2)⁻¹ = evalWord Q0Gen (QConjWord 2 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_2_4 :
    C0Gen 2 * Q0Gen 4 * (C0Gen 2)⁻¹ = evalWord Q0Gen (QConjWord 2 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_2_5 :
    C0Gen 2 * Q0Gen 5 * (C0Gen 2)⁻¹ = evalWord Q0Gen (QConjWord 2 5) := QConj_2_0

private theorem QConj_2_6 :
    C0Gen 2 * Q0Gen 6 * (C0Gen 2)⁻¹ = evalWord Q0Gen (QConjWord 2 6) := QConj_2_1

private theorem QConj_2_7 :
    C0Gen 2 * Q0Gen 7 * (C0Gen 2)⁻¹ = evalWord Q0Gen (QConjWord 2 7) := QConj_2_2

private theorem QConj_2_8 :
    C0Gen 2 * Q0Gen 8 * (C0Gen 2)⁻¹ = evalWord Q0Gen (QConjWord 2 8) := QConj_2_3

private theorem QConj_2_9 :
    C0Gen 2 * Q0Gen 9 * (C0Gen 2)⁻¹ = evalWord Q0Gen (QConjWord 2 9) := QConj_2_4

private theorem QConj_3_0 :
    C0Gen 3 * Q0Gen 0 * (C0Gen 3)⁻¹ = evalWord Q0Gen (QConjWord 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_3_1 :
    C0Gen 3 * Q0Gen 1 * (C0Gen 3)⁻¹ = evalWord Q0Gen (QConjWord 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_3_2 :
    C0Gen 3 * Q0Gen 2 * (C0Gen 3)⁻¹ = evalWord Q0Gen (QConjWord 3 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_3_3 :
    C0Gen 3 * Q0Gen 3 * (C0Gen 3)⁻¹ = evalWord Q0Gen (QConjWord 3 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_3_4 :
    C0Gen 3 * Q0Gen 4 * (C0Gen 3)⁻¹ = evalWord Q0Gen (QConjWord 3 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_3_5 :
    C0Gen 3 * Q0Gen 5 * (C0Gen 3)⁻¹ = evalWord Q0Gen (QConjWord 3 5) := QConj_3_0

private theorem QConj_3_6 :
    C0Gen 3 * Q0Gen 6 * (C0Gen 3)⁻¹ = evalWord Q0Gen (QConjWord 3 6) := QConj_3_1

private theorem QConj_3_7 :
    C0Gen 3 * Q0Gen 7 * (C0Gen 3)⁻¹ = evalWord Q0Gen (QConjWord 3 7) := QConj_3_2

private theorem QConj_3_8 :
    C0Gen 3 * Q0Gen 8 * (C0Gen 3)⁻¹ = evalWord Q0Gen (QConjWord 3 8) := QConj_3_3

private theorem QConj_3_9 :
    C0Gen 3 * Q0Gen 9 * (C0Gen 3)⁻¹ = evalWord Q0Gen (QConjWord 3 9) := QConj_3_4

private theorem QConj_4_0 :
    C0Gen 4 * Q0Gen 0 * (C0Gen 4)⁻¹ = evalWord Q0Gen (QConjWord 4 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_4_1 :
    C0Gen 4 * Q0Gen 1 * (C0Gen 4)⁻¹ = evalWord Q0Gen (QConjWord 4 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_4_2 :
    C0Gen 4 * Q0Gen 2 * (C0Gen 4)⁻¹ = evalWord Q0Gen (QConjWord 4 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_4_3 :
    C0Gen 4 * Q0Gen 3 * (C0Gen 4)⁻¹ = evalWord Q0Gen (QConjWord 4 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_4_4 :
    C0Gen 4 * Q0Gen 4 * (C0Gen 4)⁻¹ = evalWord Q0Gen (QConjWord 4 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_4_5 :
    C0Gen 4 * Q0Gen 5 * (C0Gen 4)⁻¹ = evalWord Q0Gen (QConjWord 4 5) := QConj_4_0

private theorem QConj_4_6 :
    C0Gen 4 * Q0Gen 6 * (C0Gen 4)⁻¹ = evalWord Q0Gen (QConjWord 4 6) := QConj_4_1

private theorem QConj_4_7 :
    C0Gen 4 * Q0Gen 7 * (C0Gen 4)⁻¹ = evalWord Q0Gen (QConjWord 4 7) := QConj_4_2

private theorem QConj_4_8 :
    C0Gen 4 * Q0Gen 8 * (C0Gen 4)⁻¹ = evalWord Q0Gen (QConjWord 4 8) := QConj_4_3

private theorem QConj_4_9 :
    C0Gen 4 * Q0Gen 9 * (C0Gen 4)⁻¹ = evalWord Q0Gen (QConjWord 4 9) := QConj_4_4

private theorem QConj_5_0 :
    C0Gen 5 * Q0Gen 0 * (C0Gen 5)⁻¹ = evalWord Q0Gen (QConjWord 5 0) := QConj_0_0

private theorem QConj_5_1 :
    C0Gen 5 * Q0Gen 1 * (C0Gen 5)⁻¹ = evalWord Q0Gen (QConjWord 5 1) := QConj_0_1

private theorem QConj_5_2 :
    C0Gen 5 * Q0Gen 2 * (C0Gen 5)⁻¹ = evalWord Q0Gen (QConjWord 5 2) := QConj_0_2

private theorem QConj_5_3 :
    C0Gen 5 * Q0Gen 3 * (C0Gen 5)⁻¹ = evalWord Q0Gen (QConjWord 5 3) := QConj_0_3

private theorem QConj_5_4 :
    C0Gen 5 * Q0Gen 4 * (C0Gen 5)⁻¹ = evalWord Q0Gen (QConjWord 5 4) := QConj_0_4

private theorem QConj_5_5 :
    C0Gen 5 * Q0Gen 5 * (C0Gen 5)⁻¹ = evalWord Q0Gen (QConjWord 5 5) := QConj_0_0

private theorem QConj_5_6 :
    C0Gen 5 * Q0Gen 6 * (C0Gen 5)⁻¹ = evalWord Q0Gen (QConjWord 5 6) := QConj_0_1

private theorem QConj_5_7 :
    C0Gen 5 * Q0Gen 7 * (C0Gen 5)⁻¹ = evalWord Q0Gen (QConjWord 5 7) := QConj_0_2

private theorem QConj_5_8 :
    C0Gen 5 * Q0Gen 8 * (C0Gen 5)⁻¹ = evalWord Q0Gen (QConjWord 5 8) := QConj_0_3

private theorem QConj_5_9 :
    C0Gen 5 * Q0Gen 9 * (C0Gen 5)⁻¹ = evalWord Q0Gen (QConjWord 5 9) := QConj_0_4

private theorem QConj_6_0 :
    C0Gen 6 * Q0Gen 0 * (C0Gen 6)⁻¹ = evalWord Q0Gen (QConjWord 6 0) := QConj_0_0

private theorem QConj_6_1 :
    C0Gen 6 * Q0Gen 1 * (C0Gen 6)⁻¹ = evalWord Q0Gen (QConjWord 6 1) := QConj_0_1

private theorem QConj_6_2 :
    C0Gen 6 * Q0Gen 2 * (C0Gen 6)⁻¹ = evalWord Q0Gen (QConjWord 6 2) := QConj_0_2

private theorem QConj_6_3 :
    C0Gen 6 * Q0Gen 3 * (C0Gen 6)⁻¹ = evalWord Q0Gen (QConjWord 6 3) := QConj_0_3

private theorem QConj_6_4 :
    C0Gen 6 * Q0Gen 4 * (C0Gen 6)⁻¹ = evalWord Q0Gen (QConjWord 6 4) := QConj_0_4

private theorem QConj_6_5 :
    C0Gen 6 * Q0Gen 5 * (C0Gen 6)⁻¹ = evalWord Q0Gen (QConjWord 6 5) := QConj_0_0

private theorem QConj_6_6 :
    C0Gen 6 * Q0Gen 6 * (C0Gen 6)⁻¹ = evalWord Q0Gen (QConjWord 6 6) := QConj_0_1

private theorem QConj_6_7 :
    C0Gen 6 * Q0Gen 7 * (C0Gen 6)⁻¹ = evalWord Q0Gen (QConjWord 6 7) := QConj_0_2

private theorem QConj_6_8 :
    C0Gen 6 * Q0Gen 8 * (C0Gen 6)⁻¹ = evalWord Q0Gen (QConjWord 6 8) := QConj_0_3

private theorem QConj_6_9 :
    C0Gen 6 * Q0Gen 9 * (C0Gen 6)⁻¹ = evalWord Q0Gen (QConjWord 6 9) := QConj_0_4

private theorem QConj_7_0 :
    C0Gen 7 * Q0Gen 0 * (C0Gen 7)⁻¹ = evalWord Q0Gen (QConjWord 7 0) := QConj_2_0

private theorem QConj_7_1 :
    C0Gen 7 * Q0Gen 1 * (C0Gen 7)⁻¹ = evalWord Q0Gen (QConjWord 7 1) := QConj_2_1

private theorem QConj_7_2 :
    C0Gen 7 * Q0Gen 2 * (C0Gen 7)⁻¹ = evalWord Q0Gen (QConjWord 7 2) := QConj_2_2

private theorem QConj_7_3 :
    C0Gen 7 * Q0Gen 3 * (C0Gen 7)⁻¹ = evalWord Q0Gen (QConjWord 7 3) := QConj_2_3

private theorem QConj_7_4 :
    C0Gen 7 * Q0Gen 4 * (C0Gen 7)⁻¹ = evalWord Q0Gen (QConjWord 7 4) := QConj_2_4

private theorem QConj_7_5 :
    C0Gen 7 * Q0Gen 5 * (C0Gen 7)⁻¹ = evalWord Q0Gen (QConjWord 7 5) := QConj_2_0

private theorem QConj_7_6 :
    C0Gen 7 * Q0Gen 6 * (C0Gen 7)⁻¹ = evalWord Q0Gen (QConjWord 7 6) := QConj_2_1

private theorem QConj_7_7 :
    C0Gen 7 * Q0Gen 7 * (C0Gen 7)⁻¹ = evalWord Q0Gen (QConjWord 7 7) := QConj_2_2

private theorem QConj_7_8 :
    C0Gen 7 * Q0Gen 8 * (C0Gen 7)⁻¹ = evalWord Q0Gen (QConjWord 7 8) := QConj_2_3

private theorem QConj_7_9 :
    C0Gen 7 * Q0Gen 9 * (C0Gen 7)⁻¹ = evalWord Q0Gen (QConjWord 7 9) := QConj_2_4

private theorem QConj_8_0 :
    C0Gen 8 * Q0Gen 0 * (C0Gen 8)⁻¹ = evalWord Q0Gen (QConjWord 8 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_8_1 :
    C0Gen 8 * Q0Gen 1 * (C0Gen 8)⁻¹ = evalWord Q0Gen (QConjWord 8 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_8_2 :
    C0Gen 8 * Q0Gen 2 * (C0Gen 8)⁻¹ = evalWord Q0Gen (QConjWord 8 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_8_3 :
    C0Gen 8 * Q0Gen 3 * (C0Gen 8)⁻¹ = evalWord Q0Gen (QConjWord 8 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_8_4 :
    C0Gen 8 * Q0Gen 4 * (C0Gen 8)⁻¹ = evalWord Q0Gen (QConjWord 8 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_8_5 :
    C0Gen 8 * Q0Gen 5 * (C0Gen 8)⁻¹ = evalWord Q0Gen (QConjWord 8 5) := QConj_8_0

private theorem QConj_8_6 :
    C0Gen 8 * Q0Gen 6 * (C0Gen 8)⁻¹ = evalWord Q0Gen (QConjWord 8 6) := QConj_8_1

private theorem QConj_8_7 :
    C0Gen 8 * Q0Gen 7 * (C0Gen 8)⁻¹ = evalWord Q0Gen (QConjWord 8 7) := QConj_8_2

private theorem QConj_8_8 :
    C0Gen 8 * Q0Gen 8 * (C0Gen 8)⁻¹ = evalWord Q0Gen (QConjWord 8 8) := QConj_8_3

private theorem QConj_8_9 :
    C0Gen 8 * Q0Gen 9 * (C0Gen 8)⁻¹ = evalWord Q0Gen (QConjWord 8 9) := QConj_8_4

private theorem QConj_9_0 :
    C0Gen 9 * Q0Gen 0 * (C0Gen 9)⁻¹ = evalWord Q0Gen (QConjWord 9 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_9_1 :
    C0Gen 9 * Q0Gen 1 * (C0Gen 9)⁻¹ = evalWord Q0Gen (QConjWord 9 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_9_2 :
    C0Gen 9 * Q0Gen 2 * (C0Gen 9)⁻¹ = evalWord Q0Gen (QConjWord 9 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_9_3 :
    C0Gen 9 * Q0Gen 3 * (C0Gen 9)⁻¹ = evalWord Q0Gen (QConjWord 9 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_9_4 :
    C0Gen 9 * Q0Gen 4 * (C0Gen 9)⁻¹ = evalWord Q0Gen (QConjWord 9 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem QConj_9_5 :
    C0Gen 9 * Q0Gen 5 * (C0Gen 9)⁻¹ = evalWord Q0Gen (QConjWord 9 5) := QConj_9_0

private theorem QConj_9_6 :
    C0Gen 9 * Q0Gen 6 * (C0Gen 9)⁻¹ = evalWord Q0Gen (QConjWord 9 6) := QConj_9_1

private theorem QConj_9_7 :
    C0Gen 9 * Q0Gen 7 * (C0Gen 9)⁻¹ = evalWord Q0Gen (QConjWord 9 7) := QConj_9_2

private theorem QConj_9_8 :
    C0Gen 9 * Q0Gen 8 * (C0Gen 9)⁻¹ = evalWord Q0Gen (QConjWord 9 8) := QConj_9_3

private theorem QConj_9_9 :
    C0Gen 9 * Q0Gen 9 * (C0Gen 9)⁻¹ = evalWord Q0Gen (QConjWord 9 9) := QConj_9_4

public theorem QConj (i j : Fin 10) :
    C0Gen i * Q0Gen j * (C0Gen i)⁻¹ = evalWord Q0Gen (QConjWord i j) := by
  fin_cases i <;> fin_cases j
  · exact QConj_0_0
  · exact QConj_0_1
  · exact QConj_0_2
  · exact QConj_0_3
  · exact QConj_0_4
  · exact QConj_0_5
  · exact QConj_0_6
  · exact QConj_0_7
  · exact QConj_0_8
  · exact QConj_0_9
  · exact QConj_1_0
  · exact QConj_1_1
  · exact QConj_1_2
  · exact QConj_1_3
  · exact QConj_1_4
  · exact QConj_1_5
  · exact QConj_1_6
  · exact QConj_1_7
  · exact QConj_1_8
  · exact QConj_1_9
  · exact QConj_2_0
  · exact QConj_2_1
  · exact QConj_2_2
  · exact QConj_2_3
  · exact QConj_2_4
  · exact QConj_2_5
  · exact QConj_2_6
  · exact QConj_2_7
  · exact QConj_2_8
  · exact QConj_2_9
  · exact QConj_3_0
  · exact QConj_3_1
  · exact QConj_3_2
  · exact QConj_3_3
  · exact QConj_3_4
  · exact QConj_3_5
  · exact QConj_3_6
  · exact QConj_3_7
  · exact QConj_3_8
  · exact QConj_3_9
  · exact QConj_4_0
  · exact QConj_4_1
  · exact QConj_4_2
  · exact QConj_4_3
  · exact QConj_4_4
  · exact QConj_4_5
  · exact QConj_4_6
  · exact QConj_4_7
  · exact QConj_4_8
  · exact QConj_4_9
  · exact QConj_5_0
  · exact QConj_5_1
  · exact QConj_5_2
  · exact QConj_5_3
  · exact QConj_5_4
  · exact QConj_5_5
  · exact QConj_5_6
  · exact QConj_5_7
  · exact QConj_5_8
  · exact QConj_5_9
  · exact QConj_6_0
  · exact QConj_6_1
  · exact QConj_6_2
  · exact QConj_6_3
  · exact QConj_6_4
  · exact QConj_6_5
  · exact QConj_6_6
  · exact QConj_6_7
  · exact QConj_6_8
  · exact QConj_6_9
  · exact QConj_7_0
  · exact QConj_7_1
  · exact QConj_7_2
  · exact QConj_7_3
  · exact QConj_7_4
  · exact QConj_7_5
  · exact QConj_7_6
  · exact QConj_7_7
  · exact QConj_7_8
  · exact QConj_7_9
  · exact QConj_8_0
  · exact QConj_8_1
  · exact QConj_8_2
  · exact QConj_8_3
  · exact QConj_8_4
  · exact QConj_8_5
  · exact QConj_8_6
  · exact QConj_8_7
  · exact QConj_8_8
  · exact QConj_8_9
  · exact QConj_9_0
  · exact QConj_9_1
  · exact QConj_9_2
  · exact QConj_9_3
  · exact QConj_9_4
  · exact QConj_9_5
  · exact QConj_9_6
  · exact QConj_9_7
  · exact QConj_9_8
  · exact QConj_9_9

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
