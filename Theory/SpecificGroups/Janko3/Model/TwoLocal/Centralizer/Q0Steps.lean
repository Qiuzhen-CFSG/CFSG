module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Q1

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 0 of the Q chain

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

@[expose] public def Q0RepWord : Fin 4 → List (Fin 10)
  | 0 => []
  | 1 => [2]
  | 2 => [3]
  | 3 => [3, 2]

@[expose] public def Q0Rep (i : Fin 4) : Equiv.Perm (Fin 6156) :=
  evalWord Q0Gen (Q0RepWord i)

@[expose] public def Q0Point : Fin 4 → Fin 6156
  | 0 => 438
  | 1 => 4069
  | 2 => 2370
  | 3 => 4093

@[expose] public def Q0Act : Fin 10 → Fin 4 → Fin 4
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 3
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => 2
  | 1, 3 => 3
  | 2, 0 => 1
  | 2, 1 => 0
  | 2, 2 => 3
  | 2, 3 => 2
  | 3, 0 => 2
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 1
  | 4, 0 => 1
  | 4, 1 => 0
  | 4, 2 => 3
  | 4, 3 => 2
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 3
  | 6, 0 => 0
  | 6, 1 => 1
  | 6, 2 => 2
  | 6, 3 => 3
  | 7, 0 => 1
  | 7, 1 => 0
  | 7, 2 => 3
  | 7, 3 => 2
  | 8, 0 => 2
  | 8, 1 => 3
  | 8, 2 => 0
  | 8, 3 => 1
  | 9, 0 => 1
  | 9, 1 => 0
  | 9, 2 => 3
  | 9, 3 => 2

@[expose] public def Q0Factor : Fin 10 → Fin 4 → List (Fin 4)
  | 0, 0 => [0, 0]
  | 0, 1 => [0, 0]
  | 0, 2 => [0, 0]
  | 0, 3 => [0, 0]
  | 1, 0 => [1]
  | 1, 1 => [1, 0, 0]
  | 1, 2 => [1, 0, 0]
  | 1, 3 => [1]
  | 2, 0 => []
  | 2, 1 => []
  | 2, 2 => [0, 0]
  | 2, 3 => [0, 0]
  | 3, 0 => []
  | 3, 1 => []
  | 3, 2 => []
  | 3, 3 => []
  | 4, 0 => [2]
  | 4, 1 => [0]
  | 4, 2 => [0]
  | 4, 3 => [2]
  | 5, 0 => [0, 0]
  | 5, 1 => [0, 0]
  | 5, 2 => [0, 0]
  | 5, 3 => [0, 0]
  | 6, 0 => [1]
  | 6, 1 => [1, 0, 0]
  | 6, 2 => [1, 0, 0]
  | 6, 3 => [1]
  | 7, 0 => []
  | 7, 1 => []
  | 7, 2 => [0, 0]
  | 7, 3 => [0, 0]
  | 8, 0 => []
  | 8, 1 => []
  | 8, 2 => []
  | 8, 3 => []
  | 9, 0 => [2]
  | 9, 1 => [0]
  | 9, 2 => [0]
  | 9, 3 => [2]

public theorem Q0Rep_mem (r : Fin 4) : Q0Rep r ∈ Q0H := ⟨_, rfl⟩
public theorem Q0Rep_base : Q0Rep 0 = 1 := rfl
public theorem Q0Rep_point : ∀ r, Q0Rep r 438 = Q0Point r := by decide +kernel
public theorem Q0Point_injective : Function.Injective Q0Point := by decide +kernel
public theorem Q1H_fix : ∀ h : Q1H, (h : Equiv.Perm (Fin 6156)) 438 = 438 :=
  wordSubgroup_fix_of_gen_fix Q1Gen Q1Inv Q1Inv_spec (by decide +kernel)

private theorem Q0Step_0_0 :
    Q0Gen 0 * Q0Rep 0 =
      Q0Rep (Q0Act 0 0) * evalWord Q1Gen (Q0Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_0_1 :
    Q0Gen 0 * Q0Rep 1 =
      Q0Rep (Q0Act 0 1) * evalWord Q1Gen (Q0Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_0_2 :
    Q0Gen 0 * Q0Rep 2 =
      Q0Rep (Q0Act 0 2) * evalWord Q1Gen (Q0Factor 0 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_0_3 :
    Q0Gen 0 * Q0Rep 3 =
      Q0Rep (Q0Act 0 3) * evalWord Q1Gen (Q0Factor 0 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_1_0 :
    Q0Gen 1 * Q0Rep 0 =
      Q0Rep (Q0Act 1 0) * evalWord Q1Gen (Q0Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_1_1 :
    Q0Gen 1 * Q0Rep 1 =
      Q0Rep (Q0Act 1 1) * evalWord Q1Gen (Q0Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_1_2 :
    Q0Gen 1 * Q0Rep 2 =
      Q0Rep (Q0Act 1 2) * evalWord Q1Gen (Q0Factor 1 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_1_3 :
    Q0Gen 1 * Q0Rep 3 =
      Q0Rep (Q0Act 1 3) * evalWord Q1Gen (Q0Factor 1 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_2_0 :
    Q0Gen 2 * Q0Rep 0 =
      Q0Rep (Q0Act 2 0) * evalWord Q1Gen (Q0Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_2_1 :
    Q0Gen 2 * Q0Rep 1 =
      Q0Rep (Q0Act 2 1) * evalWord Q1Gen (Q0Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_2_2 :
    Q0Gen 2 * Q0Rep 2 =
      Q0Rep (Q0Act 2 2) * evalWord Q1Gen (Q0Factor 2 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_2_3 :
    Q0Gen 2 * Q0Rep 3 =
      Q0Rep (Q0Act 2 3) * evalWord Q1Gen (Q0Factor 2 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_3_0 :
    Q0Gen 3 * Q0Rep 0 =
      Q0Rep (Q0Act 3 0) * evalWord Q1Gen (Q0Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_3_1 :
    Q0Gen 3 * Q0Rep 1 =
      Q0Rep (Q0Act 3 1) * evalWord Q1Gen (Q0Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_3_2 :
    Q0Gen 3 * Q0Rep 2 =
      Q0Rep (Q0Act 3 2) * evalWord Q1Gen (Q0Factor 3 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_3_3 :
    Q0Gen 3 * Q0Rep 3 =
      Q0Rep (Q0Act 3 3) * evalWord Q1Gen (Q0Factor 3 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_4_0 :
    Q0Gen 4 * Q0Rep 0 =
      Q0Rep (Q0Act 4 0) * evalWord Q1Gen (Q0Factor 4 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_4_1 :
    Q0Gen 4 * Q0Rep 1 =
      Q0Rep (Q0Act 4 1) * evalWord Q1Gen (Q0Factor 4 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_4_2 :
    Q0Gen 4 * Q0Rep 2 =
      Q0Rep (Q0Act 4 2) * evalWord Q1Gen (Q0Factor 4 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_4_3 :
    Q0Gen 4 * Q0Rep 3 =
      Q0Rep (Q0Act 4 3) * evalWord Q1Gen (Q0Factor 4 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_5_0 :
    Q0Gen 5 * Q0Rep 0 =
      Q0Rep (Q0Act 5 0) * evalWord Q1Gen (Q0Factor 5 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_5_1 :
    Q0Gen 5 * Q0Rep 1 =
      Q0Rep (Q0Act 5 1) * evalWord Q1Gen (Q0Factor 5 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_5_2 :
    Q0Gen 5 * Q0Rep 2 =
      Q0Rep (Q0Act 5 2) * evalWord Q1Gen (Q0Factor 5 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_5_3 :
    Q0Gen 5 * Q0Rep 3 =
      Q0Rep (Q0Act 5 3) * evalWord Q1Gen (Q0Factor 5 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_6_0 :
    Q0Gen 6 * Q0Rep 0 =
      Q0Rep (Q0Act 6 0) * evalWord Q1Gen (Q0Factor 6 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_6_1 :
    Q0Gen 6 * Q0Rep 1 =
      Q0Rep (Q0Act 6 1) * evalWord Q1Gen (Q0Factor 6 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_6_2 :
    Q0Gen 6 * Q0Rep 2 =
      Q0Rep (Q0Act 6 2) * evalWord Q1Gen (Q0Factor 6 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_6_3 :
    Q0Gen 6 * Q0Rep 3 =
      Q0Rep (Q0Act 6 3) * evalWord Q1Gen (Q0Factor 6 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_7_0 :
    Q0Gen 7 * Q0Rep 0 =
      Q0Rep (Q0Act 7 0) * evalWord Q1Gen (Q0Factor 7 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_7_1 :
    Q0Gen 7 * Q0Rep 1 =
      Q0Rep (Q0Act 7 1) * evalWord Q1Gen (Q0Factor 7 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_7_2 :
    Q0Gen 7 * Q0Rep 2 =
      Q0Rep (Q0Act 7 2) * evalWord Q1Gen (Q0Factor 7 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_7_3 :
    Q0Gen 7 * Q0Rep 3 =
      Q0Rep (Q0Act 7 3) * evalWord Q1Gen (Q0Factor 7 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_8_0 :
    Q0Gen 8 * Q0Rep 0 =
      Q0Rep (Q0Act 8 0) * evalWord Q1Gen (Q0Factor 8 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_8_1 :
    Q0Gen 8 * Q0Rep 1 =
      Q0Rep (Q0Act 8 1) * evalWord Q1Gen (Q0Factor 8 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_8_2 :
    Q0Gen 8 * Q0Rep 2 =
      Q0Rep (Q0Act 8 2) * evalWord Q1Gen (Q0Factor 8 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_8_3 :
    Q0Gen 8 * Q0Rep 3 =
      Q0Rep (Q0Act 8 3) * evalWord Q1Gen (Q0Factor 8 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_9_0 :
    Q0Gen 9 * Q0Rep 0 =
      Q0Rep (Q0Act 9 0) * evalWord Q1Gen (Q0Factor 9 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_9_1 :
    Q0Gen 9 * Q0Rep 1 =
      Q0Rep (Q0Act 9 1) * evalWord Q1Gen (Q0Factor 9 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_9_2 :
    Q0Gen 9 * Q0Rep 2 =
      Q0Rep (Q0Act 9 2) * evalWord Q1Gen (Q0Factor 9 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q0Step_9_3 :
    Q0Gen 9 * Q0Rep 3 =
      Q0Rep (Q0Act 9 3) * evalWord Q1Gen (Q0Factor 9 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem Q0Step (i : Fin 10) (r : Fin 4) :
    Q0Gen i * Q0Rep r =
      Q0Rep (Q0Act i r) * evalWord Q1Gen (Q0Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact Q0Step_0_0
  · exact Q0Step_0_1
  · exact Q0Step_0_2
  · exact Q0Step_0_3
  · exact Q0Step_1_0
  · exact Q0Step_1_1
  · exact Q0Step_1_2
  · exact Q0Step_1_3
  · exact Q0Step_2_0
  · exact Q0Step_2_1
  · exact Q0Step_2_2
  · exact Q0Step_2_3
  · exact Q0Step_3_0
  · exact Q0Step_3_1
  · exact Q0Step_3_2
  · exact Q0Step_3_3
  · exact Q0Step_4_0
  · exact Q0Step_4_1
  · exact Q0Step_4_2
  · exact Q0Step_4_3
  · exact Q0Step_5_0
  · exact Q0Step_5_1
  · exact Q0Step_5_2
  · exact Q0Step_5_3
  · exact Q0Step_6_0
  · exact Q0Step_6_1
  · exact Q0Step_6_2
  · exact Q0Step_6_3
  · exact Q0Step_7_0
  · exact Q0Step_7_1
  · exact Q0Step_7_2
  · exact Q0Step_7_3
  · exact Q0Step_8_0
  · exact Q0Step_8_1
  · exact Q0Step_8_2
  · exact Q0Step_8_3
  · exact Q0Step_9_0
  · exact Q0Step_9_1
  · exact Q0Step_9_2
  · exact Q0Step_9_3

public theorem Q0H_card : Nat.card Q0H = 4 * Nat.card Q1H :=
  wordSubgroup_card_eq_mul_next Q0Gen Q0Inv Q0Inv_spec
    Q1Gen Q1Inv Q1Inv_spec Q0Rep Q0Act Q0Factor
    438 Q0Point 0 Q0Rep_mem Q1H_le Q0Rep_base
    Q0Rep_point Q0Point_injective Q1H_fix Q0Step

public theorem Q0H_decompose (g : Q0H) :
    ∃ r, ∃ k : Q1H, (g : Equiv.Perm (Fin 6156)) = Q0Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : Q1H, evalWord Q0Gen w = Q0Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, Q0Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨Q0Act i r, ⟨evalWord Q1Gen (Q0Factor i r) * k,
      Q1H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change Q0Gen i * evalWord Q0Gen w = _
    rw [hk, ← mul_assoc, Q0Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
