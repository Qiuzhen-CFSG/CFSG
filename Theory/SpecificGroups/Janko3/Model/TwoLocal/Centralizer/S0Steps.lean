module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S1

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 0 of the S chain

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

@[expose] public def S0RepWord : Fin 4 → List (Fin 10)
  | 0 => []
  | 1 => [1]
  | 2 => [2]
  | 3 => [2, 1]

@[expose] public def S0Rep (i : Fin 4) : Equiv.Perm (Fin 6156) :=
  evalWord S0Gen (S0RepWord i)

@[expose] public def S0Point : Fin 4 → Fin 6156
  | 0 => 1453
  | 1 => 2827
  | 2 => 4158
  | 3 => 5640

@[expose] public def S0Act : Fin 10 → Fin 4 → Fin 4
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 3
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 2
  | 1, 3 => 3
  | 2, 0 => 2
  | 2, 1 => 3
  | 2, 2 => 0
  | 2, 3 => 1
  | 3, 0 => 2
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 1
  | 4, 0 => 0
  | 4, 1 => 1
  | 4, 2 => 3
  | 4, 3 => 2
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 3
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 2
  | 6, 3 => 3
  | 7, 0 => 2
  | 7, 1 => 3
  | 7, 2 => 0
  | 7, 3 => 1
  | 8, 0 => 2
  | 8, 1 => 3
  | 8, 2 => 0
  | 8, 3 => 1
  | 9, 0 => 0
  | 9, 1 => 1
  | 9, 2 => 3
  | 9, 3 => 2

@[expose] public def S0Factor : Fin 10 → Fin 4 → List (Fin 6)
  | 0, 0 => [0, 0]
  | 0, 1 => [0, 0]
  | 0, 2 => [0, 0]
  | 0, 3 => [0, 0]
  | 1, 0 => []
  | 1, 1 => []
  | 1, 2 => [2]
  | 1, 3 => [2, 0, 0]
  | 2, 0 => []
  | 2, 1 => []
  | 2, 2 => []
  | 2, 3 => []
  | 3, 0 => [3]
  | 3, 1 => [1, 3, 1]
  | 3, 2 => [0]
  | 3, 3 => [1, 0, 1]
  | 4, 0 => [1]
  | 4, 1 => [0, 1, 0]
  | 4, 2 => [2, 1, 0]
  | 4, 3 => [2, 1, 0]
  | 5, 0 => [0, 0]
  | 5, 1 => [0, 0]
  | 5, 2 => [0, 0]
  | 5, 3 => [0, 0]
  | 6, 0 => []
  | 6, 1 => []
  | 6, 2 => [2]
  | 6, 3 => [2, 0, 0]
  | 7, 0 => []
  | 7, 1 => []
  | 7, 2 => []
  | 7, 3 => []
  | 8, 0 => [3]
  | 8, 1 => [1, 3, 1]
  | 8, 2 => [0]
  | 8, 3 => [1, 0, 1]
  | 9, 0 => [1]
  | 9, 1 => [0, 1, 0]
  | 9, 2 => [2, 1, 0]
  | 9, 3 => [2, 1, 0]

public theorem S0Rep_mem (r : Fin 4) : S0Rep r ∈ S0H := ⟨_, rfl⟩
public theorem S0Rep_base : S0Rep 0 = 1 := rfl
public theorem S0Rep_point : ∀ r, S0Rep r 1453 = S0Point r := by decide +kernel
public theorem S0Point_injective : Function.Injective S0Point := by decide +kernel
public theorem S1H_fix : ∀ h : S1H, (h : Equiv.Perm (Fin 6156)) 1453 = 1453 :=
  wordSubgroup_fix_of_gen_fix S1Gen S1Inv S1Inv_spec (by decide +kernel)

private theorem S0Step_0_0 :
    S0Gen 0 * S0Rep 0 =
      S0Rep (S0Act 0 0) * evalWord S1Gen (S0Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_0_1 :
    S0Gen 0 * S0Rep 1 =
      S0Rep (S0Act 0 1) * evalWord S1Gen (S0Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_0_2 :
    S0Gen 0 * S0Rep 2 =
      S0Rep (S0Act 0 2) * evalWord S1Gen (S0Factor 0 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_0_3 :
    S0Gen 0 * S0Rep 3 =
      S0Rep (S0Act 0 3) * evalWord S1Gen (S0Factor 0 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_1_0 :
    S0Gen 1 * S0Rep 0 =
      S0Rep (S0Act 1 0) * evalWord S1Gen (S0Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_1_1 :
    S0Gen 1 * S0Rep 1 =
      S0Rep (S0Act 1 1) * evalWord S1Gen (S0Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_1_2 :
    S0Gen 1 * S0Rep 2 =
      S0Rep (S0Act 1 2) * evalWord S1Gen (S0Factor 1 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_1_3 :
    S0Gen 1 * S0Rep 3 =
      S0Rep (S0Act 1 3) * evalWord S1Gen (S0Factor 1 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_2_0 :
    S0Gen 2 * S0Rep 0 =
      S0Rep (S0Act 2 0) * evalWord S1Gen (S0Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_2_1 :
    S0Gen 2 * S0Rep 1 =
      S0Rep (S0Act 2 1) * evalWord S1Gen (S0Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_2_2 :
    S0Gen 2 * S0Rep 2 =
      S0Rep (S0Act 2 2) * evalWord S1Gen (S0Factor 2 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_2_3 :
    S0Gen 2 * S0Rep 3 =
      S0Rep (S0Act 2 3) * evalWord S1Gen (S0Factor 2 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_3_0 :
    S0Gen 3 * S0Rep 0 =
      S0Rep (S0Act 3 0) * evalWord S1Gen (S0Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_3_1 :
    S0Gen 3 * S0Rep 1 =
      S0Rep (S0Act 3 1) * evalWord S1Gen (S0Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_3_2 :
    S0Gen 3 * S0Rep 2 =
      S0Rep (S0Act 3 2) * evalWord S1Gen (S0Factor 3 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_3_3 :
    S0Gen 3 * S0Rep 3 =
      S0Rep (S0Act 3 3) * evalWord S1Gen (S0Factor 3 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_4_0 :
    S0Gen 4 * S0Rep 0 =
      S0Rep (S0Act 4 0) * evalWord S1Gen (S0Factor 4 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_4_1 :
    S0Gen 4 * S0Rep 1 =
      S0Rep (S0Act 4 1) * evalWord S1Gen (S0Factor 4 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_4_2 :
    S0Gen 4 * S0Rep 2 =
      S0Rep (S0Act 4 2) * evalWord S1Gen (S0Factor 4 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_4_3 :
    S0Gen 4 * S0Rep 3 =
      S0Rep (S0Act 4 3) * evalWord S1Gen (S0Factor 4 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_5_0 :
    S0Gen 5 * S0Rep 0 =
      S0Rep (S0Act 5 0) * evalWord S1Gen (S0Factor 5 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_5_1 :
    S0Gen 5 * S0Rep 1 =
      S0Rep (S0Act 5 1) * evalWord S1Gen (S0Factor 5 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_5_2 :
    S0Gen 5 * S0Rep 2 =
      S0Rep (S0Act 5 2) * evalWord S1Gen (S0Factor 5 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_5_3 :
    S0Gen 5 * S0Rep 3 =
      S0Rep (S0Act 5 3) * evalWord S1Gen (S0Factor 5 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_6_0 :
    S0Gen 6 * S0Rep 0 =
      S0Rep (S0Act 6 0) * evalWord S1Gen (S0Factor 6 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_6_1 :
    S0Gen 6 * S0Rep 1 =
      S0Rep (S0Act 6 1) * evalWord S1Gen (S0Factor 6 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_6_2 :
    S0Gen 6 * S0Rep 2 =
      S0Rep (S0Act 6 2) * evalWord S1Gen (S0Factor 6 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_6_3 :
    S0Gen 6 * S0Rep 3 =
      S0Rep (S0Act 6 3) * evalWord S1Gen (S0Factor 6 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_7_0 :
    S0Gen 7 * S0Rep 0 =
      S0Rep (S0Act 7 0) * evalWord S1Gen (S0Factor 7 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_7_1 :
    S0Gen 7 * S0Rep 1 =
      S0Rep (S0Act 7 1) * evalWord S1Gen (S0Factor 7 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_7_2 :
    S0Gen 7 * S0Rep 2 =
      S0Rep (S0Act 7 2) * evalWord S1Gen (S0Factor 7 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_7_3 :
    S0Gen 7 * S0Rep 3 =
      S0Rep (S0Act 7 3) * evalWord S1Gen (S0Factor 7 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_8_0 :
    S0Gen 8 * S0Rep 0 =
      S0Rep (S0Act 8 0) * evalWord S1Gen (S0Factor 8 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_8_1 :
    S0Gen 8 * S0Rep 1 =
      S0Rep (S0Act 8 1) * evalWord S1Gen (S0Factor 8 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_8_2 :
    S0Gen 8 * S0Rep 2 =
      S0Rep (S0Act 8 2) * evalWord S1Gen (S0Factor 8 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_8_3 :
    S0Gen 8 * S0Rep 3 =
      S0Rep (S0Act 8 3) * evalWord S1Gen (S0Factor 8 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_9_0 :
    S0Gen 9 * S0Rep 0 =
      S0Rep (S0Act 9 0) * evalWord S1Gen (S0Factor 9 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_9_1 :
    S0Gen 9 * S0Rep 1 =
      S0Rep (S0Act 9 1) * evalWord S1Gen (S0Factor 9 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_9_2 :
    S0Gen 9 * S0Rep 2 =
      S0Rep (S0Act 9 2) * evalWord S1Gen (S0Factor 9 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S0Step_9_3 :
    S0Gen 9 * S0Rep 3 =
      S0Rep (S0Act 9 3) * evalWord S1Gen (S0Factor 9 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem S0Step (i : Fin 10) (r : Fin 4) :
    S0Gen i * S0Rep r =
      S0Rep (S0Act i r) * evalWord S1Gen (S0Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact S0Step_0_0
  · exact S0Step_0_1
  · exact S0Step_0_2
  · exact S0Step_0_3
  · exact S0Step_1_0
  · exact S0Step_1_1
  · exact S0Step_1_2
  · exact S0Step_1_3
  · exact S0Step_2_0
  · exact S0Step_2_1
  · exact S0Step_2_2
  · exact S0Step_2_3
  · exact S0Step_3_0
  · exact S0Step_3_1
  · exact S0Step_3_2
  · exact S0Step_3_3
  · exact S0Step_4_0
  · exact S0Step_4_1
  · exact S0Step_4_2
  · exact S0Step_4_3
  · exact S0Step_5_0
  · exact S0Step_5_1
  · exact S0Step_5_2
  · exact S0Step_5_3
  · exact S0Step_6_0
  · exact S0Step_6_1
  · exact S0Step_6_2
  · exact S0Step_6_3
  · exact S0Step_7_0
  · exact S0Step_7_1
  · exact S0Step_7_2
  · exact S0Step_7_3
  · exact S0Step_8_0
  · exact S0Step_8_1
  · exact S0Step_8_2
  · exact S0Step_8_3
  · exact S0Step_9_0
  · exact S0Step_9_1
  · exact S0Step_9_2
  · exact S0Step_9_3

public theorem S0H_card : Nat.card S0H = 4 * Nat.card S1H :=
  wordSubgroup_card_eq_mul_next S0Gen S0Inv S0Inv_spec
    S1Gen S1Inv S1Inv_spec S0Rep S0Act S0Factor
    1453 S0Point 0 S0Rep_mem S1H_le S0Rep_base
    S0Rep_point S0Point_injective S1H_fix S0Step

public theorem S0H_decompose (g : S0H) :
    ∃ r, ∃ k : S1H, (g : Equiv.Perm (Fin 6156)) = S0Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : S1H, evalWord S0Gen w = S0Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, S0Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨S0Act i r, ⟨evalWord S1Gen (S0Factor i r) * k,
      S1H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change S0Gen i * evalWord S0Gen w = _
    rw [hk, ← mul_assoc, S0Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
