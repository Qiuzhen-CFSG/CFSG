module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Q2

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 1 of the Q chain

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

@[expose] public def Q1RepWord : Fin 2 → List (Fin 4)
  | 0 => []
  | 1 => [0]

@[expose] public def Q1Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord Q1Gen (Q1RepWord i)

@[expose] public def Q1Point : Fin 2 → Fin 6156
  | 0 => 566
  | 1 => 1210

@[expose] public def Q1Act : Fin 4 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 2, 0 => 1
  | 2, 1 => 0
  | 3, 0 => 1
  | 3, 1 => 0

@[expose] public def Q1Factor : Fin 4 → Fin 2 → List (Fin 2)
  | 0, 0 => []
  | 0, 1 => [0, 0]
  | 1, 0 => [1]
  | 1, 1 => [0]
  | 2, 0 => [0, 0]
  | 2, 1 => []
  | 3, 0 => [1]
  | 3, 1 => [0]

public theorem Q1Rep_mem (r : Fin 2) : Q1Rep r ∈ Q1H := ⟨_, rfl⟩
public theorem Q1Rep_base : Q1Rep 0 = 1 := rfl
public theorem Q1Rep_point : ∀ r, Q1Rep r 566 = Q1Point r := by decide +kernel
public theorem Q1Point_injective : Function.Injective Q1Point := by decide +kernel
public theorem Q2H_fix : ∀ h : Q2H, (h : Equiv.Perm (Fin 6156)) 566 = 566 :=
  wordSubgroup_fix_of_gen_fix Q2Gen Q2Inv Q2Inv_spec (by decide +kernel)

private theorem Q1Step_0_0 :
    Q1Gen 0 * Q1Rep 0 =
      Q1Rep (Q1Act 0 0) * evalWord Q2Gen (Q1Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q1Step_0_1 :
    Q1Gen 0 * Q1Rep 1 =
      Q1Rep (Q1Act 0 1) * evalWord Q2Gen (Q1Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q1Step_1_0 :
    Q1Gen 1 * Q1Rep 0 =
      Q1Rep (Q1Act 1 0) * evalWord Q2Gen (Q1Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q1Step_1_1 :
    Q1Gen 1 * Q1Rep 1 =
      Q1Rep (Q1Act 1 1) * evalWord Q2Gen (Q1Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q1Step_2_0 :
    Q1Gen 2 * Q1Rep 0 =
      Q1Rep (Q1Act 2 0) * evalWord Q2Gen (Q1Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q1Step_2_1 :
    Q1Gen 2 * Q1Rep 1 =
      Q1Rep (Q1Act 2 1) * evalWord Q2Gen (Q1Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q1Step_3_0 :
    Q1Gen 3 * Q1Rep 0 =
      Q1Rep (Q1Act 3 0) * evalWord Q2Gen (Q1Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q1Step_3_1 :
    Q1Gen 3 * Q1Rep 1 =
      Q1Rep (Q1Act 3 1) * evalWord Q2Gen (Q1Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem Q1Step (i : Fin 4) (r : Fin 2) :
    Q1Gen i * Q1Rep r =
      Q1Rep (Q1Act i r) * evalWord Q2Gen (Q1Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact Q1Step_0_0
  · exact Q1Step_0_1
  · exact Q1Step_1_0
  · exact Q1Step_1_1
  · exact Q1Step_2_0
  · exact Q1Step_2_1
  · exact Q1Step_3_0
  · exact Q1Step_3_1

public theorem Q1H_card : Nat.card Q1H = 2 * Nat.card Q2H :=
  wordSubgroup_card_eq_mul_next Q1Gen Q1Inv Q1Inv_spec
    Q2Gen Q2Inv Q2Inv_spec Q1Rep Q1Act Q1Factor
    566 Q1Point 0 Q1Rep_mem Q2H_le Q1Rep_base
    Q1Rep_point Q1Point_injective Q2H_fix Q1Step

public theorem Q1H_decompose (g : Q1H) :
    ∃ r, ∃ k : Q2H, (g : Equiv.Perm (Fin 6156)) = Q1Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : Q2H, evalWord Q1Gen w = Q1Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, Q1Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨Q1Act i r, ⟨evalWord Q2Gen (Q1Factor i r) * k,
      Q2H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change Q1Gen i * evalWord Q1Gen w = _
    rw [hk, ← mul_assoc, Q1Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
