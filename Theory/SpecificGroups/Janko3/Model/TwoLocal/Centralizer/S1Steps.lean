module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S2

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 1 of the S chain

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

@[expose] public def S1RepWord : Fin 2 → List (Fin 6)
  | 0 => []
  | 1 => [0]

@[expose] public def S1Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord S1Gen (S1RepWord i)

@[expose] public def S1Point : Fin 2 → Fin 6156
  | 0 => 2431
  | 1 => 5536

@[expose] public def S1Act : Fin 6 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 0
  | 1, 1 => 1
  | 2, 0 => 0
  | 2, 1 => 1
  | 3, 0 => 1
  | 3, 1 => 0
  | 4, 0 => 0
  | 4, 1 => 1
  | 5, 0 => 0
  | 5, 1 => 1

@[expose] public def S1Factor : Fin 6 → Fin 2 → List (Fin 8)
  | 0, 0 => []
  | 0, 1 => [2]
  | 1, 0 => [0]
  | 1, 1 => [3, 2]
  | 2, 0 => [1]
  | 2, 1 => [3, 1, 0]
  | 3, 0 => [2]
  | 3, 1 => []
  | 4, 0 => [0]
  | 4, 1 => [3, 2]
  | 5, 0 => [1]
  | 5, 1 => [3, 1, 0]

public theorem S1Rep_mem (r : Fin 2) : S1Rep r ∈ S1H := ⟨_, rfl⟩
public theorem S1Rep_base : S1Rep 0 = 1 := rfl
public theorem S1Rep_point : ∀ r, S1Rep r 2431 = S1Point r := by decide +kernel
public theorem S1Point_injective : Function.Injective S1Point := by decide +kernel
public theorem S2H_fix : ∀ h : S2H, (h : Equiv.Perm (Fin 6156)) 2431 = 2431 :=
  wordSubgroup_fix_of_gen_fix S2Gen S2Inv S2Inv_spec (by decide +kernel)

private theorem S1Step_0_0 :
    S1Gen 0 * S1Rep 0 =
      S1Rep (S1Act 0 0) * evalWord S2Gen (S1Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_0_1 :
    S1Gen 0 * S1Rep 1 =
      S1Rep (S1Act 0 1) * evalWord S2Gen (S1Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_1_0 :
    S1Gen 1 * S1Rep 0 =
      S1Rep (S1Act 1 0) * evalWord S2Gen (S1Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_1_1 :
    S1Gen 1 * S1Rep 1 =
      S1Rep (S1Act 1 1) * evalWord S2Gen (S1Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_2_0 :
    S1Gen 2 * S1Rep 0 =
      S1Rep (S1Act 2 0) * evalWord S2Gen (S1Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_2_1 :
    S1Gen 2 * S1Rep 1 =
      S1Rep (S1Act 2 1) * evalWord S2Gen (S1Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_3_0 :
    S1Gen 3 * S1Rep 0 =
      S1Rep (S1Act 3 0) * evalWord S2Gen (S1Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_3_1 :
    S1Gen 3 * S1Rep 1 =
      S1Rep (S1Act 3 1) * evalWord S2Gen (S1Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_4_0 :
    S1Gen 4 * S1Rep 0 =
      S1Rep (S1Act 4 0) * evalWord S2Gen (S1Factor 4 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_4_1 :
    S1Gen 4 * S1Rep 1 =
      S1Rep (S1Act 4 1) * evalWord S2Gen (S1Factor 4 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_5_0 :
    S1Gen 5 * S1Rep 0 =
      S1Rep (S1Act 5 0) * evalWord S2Gen (S1Factor 5 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S1Step_5_1 :
    S1Gen 5 * S1Rep 1 =
      S1Rep (S1Act 5 1) * evalWord S2Gen (S1Factor 5 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem S1Step (i : Fin 6) (r : Fin 2) :
    S1Gen i * S1Rep r =
      S1Rep (S1Act i r) * evalWord S2Gen (S1Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact S1Step_0_0
  · exact S1Step_0_1
  · exact S1Step_1_0
  · exact S1Step_1_1
  · exact S1Step_2_0
  · exact S1Step_2_1
  · exact S1Step_3_0
  · exact S1Step_3_1
  · exact S1Step_4_0
  · exact S1Step_4_1
  · exact S1Step_5_0
  · exact S1Step_5_1

public theorem S1H_card : Nat.card S1H = 2 * Nat.card S2H :=
  wordSubgroup_card_eq_mul_next S1Gen S1Inv S1Inv_spec
    S2Gen S2Inv S2Inv_spec S1Rep S1Act S1Factor
    2431 S1Point 0 S1Rep_mem S2H_le S1Rep_base
    S1Rep_point S1Point_injective S2H_fix S1Step

public theorem S1H_decompose (g : S1H) :
    ∃ r, ∃ k : S2H, (g : Equiv.Perm (Fin 6156)) = S1Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : S2H, evalWord S1Gen w = S1Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, S1Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨S1Act i r, ⟨evalWord S2Gen (S1Factor i r) * k,
      S2H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change S1Gen i * evalWord S1Gen w = _
    rw [hk, ← mul_assoc, S1Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
