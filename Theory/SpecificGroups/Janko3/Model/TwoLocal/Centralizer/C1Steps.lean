module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C2

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 1 of the C chain

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

@[expose] public def C1RepWord : Fin 5 → List (Fin 4)
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | 4 => [0, 1]

@[expose] public def C1Rep (i : Fin 5) : Equiv.Perm (Fin 6156) :=
  evalWord C1Gen (C1RepWord i)

@[expose] public def C1Point : Fin 5 → Fin 6156
  | 0 => 1707
  | 1 => 2620
  | 2 => 5411
  | 3 => 5575
  | 4 => 3781

@[expose] public def C1Act : Fin 4 → Fin 5 → Fin 5
  | 0, 0 => 1
  | 0, 1 => 2
  | 0, 2 => 4
  | 0, 3 => 0
  | 0, 4 => 3
  | 1, 0 => 2
  | 1, 1 => 0
  | 1, 2 => 4
  | 1, 3 => 1
  | 1, 4 => 3
  | 2, 0 => 3
  | 2, 1 => 0
  | 2, 2 => 1
  | 2, 3 => 4
  | 2, 4 => 2
  | 3, 0 => 1
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 4
  | 3, 4 => 2

@[expose] public def C1Factor : Fin 4 → Fin 5 → List (Fin 4)
  | 0, 0 => []
  | 0, 1 => [0, 0]
  | 0, 2 => []
  | 0, 3 => []
  | 0, 4 => [0]
  | 1, 0 => []
  | 1, 1 => [1]
  | 1, 2 => [1, 0, 1]
  | 1, 3 => [2, 1]
  | 1, 4 => []
  | 2, 0 => []
  | 2, 1 => []
  | 2, 2 => [2, 2]
  | 2, 3 => [2]
  | 2, 4 => []
  | 3, 0 => [1]
  | 3, 1 => [1, 0]
  | 3, 2 => []
  | 3, 3 => []
  | 3, 4 => [0, 1, 0]

public theorem C1Rep_mem (r : Fin 5) : C1Rep r ∈ C1H := ⟨_, rfl⟩
public theorem C1Rep_base : C1Rep 0 = 1 := rfl
public theorem C1Rep_point : ∀ r, C1Rep r 1707 = C1Point r := by decide +kernel
public theorem C1Point_injective : Function.Injective C1Point := by decide +kernel
public theorem C2H_fix : ∀ h : C2H, (h : Equiv.Perm (Fin 6156)) 1707 = 1707 :=
  wordSubgroup_fix_of_gen_fix C2Gen C2Inv C2Inv_spec (by decide +kernel)

private theorem C1Step_0_0 :
    C1Gen 0 * C1Rep 0 =
      C1Rep (C1Act 0 0) * evalWord C2Gen (C1Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_0_1 :
    C1Gen 0 * C1Rep 1 =
      C1Rep (C1Act 0 1) * evalWord C2Gen (C1Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_0_2 :
    C1Gen 0 * C1Rep 2 =
      C1Rep (C1Act 0 2) * evalWord C2Gen (C1Factor 0 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_0_3 :
    C1Gen 0 * C1Rep 3 =
      C1Rep (C1Act 0 3) * evalWord C2Gen (C1Factor 0 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_0_4 :
    C1Gen 0 * C1Rep 4 =
      C1Rep (C1Act 0 4) * evalWord C2Gen (C1Factor 0 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_1_0 :
    C1Gen 1 * C1Rep 0 =
      C1Rep (C1Act 1 0) * evalWord C2Gen (C1Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_1_1 :
    C1Gen 1 * C1Rep 1 =
      C1Rep (C1Act 1 1) * evalWord C2Gen (C1Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_1_2 :
    C1Gen 1 * C1Rep 2 =
      C1Rep (C1Act 1 2) * evalWord C2Gen (C1Factor 1 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_1_3 :
    C1Gen 1 * C1Rep 3 =
      C1Rep (C1Act 1 3) * evalWord C2Gen (C1Factor 1 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_1_4 :
    C1Gen 1 * C1Rep 4 =
      C1Rep (C1Act 1 4) * evalWord C2Gen (C1Factor 1 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_2_0 :
    C1Gen 2 * C1Rep 0 =
      C1Rep (C1Act 2 0) * evalWord C2Gen (C1Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_2_1 :
    C1Gen 2 * C1Rep 1 =
      C1Rep (C1Act 2 1) * evalWord C2Gen (C1Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_2_2 :
    C1Gen 2 * C1Rep 2 =
      C1Rep (C1Act 2 2) * evalWord C2Gen (C1Factor 2 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_2_3 :
    C1Gen 2 * C1Rep 3 =
      C1Rep (C1Act 2 3) * evalWord C2Gen (C1Factor 2 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_2_4 :
    C1Gen 2 * C1Rep 4 =
      C1Rep (C1Act 2 4) * evalWord C2Gen (C1Factor 2 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_3_0 :
    C1Gen 3 * C1Rep 0 =
      C1Rep (C1Act 3 0) * evalWord C2Gen (C1Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_3_1 :
    C1Gen 3 * C1Rep 1 =
      C1Rep (C1Act 3 1) * evalWord C2Gen (C1Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_3_2 :
    C1Gen 3 * C1Rep 2 =
      C1Rep (C1Act 3 2) * evalWord C2Gen (C1Factor 3 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_3_3 :
    C1Gen 3 * C1Rep 3 =
      C1Rep (C1Act 3 3) * evalWord C2Gen (C1Factor 3 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C1Step_3_4 :
    C1Gen 3 * C1Rep 4 =
      C1Rep (C1Act 3 4) * evalWord C2Gen (C1Factor 3 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem C1Step (i : Fin 4) (r : Fin 5) :
    C1Gen i * C1Rep r =
      C1Rep (C1Act i r) * evalWord C2Gen (C1Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact C1Step_0_0
  · exact C1Step_0_1
  · exact C1Step_0_2
  · exact C1Step_0_3
  · exact C1Step_0_4
  · exact C1Step_1_0
  · exact C1Step_1_1
  · exact C1Step_1_2
  · exact C1Step_1_3
  · exact C1Step_1_4
  · exact C1Step_2_0
  · exact C1Step_2_1
  · exact C1Step_2_2
  · exact C1Step_2_3
  · exact C1Step_2_4
  · exact C1Step_3_0
  · exact C1Step_3_1
  · exact C1Step_3_2
  · exact C1Step_3_3
  · exact C1Step_3_4

public theorem C1H_card : Nat.card C1H = 5 * Nat.card C2H :=
  wordSubgroup_card_eq_mul_next C1Gen C1Inv C1Inv_spec
    C2Gen C2Inv C2Inv_spec C1Rep C1Act C1Factor
    1707 C1Point 0 C1Rep_mem C2H_le C1Rep_base
    C1Rep_point C1Point_injective C2H_fix C1Step

public theorem C1H_decompose (g : C1H) :
    ∃ r, ∃ k : C2H, (g : Equiv.Perm (Fin 6156)) = C1Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : C2H, evalWord C1Gen w = C1Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, C1Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨C1Act i r, ⟨evalWord C2Gen (C1Factor i r) * k,
      C2H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change C1Gen i * evalWord C1Gen w = _
    rw [hk, ← mul_assoc, C1Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
