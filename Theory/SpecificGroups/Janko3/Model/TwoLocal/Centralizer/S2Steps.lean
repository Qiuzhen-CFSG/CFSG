module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S3

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 2 of the S chain

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

@[expose] public def S2RepWord : Fin 2 → List (Fin 8)
  | 0 => []
  | 1 => [0]

@[expose] public def S2Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord S2Gen (S2RepWord i)

@[expose] public def S2Point : Fin 2 → Fin 6156
  | 0 => 175
  | 1 => 1073

@[expose] public def S2Act : Fin 8 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 2, 0 => 1
  | 2, 1 => 0
  | 3, 0 => 0
  | 3, 1 => 1
  | 4, 0 => 1
  | 4, 1 => 0
  | 5, 0 => 1
  | 5, 1 => 0
  | 6, 0 => 1
  | 6, 1 => 0
  | 7, 0 => 0
  | 7, 1 => 1

@[expose] public def S2Factor : Fin 8 → Fin 2 → List (Fin 6)
  | 0, 0 => []
  | 0, 1 => []
  | 1, 0 => [1]
  | 1, 1 => [1]
  | 2, 0 => [2]
  | 2, 1 => [2]
  | 3, 0 => [0]
  | 3, 1 => [0]
  | 4, 0 => []
  | 4, 1 => []
  | 5, 0 => [1]
  | 5, 1 => [1]
  | 6, 0 => [2]
  | 6, 1 => [2]
  | 7, 0 => [0]
  | 7, 1 => [0]

public theorem S2Rep_mem (r : Fin 2) : S2Rep r ∈ S2H := ⟨_, rfl⟩
public theorem S2Rep_base : S2Rep 0 = 1 := rfl
public theorem S2Rep_point : ∀ r, S2Rep r 175 = S2Point r := by decide +kernel
public theorem S2Point_injective : Function.Injective S2Point := by decide +kernel
public theorem S3H_fix : ∀ h : S3H, (h : Equiv.Perm (Fin 6156)) 175 = 175 :=
  wordSubgroup_fix_of_gen_fix S3Gen S3Inv S3Inv_spec (by decide +kernel)

private theorem S2Step_0_0 :
    S2Gen 0 * S2Rep 0 =
      S2Rep (S2Act 0 0) * evalWord S3Gen (S2Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_0_1 :
    S2Gen 0 * S2Rep 1 =
      S2Rep (S2Act 0 1) * evalWord S3Gen (S2Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_1_0 :
    S2Gen 1 * S2Rep 0 =
      S2Rep (S2Act 1 0) * evalWord S3Gen (S2Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_1_1 :
    S2Gen 1 * S2Rep 1 =
      S2Rep (S2Act 1 1) * evalWord S3Gen (S2Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_2_0 :
    S2Gen 2 * S2Rep 0 =
      S2Rep (S2Act 2 0) * evalWord S3Gen (S2Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_2_1 :
    S2Gen 2 * S2Rep 1 =
      S2Rep (S2Act 2 1) * evalWord S3Gen (S2Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_3_0 :
    S2Gen 3 * S2Rep 0 =
      S2Rep (S2Act 3 0) * evalWord S3Gen (S2Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_3_1 :
    S2Gen 3 * S2Rep 1 =
      S2Rep (S2Act 3 1) * evalWord S3Gen (S2Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_4_0 :
    S2Gen 4 * S2Rep 0 =
      S2Rep (S2Act 4 0) * evalWord S3Gen (S2Factor 4 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_4_1 :
    S2Gen 4 * S2Rep 1 =
      S2Rep (S2Act 4 1) * evalWord S3Gen (S2Factor 4 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_5_0 :
    S2Gen 5 * S2Rep 0 =
      S2Rep (S2Act 5 0) * evalWord S3Gen (S2Factor 5 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_5_1 :
    S2Gen 5 * S2Rep 1 =
      S2Rep (S2Act 5 1) * evalWord S3Gen (S2Factor 5 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_6_0 :
    S2Gen 6 * S2Rep 0 =
      S2Rep (S2Act 6 0) * evalWord S3Gen (S2Factor 6 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_6_1 :
    S2Gen 6 * S2Rep 1 =
      S2Rep (S2Act 6 1) * evalWord S3Gen (S2Factor 6 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_7_0 :
    S2Gen 7 * S2Rep 0 =
      S2Rep (S2Act 7 0) * evalWord S3Gen (S2Factor 7 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S2Step_7_1 :
    S2Gen 7 * S2Rep 1 =
      S2Rep (S2Act 7 1) * evalWord S3Gen (S2Factor 7 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem S2Step (i : Fin 8) (r : Fin 2) :
    S2Gen i * S2Rep r =
      S2Rep (S2Act i r) * evalWord S3Gen (S2Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact S2Step_0_0
  · exact S2Step_0_1
  · exact S2Step_1_0
  · exact S2Step_1_1
  · exact S2Step_2_0
  · exact S2Step_2_1
  · exact S2Step_3_0
  · exact S2Step_3_1
  · exact S2Step_4_0
  · exact S2Step_4_1
  · exact S2Step_5_0
  · exact S2Step_5_1
  · exact S2Step_6_0
  · exact S2Step_6_1
  · exact S2Step_7_0
  · exact S2Step_7_1

public theorem S2H_card : Nat.card S2H = 2 * Nat.card S3H :=
  wordSubgroup_card_eq_mul_next S2Gen S2Inv S2Inv_spec
    S3Gen S3Inv S3Inv_spec S2Rep S2Act S2Factor
    175 S2Point 0 S2Rep_mem S3H_le S2Rep_base
    S2Rep_point S2Point_injective S3H_fix S2Step

public theorem S2H_decompose (g : S2H) :
    ∃ r, ∃ k : S3H, (g : Equiv.Perm (Fin 6156)) = S2Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : S3H, evalWord S2Gen w = S2Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, S2Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨S2Act i r, ⟨evalWord S3Gen (S2Factor i r) * k,
      S3H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change S2Gen i * evalWord S2Gen w = _
    rw [hk, ← mul_assoc, S2Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
