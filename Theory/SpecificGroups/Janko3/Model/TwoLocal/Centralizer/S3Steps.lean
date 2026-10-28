module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S4

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 3 of the S chain

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

@[expose] public def S3RepWord : Fin 2 → List (Fin 6)
  | 0 => []
  | 1 => [0]

@[expose] public def S3Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord S3Gen (S3RepWord i)

@[expose] public def S3Point : Fin 2 → Fin 6156
  | 0 => 754
  | 1 => 4721

@[expose] public def S3Act : Fin 6 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 2, 0 => 0
  | 2, 1 => 1
  | 3, 0 => 1
  | 3, 1 => 0
  | 4, 0 => 1
  | 4, 1 => 0
  | 5, 0 => 0
  | 5, 1 => 1

@[expose] public def S3Factor : Fin 6 → Fin 2 → List (Fin 4)
  | 0, 0 => []
  | 0, 1 => []
  | 1, 0 => [1]
  | 1, 1 => [1]
  | 2, 0 => [0]
  | 2, 1 => [0]
  | 3, 0 => []
  | 3, 1 => []
  | 4, 0 => [1]
  | 4, 1 => [1]
  | 5, 0 => [0]
  | 5, 1 => [0]

public theorem S3Rep_mem (r : Fin 2) : S3Rep r ∈ S3H := ⟨_, rfl⟩
public theorem S3Rep_base : S3Rep 0 = 1 := rfl
public theorem S3Rep_point : ∀ r, S3Rep r 754 = S3Point r := by decide +kernel
public theorem S3Point_injective : Function.Injective S3Point := by decide +kernel
public theorem S4H_fix : ∀ h : S4H, (h : Equiv.Perm (Fin 6156)) 754 = 754 :=
  wordSubgroup_fix_of_gen_fix S4Gen S4Inv S4Inv_spec (by decide +kernel)

private theorem S3Step_0_0 :
    S3Gen 0 * S3Rep 0 =
      S3Rep (S3Act 0 0) * evalWord S4Gen (S3Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_0_1 :
    S3Gen 0 * S3Rep 1 =
      S3Rep (S3Act 0 1) * evalWord S4Gen (S3Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_1_0 :
    S3Gen 1 * S3Rep 0 =
      S3Rep (S3Act 1 0) * evalWord S4Gen (S3Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_1_1 :
    S3Gen 1 * S3Rep 1 =
      S3Rep (S3Act 1 1) * evalWord S4Gen (S3Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_2_0 :
    S3Gen 2 * S3Rep 0 =
      S3Rep (S3Act 2 0) * evalWord S4Gen (S3Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_2_1 :
    S3Gen 2 * S3Rep 1 =
      S3Rep (S3Act 2 1) * evalWord S4Gen (S3Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_3_0 :
    S3Gen 3 * S3Rep 0 =
      S3Rep (S3Act 3 0) * evalWord S4Gen (S3Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_3_1 :
    S3Gen 3 * S3Rep 1 =
      S3Rep (S3Act 3 1) * evalWord S4Gen (S3Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_4_0 :
    S3Gen 4 * S3Rep 0 =
      S3Rep (S3Act 4 0) * evalWord S4Gen (S3Factor 4 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_4_1 :
    S3Gen 4 * S3Rep 1 =
      S3Rep (S3Act 4 1) * evalWord S4Gen (S3Factor 4 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_5_0 :
    S3Gen 5 * S3Rep 0 =
      S3Rep (S3Act 5 0) * evalWord S4Gen (S3Factor 5 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S3Step_5_1 :
    S3Gen 5 * S3Rep 1 =
      S3Rep (S3Act 5 1) * evalWord S4Gen (S3Factor 5 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem S3Step (i : Fin 6) (r : Fin 2) :
    S3Gen i * S3Rep r =
      S3Rep (S3Act i r) * evalWord S4Gen (S3Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact S3Step_0_0
  · exact S3Step_0_1
  · exact S3Step_1_0
  · exact S3Step_1_1
  · exact S3Step_2_0
  · exact S3Step_2_1
  · exact S3Step_3_0
  · exact S3Step_3_1
  · exact S3Step_4_0
  · exact S3Step_4_1
  · exact S3Step_5_0
  · exact S3Step_5_1

public theorem S3H_card : Nat.card S3H = 2 * Nat.card S4H :=
  wordSubgroup_card_eq_mul_next S3Gen S3Inv S3Inv_spec
    S4Gen S4Inv S4Inv_spec S3Rep S3Act S3Factor
    754 S3Point 0 S3Rep_mem S4H_le S3Rep_base
    S3Rep_point S3Point_injective S4H_fix S3Step

public theorem S3H_decompose (g : S3H) :
    ∃ r, ∃ k : S4H, (g : Equiv.Perm (Fin 6156)) = S3Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : S4H, evalWord S3Gen w = S3Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, S3Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨S3Act i r, ⟨evalWord S4Gen (S3Factor i r) * k,
      S4H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change S3Gen i * evalWord S3Gen w = _
    rw [hk, ← mul_assoc, S3Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
