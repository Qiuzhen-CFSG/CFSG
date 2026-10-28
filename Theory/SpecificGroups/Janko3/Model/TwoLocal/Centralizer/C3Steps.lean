module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C4

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 3 of the C chain

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

@[expose] public def C3RepWord : Fin 3 → List (Fin 4)
  | 0 => []
  | 1 => [0]
  | 2 => [1]

@[expose] public def C3Rep (i : Fin 3) : Equiv.Perm (Fin 6156) :=
  evalWord C3Gen (C3RepWord i)

@[expose] public def C3Point : Fin 3 → Fin 6156
  | 0 => 2861
  | 1 => 5122
  | 2 => 3556

@[expose] public def C3Act : Fin 4 → Fin 3 → Fin 3
  | 0, 0 => 1
  | 0, 1 => 2
  | 0, 2 => 0
  | 1, 0 => 2
  | 1, 1 => 0
  | 1, 2 => 1
  | 2, 0 => 2
  | 2, 1 => 0
  | 2, 2 => 1
  | 3, 0 => 1
  | 3, 1 => 2
  | 3, 2 => 0

@[expose] public def C3Factor : Fin 4 → Fin 3 → List (Fin 4)
  | 0, 0 => []
  | 0, 1 => [1]
  | 0, 2 => [1]
  | 1, 0 => []
  | 1, 1 => [0]
  | 1, 2 => [0]
  | 2, 0 => [1]
  | 2, 1 => []
  | 2, 2 => [1]
  | 3, 0 => [0]
  | 3, 1 => [0]
  | 3, 2 => []

public theorem C3Rep_mem (r : Fin 3) : C3Rep r ∈ C3H := ⟨_, rfl⟩
public theorem C3Rep_base : C3Rep 0 = 1 := rfl
public theorem C3Rep_point : ∀ r, C3Rep r 2861 = C3Point r := by decide +kernel
public theorem C3Point_injective : Function.Injective C3Point := by decide +kernel
public theorem C4H_fix : ∀ h : C4H, (h : Equiv.Perm (Fin 6156)) 2861 = 2861 :=
  wordSubgroup_fix_of_gen_fix C4Gen C4Inv C4Inv_spec (by decide +kernel)

private theorem C3Step_0_0 :
    C3Gen 0 * C3Rep 0 =
      C3Rep (C3Act 0 0) * evalWord C4Gen (C3Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_0_1 :
    C3Gen 0 * C3Rep 1 =
      C3Rep (C3Act 0 1) * evalWord C4Gen (C3Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_0_2 :
    C3Gen 0 * C3Rep 2 =
      C3Rep (C3Act 0 2) * evalWord C4Gen (C3Factor 0 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_1_0 :
    C3Gen 1 * C3Rep 0 =
      C3Rep (C3Act 1 0) * evalWord C4Gen (C3Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_1_1 :
    C3Gen 1 * C3Rep 1 =
      C3Rep (C3Act 1 1) * evalWord C4Gen (C3Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_1_2 :
    C3Gen 1 * C3Rep 2 =
      C3Rep (C3Act 1 2) * evalWord C4Gen (C3Factor 1 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_2_0 :
    C3Gen 2 * C3Rep 0 =
      C3Rep (C3Act 2 0) * evalWord C4Gen (C3Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_2_1 :
    C3Gen 2 * C3Rep 1 =
      C3Rep (C3Act 2 1) * evalWord C4Gen (C3Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_2_2 :
    C3Gen 2 * C3Rep 2 =
      C3Rep (C3Act 2 2) * evalWord C4Gen (C3Factor 2 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_3_0 :
    C3Gen 3 * C3Rep 0 =
      C3Rep (C3Act 3 0) * evalWord C4Gen (C3Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_3_1 :
    C3Gen 3 * C3Rep 1 =
      C3Rep (C3Act 3 1) * evalWord C4Gen (C3Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C3Step_3_2 :
    C3Gen 3 * C3Rep 2 =
      C3Rep (C3Act 3 2) * evalWord C4Gen (C3Factor 3 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem C3Step (i : Fin 4) (r : Fin 3) :
    C3Gen i * C3Rep r =
      C3Rep (C3Act i r) * evalWord C4Gen (C3Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact C3Step_0_0
  · exact C3Step_0_1
  · exact C3Step_0_2
  · exact C3Step_1_0
  · exact C3Step_1_1
  · exact C3Step_1_2
  · exact C3Step_2_0
  · exact C3Step_2_1
  · exact C3Step_2_2
  · exact C3Step_3_0
  · exact C3Step_3_1
  · exact C3Step_3_2

public theorem C3H_card : Nat.card C3H = 3 * Nat.card C4H :=
  wordSubgroup_card_eq_mul_next C3Gen C3Inv C3Inv_spec
    C4Gen C4Inv C4Inv_spec C3Rep C3Act C3Factor
    2861 C3Point 0 C3Rep_mem C4H_le C3Rep_base
    C3Rep_point C3Point_injective C4H_fix C3Step

public theorem C3H_decompose (g : C3H) :
    ∃ r, ∃ k : C4H, (g : Equiv.Perm (Fin 6156)) = C3Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : C4H, evalWord C3Gen w = C3Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, C3Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨C3Act i r, ⟨evalWord C4Gen (C3Factor i r) * k,
      C4H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change C3Gen i * evalWord C3Gen w = _
    rw [hk, ← mul_assoc, C3Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
