module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C3

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 2 of the C chain

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

@[expose] public def C2RepWord : Fin 2 → List (Fin 4)
  | 0 => []
  | 1 => [0]

@[expose] public def C2Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord C2Gen (C2RepWord i)

@[expose] public def C2Point : Fin 2 → Fin 6156
  | 0 => 3589
  | 1 => 4629

@[expose] public def C2Act : Fin 4 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 2, 0 => 1
  | 2, 1 => 0
  | 3, 0 => 1
  | 3, 1 => 0

@[expose] public def C2Factor : Fin 4 → Fin 2 → List (Fin 4)
  | 0, 0 => []
  | 0, 1 => [0]
  | 1, 0 => [3]
  | 1, 1 => [1]
  | 2, 0 => [2]
  | 2, 1 => []
  | 3, 0 => [3]
  | 3, 1 => [1]

public theorem C2Rep_mem (r : Fin 2) : C2Rep r ∈ C2H := ⟨_, rfl⟩
public theorem C2Rep_base : C2Rep 0 = 1 := rfl
public theorem C2Rep_point : ∀ r, C2Rep r 3589 = C2Point r := by decide +kernel
public theorem C2Point_injective : Function.Injective C2Point := by decide +kernel
public theorem C3H_fix : ∀ h : C3H, (h : Equiv.Perm (Fin 6156)) 3589 = 3589 :=
  wordSubgroup_fix_of_gen_fix C3Gen C3Inv C3Inv_spec (by decide +kernel)

private theorem C2Step_0_0 :
    C2Gen 0 * C2Rep 0 =
      C2Rep (C2Act 0 0) * evalWord C3Gen (C2Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C2Step_0_1 :
    C2Gen 0 * C2Rep 1 =
      C2Rep (C2Act 0 1) * evalWord C3Gen (C2Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C2Step_1_0 :
    C2Gen 1 * C2Rep 0 =
      C2Rep (C2Act 1 0) * evalWord C3Gen (C2Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C2Step_1_1 :
    C2Gen 1 * C2Rep 1 =
      C2Rep (C2Act 1 1) * evalWord C3Gen (C2Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C2Step_2_0 :
    C2Gen 2 * C2Rep 0 =
      C2Rep (C2Act 2 0) * evalWord C3Gen (C2Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C2Step_2_1 :
    C2Gen 2 * C2Rep 1 =
      C2Rep (C2Act 2 1) * evalWord C3Gen (C2Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C2Step_3_0 :
    C2Gen 3 * C2Rep 0 =
      C2Rep (C2Act 3 0) * evalWord C3Gen (C2Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C2Step_3_1 :
    C2Gen 3 * C2Rep 1 =
      C2Rep (C2Act 3 1) * evalWord C3Gen (C2Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem C2Step (i : Fin 4) (r : Fin 2) :
    C2Gen i * C2Rep r =
      C2Rep (C2Act i r) * evalWord C3Gen (C2Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact C2Step_0_0
  · exact C2Step_0_1
  · exact C2Step_1_0
  · exact C2Step_1_1
  · exact C2Step_2_0
  · exact C2Step_2_1
  · exact C2Step_3_0
  · exact C2Step_3_1

public theorem C2H_card : Nat.card C2H = 2 * Nat.card C3H :=
  wordSubgroup_card_eq_mul_next C2Gen C2Inv C2Inv_spec
    C3Gen C3Inv C3Inv_spec C2Rep C2Act C2Factor
    3589 C2Point 0 C2Rep_mem C3H_le C2Rep_base
    C2Rep_point C2Point_injective C3H_fix C2Step

public theorem C2H_decompose (g : C2H) :
    ∃ r, ∃ k : C3H, (g : Equiv.Perm (Fin 6156)) = C2Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : C3H, evalWord C2Gen w = C2Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, C2Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨C2Act i r, ⟨evalWord C3Gen (C2Factor i r) * k,
      C3H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change C2Gen i * evalWord C2Gen w = _
    rw [hk, ← mul_assoc, C2Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
