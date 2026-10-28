module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Q3

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 2 of the Q chain

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

@[expose] public def Q2RepWord : Fin 2 → List (Fin 2)
  | 0 => []
  | 1 => [0]

@[expose] public def Q2Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord Q2Gen (Q2RepWord i)

@[expose] public def Q2Point : Fin 2 → Fin 6156
  | 0 => 439
  | 1 => 5175

@[expose] public def Q2Act : Fin 2 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 1
  | 1, 1 => 0

@[expose] public def Q2Factor : Fin 2 → Fin 2 → List (Fin 2)
  | 0, 0 => []
  | 0, 1 => [0]
  | 1, 0 => [0]
  | 1, 1 => []

public theorem Q2Rep_mem (r : Fin 2) : Q2Rep r ∈ Q2H := ⟨_, rfl⟩
public theorem Q2Rep_base : Q2Rep 0 = 1 := rfl
public theorem Q2Rep_point : ∀ r, Q2Rep r 439 = Q2Point r := by decide +kernel
public theorem Q2Point_injective : Function.Injective Q2Point := by decide +kernel
public theorem Q3H_fix : ∀ h : Q3H, (h : Equiv.Perm (Fin 6156)) 439 = 439 :=
  wordSubgroup_fix_of_gen_fix Q3Gen Q3Inv Q3Inv_spec (by decide +kernel)

private theorem Q2Step_0_0 :
    Q2Gen 0 * Q2Rep 0 =
      Q2Rep (Q2Act 0 0) * evalWord Q3Gen (Q2Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q2Step_0_1 :
    Q2Gen 0 * Q2Rep 1 =
      Q2Rep (Q2Act 0 1) * evalWord Q3Gen (Q2Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q2Step_1_0 :
    Q2Gen 1 * Q2Rep 0 =
      Q2Rep (Q2Act 1 0) * evalWord Q3Gen (Q2Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q2Step_1_1 :
    Q2Gen 1 * Q2Rep 1 =
      Q2Rep (Q2Act 1 1) * evalWord Q3Gen (Q2Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem Q2Step (i : Fin 2) (r : Fin 2) :
    Q2Gen i * Q2Rep r =
      Q2Rep (Q2Act i r) * evalWord Q3Gen (Q2Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact Q2Step_0_0
  · exact Q2Step_0_1
  · exact Q2Step_1_0
  · exact Q2Step_1_1

public theorem Q2H_card : Nat.card Q2H = 2 * Nat.card Q3H :=
  wordSubgroup_card_eq_mul_next Q2Gen Q2Inv Q2Inv_spec
    Q3Gen Q3Inv Q3Inv_spec Q2Rep Q2Act Q2Factor
    439 Q2Point 0 Q2Rep_mem Q3H_le Q2Rep_base
    Q2Rep_point Q2Point_injective Q3H_fix Q2Step

public theorem Q2H_decompose (g : Q2H) :
    ∃ r, ∃ k : Q3H, (g : Equiv.Perm (Fin 6156)) = Q2Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : Q3H, evalWord Q2Gen w = Q2Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, Q2Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨Q2Act i r, ⟨evalWord Q3Gen (Q2Factor i r) * k,
      Q3H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change Q2Gen i * evalWord Q2Gen w = _
    rw [hk, ← mul_assoc, Q2Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
