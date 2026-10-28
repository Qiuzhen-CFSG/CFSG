module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Q4

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 3 of the Q chain

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

@[expose] public def Q3RepWord : Fin 2 → List (Fin 2)
  | 0 => []
  | 1 => [0]

@[expose] public def Q3Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord Q3Gen (Q3RepWord i)

@[expose] public def Q3Point : Fin 2 → Fin 6156
  | 0 => 0
  | 1 => 2786

@[expose] public def Q3Act : Fin 2 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 1
  | 1, 1 => 0

@[expose] public def Q3Factor : Fin 2 → Fin 2 → List (Fin 0)
  | 0, 0 => []
  | 0, 1 => []
  | 1, 0 => []
  | 1, 1 => []

public theorem Q3Rep_mem (r : Fin 2) : Q3Rep r ∈ Q3H := ⟨_, rfl⟩
public theorem Q3Rep_base : Q3Rep 0 = 1 := rfl
public theorem Q3Rep_point : ∀ r, Q3Rep r 0 = Q3Point r := by decide +kernel
public theorem Q3Point_injective : Function.Injective Q3Point := by decide +kernel
public theorem Q4H_fix : ∀ h : Q4H, (h : Equiv.Perm (Fin 6156)) 0 = 0 :=
  wordSubgroup_fix_of_gen_fix Q4Gen Q4Inv Q4Inv_spec (by decide +kernel)

private theorem Q3Step_0_0 :
    Q3Gen 0 * Q3Rep 0 =
      Q3Rep (Q3Act 0 0) * evalWord Q4Gen (Q3Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q3Step_0_1 :
    Q3Gen 0 * Q3Rep 1 =
      Q3Rep (Q3Act 0 1) * evalWord Q4Gen (Q3Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q3Step_1_0 :
    Q3Gen 1 * Q3Rep 0 =
      Q3Rep (Q3Act 1 0) * evalWord Q4Gen (Q3Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem Q3Step_1_1 :
    Q3Gen 1 * Q3Rep 1 =
      Q3Rep (Q3Act 1 1) * evalWord Q4Gen (Q3Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem Q3Step (i : Fin 2) (r : Fin 2) :
    Q3Gen i * Q3Rep r =
      Q3Rep (Q3Act i r) * evalWord Q4Gen (Q3Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact Q3Step_0_0
  · exact Q3Step_0_1
  · exact Q3Step_1_0
  · exact Q3Step_1_1

public theorem Q3H_card : Nat.card Q3H = 2 * Nat.card Q4H :=
  wordSubgroup_card_eq_mul_next Q3Gen Q3Inv Q3Inv_spec
    Q4Gen Q4Inv Q4Inv_spec Q3Rep Q3Act Q3Factor
    0 Q3Point 0 Q3Rep_mem Q4H_le Q3Rep_base
    Q3Rep_point Q3Point_injective Q4H_fix Q3Step

public theorem Q3H_decompose (g : Q3H) :
    ∃ r, ∃ k : Q4H, (g : Equiv.Perm (Fin 6156)) = Q3Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : Q4H, evalWord Q3Gen w = Q3Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, Q3Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨Q3Act i r, ⟨evalWord Q4Gen (Q3Factor i r) * k,
      Q4H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change Q3Gen i * evalWord Q3Gen w = _
    rw [hk, ← mul_assoc, Q3Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
