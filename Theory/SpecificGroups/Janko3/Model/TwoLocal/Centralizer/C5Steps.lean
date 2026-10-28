module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C6

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 5 of the C chain

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

@[expose] public def C5RepWord : Fin 2 → List (Fin 2)
  | 0 => []
  | 1 => [0]

@[expose] public def C5Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord C5Gen (C5RepWord i)

@[expose] public def C5Point : Fin 2 → Fin 6156
  | 0 => 0
  | 1 => 188

@[expose] public def C5Act : Fin 2 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 1
  | 1, 1 => 0

@[expose] public def C5Factor : Fin 2 → Fin 2 → List (Fin 0)
  | 0, 0 => []
  | 0, 1 => []
  | 1, 0 => []
  | 1, 1 => []

public theorem C5Rep_mem (r : Fin 2) : C5Rep r ∈ C5H := ⟨_, rfl⟩
public theorem C5Rep_base : C5Rep 0 = 1 := rfl
public theorem C5Rep_point : ∀ r, C5Rep r 0 = C5Point r := by decide +kernel
public theorem C5Point_injective : Function.Injective C5Point := by decide +kernel
public theorem C6H_fix : ∀ h : C6H, (h : Equiv.Perm (Fin 6156)) 0 = 0 :=
  wordSubgroup_fix_of_gen_fix C6Gen C6Inv C6Inv_spec (by decide +kernel)

private theorem C5Step_0_0 :
    C5Gen 0 * C5Rep 0 =
      C5Rep (C5Act 0 0) * evalWord C6Gen (C5Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C5Step_0_1 :
    C5Gen 0 * C5Rep 1 =
      C5Rep (C5Act 0 1) * evalWord C6Gen (C5Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C5Step_1_0 :
    C5Gen 1 * C5Rep 0 =
      C5Rep (C5Act 1 0) * evalWord C6Gen (C5Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C5Step_1_1 :
    C5Gen 1 * C5Rep 1 =
      C5Rep (C5Act 1 1) * evalWord C6Gen (C5Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem C5Step (i : Fin 2) (r : Fin 2) :
    C5Gen i * C5Rep r =
      C5Rep (C5Act i r) * evalWord C6Gen (C5Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact C5Step_0_0
  · exact C5Step_0_1
  · exact C5Step_1_0
  · exact C5Step_1_1

public theorem C5H_card : Nat.card C5H = 2 * Nat.card C6H :=
  wordSubgroup_card_eq_mul_next C5Gen C5Inv C5Inv_spec
    C6Gen C6Inv C6Inv_spec C5Rep C5Act C5Factor
    0 C5Point 0 C5Rep_mem C6H_le C5Rep_base
    C5Rep_point C5Point_injective C6H_fix C5Step

public theorem C5H_decompose (g : C5H) :
    ∃ r, ∃ k : C6H, (g : Equiv.Perm (Fin 6156)) = C5Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : C6H, evalWord C5Gen w = C5Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, C5Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨C5Act i r, ⟨evalWord C6Gen (C5Factor i r) * k,
      C6H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change C5Gen i * evalWord C5Gen w = _
    rw [hk, ← mul_assoc, C5Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
