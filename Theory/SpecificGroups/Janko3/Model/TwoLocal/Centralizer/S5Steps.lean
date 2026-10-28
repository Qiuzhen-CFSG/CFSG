module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S6

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 5 of the S chain

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

@[expose] public def S5RepWord : Fin 2 → List (Fin 2)
  | 0 => []
  | 1 => [0]

@[expose] public def S5Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord S5Gen (S5RepWord i)

@[expose] public def S5Point : Fin 2 → Fin 6156
  | 0 => 0
  | 1 => 5321

@[expose] public def S5Act : Fin 2 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 1
  | 1, 1 => 0

@[expose] public def S5Factor : Fin 2 → Fin 2 → List (Fin 0)
  | 0, 0 => []
  | 0, 1 => []
  | 1, 0 => []
  | 1, 1 => []

public theorem S5Rep_mem (r : Fin 2) : S5Rep r ∈ S5H := ⟨_, rfl⟩
public theorem S5Rep_base : S5Rep 0 = 1 := rfl
public theorem S5Rep_point : ∀ r, S5Rep r 0 = S5Point r := by decide +kernel
public theorem S5Point_injective : Function.Injective S5Point := by decide +kernel
public theorem S6H_fix : ∀ h : S6H, (h : Equiv.Perm (Fin 6156)) 0 = 0 :=
  wordSubgroup_fix_of_gen_fix S6Gen S6Inv S6Inv_spec (by decide +kernel)

private theorem S5Step_0_0 :
    S5Gen 0 * S5Rep 0 =
      S5Rep (S5Act 0 0) * evalWord S6Gen (S5Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S5Step_0_1 :
    S5Gen 0 * S5Rep 1 =
      S5Rep (S5Act 0 1) * evalWord S6Gen (S5Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S5Step_1_0 :
    S5Gen 1 * S5Rep 0 =
      S5Rep (S5Act 1 0) * evalWord S6Gen (S5Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S5Step_1_1 :
    S5Gen 1 * S5Rep 1 =
      S5Rep (S5Act 1 1) * evalWord S6Gen (S5Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem S5Step (i : Fin 2) (r : Fin 2) :
    S5Gen i * S5Rep r =
      S5Rep (S5Act i r) * evalWord S6Gen (S5Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact S5Step_0_0
  · exact S5Step_0_1
  · exact S5Step_1_0
  · exact S5Step_1_1

public theorem S5H_card : Nat.card S5H = 2 * Nat.card S6H :=
  wordSubgroup_card_eq_mul_next S5Gen S5Inv S5Inv_spec
    S6Gen S6Inv S6Inv_spec S5Rep S5Act S5Factor
    0 S5Point 0 S5Rep_mem S6H_le S5Rep_base
    S5Rep_point S5Point_injective S6H_fix S5Step

public theorem S5H_decompose (g : S5H) :
    ∃ r, ∃ k : S6H, (g : Equiv.Perm (Fin 6156)) = S5Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : S6H, evalWord S5Gen w = S5Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, S5Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨S5Act i r, ⟨evalWord S6Gen (S5Factor i r) * k,
      S6H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change S5Gen i * evalWord S5Gen w = _
    rw [hk, ← mul_assoc, S5Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
