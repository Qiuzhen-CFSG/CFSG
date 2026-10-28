module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S5

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 4 of the S chain

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

@[expose] public def S4RepWord : Fin 2 → List (Fin 4)
  | 0 => []
  | 1 => [0]

@[expose] public def S4Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord S4Gen (S4RepWord i)

@[expose] public def S4Point : Fin 2 → Fin 6156
  | 0 => 73
  | 1 => 4212

@[expose] public def S4Act : Fin 4 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 2, 0 => 1
  | 2, 1 => 0
  | 3, 0 => 1
  | 3, 1 => 0

@[expose] public def S4Factor : Fin 4 → Fin 2 → List (Fin 2)
  | 0, 0 => []
  | 0, 1 => []
  | 1, 0 => [0]
  | 1, 1 => [0]
  | 2, 0 => []
  | 2, 1 => []
  | 3, 0 => [0]
  | 3, 1 => [0]

public theorem S4Rep_mem (r : Fin 2) : S4Rep r ∈ S4H := ⟨_, rfl⟩
public theorem S4Rep_base : S4Rep 0 = 1 := rfl
public theorem S4Rep_point : ∀ r, S4Rep r 73 = S4Point r := by decide +kernel
public theorem S4Point_injective : Function.Injective S4Point := by decide +kernel
public theorem S5H_fix : ∀ h : S5H, (h : Equiv.Perm (Fin 6156)) 73 = 73 :=
  wordSubgroup_fix_of_gen_fix S5Gen S5Inv S5Inv_spec (by decide +kernel)

private theorem S4Step_0_0 :
    S4Gen 0 * S4Rep 0 =
      S4Rep (S4Act 0 0) * evalWord S5Gen (S4Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S4Step_0_1 :
    S4Gen 0 * S4Rep 1 =
      S4Rep (S4Act 0 1) * evalWord S5Gen (S4Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S4Step_1_0 :
    S4Gen 1 * S4Rep 0 =
      S4Rep (S4Act 1 0) * evalWord S5Gen (S4Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S4Step_1_1 :
    S4Gen 1 * S4Rep 1 =
      S4Rep (S4Act 1 1) * evalWord S5Gen (S4Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S4Step_2_0 :
    S4Gen 2 * S4Rep 0 =
      S4Rep (S4Act 2 0) * evalWord S5Gen (S4Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S4Step_2_1 :
    S4Gen 2 * S4Rep 1 =
      S4Rep (S4Act 2 1) * evalWord S5Gen (S4Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S4Step_3_0 :
    S4Gen 3 * S4Rep 0 =
      S4Rep (S4Act 3 0) * evalWord S5Gen (S4Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem S4Step_3_1 :
    S4Gen 3 * S4Rep 1 =
      S4Rep (S4Act 3 1) * evalWord S5Gen (S4Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem S4Step (i : Fin 4) (r : Fin 2) :
    S4Gen i * S4Rep r =
      S4Rep (S4Act i r) * evalWord S5Gen (S4Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact S4Step_0_0
  · exact S4Step_0_1
  · exact S4Step_1_0
  · exact S4Step_1_1
  · exact S4Step_2_0
  · exact S4Step_2_1
  · exact S4Step_3_0
  · exact S4Step_3_1

public theorem S4H_card : Nat.card S4H = 2 * Nat.card S5H :=
  wordSubgroup_card_eq_mul_next S4Gen S4Inv S4Inv_spec
    S5Gen S5Inv S5Inv_spec S4Rep S4Act S4Factor
    73 S4Point 0 S4Rep_mem S5H_le S4Rep_base
    S4Rep_point S4Point_injective S5H_fix S4Step

public theorem S4H_decompose (g : S4H) :
    ∃ r, ∃ k : S5H, (g : Equiv.Perm (Fin 6156)) = S4Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : S5H, evalWord S4Gen w = S4Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, S4Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨S4Act i r, ⟨evalWord S5Gen (S4Factor i r) * k,
      S5H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change S4Gen i * evalWord S4Gen w = _
    rw [hk, ← mul_assoc, S4Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
