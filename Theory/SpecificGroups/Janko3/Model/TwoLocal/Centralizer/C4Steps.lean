module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C5

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 4 of the C chain

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

@[expose] public def C4RepWord : Fin 2 → List (Fin 4)
  | 0 => []
  | 1 => [1]

@[expose] public def C4Rep (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  evalWord C4Gen (C4RepWord i)

@[expose] public def C4Point : Fin 2 → Fin 6156
  | 0 => 29
  | 1 => 715

@[expose] public def C4Act : Fin 4 → Fin 2 → Fin 2
  | 0, 0 => 0
  | 0, 1 => 1
  | 1, 0 => 1
  | 1, 1 => 0
  | 2, 0 => 0
  | 2, 1 => 1
  | 3, 0 => 1
  | 3, 1 => 0

@[expose] public def C4Factor : Fin 4 → Fin 2 → List (Fin 2)
  | 0, 0 => [0]
  | 0, 1 => [0]
  | 1, 0 => []
  | 1, 1 => []
  | 2, 0 => [0]
  | 2, 1 => [0]
  | 3, 0 => []
  | 3, 1 => []

public theorem C4Rep_mem (r : Fin 2) : C4Rep r ∈ C4H := ⟨_, rfl⟩
public theorem C4Rep_base : C4Rep 0 = 1 := rfl
public theorem C4Rep_point : ∀ r, C4Rep r 29 = C4Point r := by decide +kernel
public theorem C4Point_injective : Function.Injective C4Point := by decide +kernel
public theorem C5H_fix : ∀ h : C5H, (h : Equiv.Perm (Fin 6156)) 29 = 29 :=
  wordSubgroup_fix_of_gen_fix C5Gen C5Inv C5Inv_spec (by decide +kernel)

private theorem C4Step_0_0 :
    C4Gen 0 * C4Rep 0 =
      C4Rep (C4Act 0 0) * evalWord C5Gen (C4Factor 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C4Step_0_1 :
    C4Gen 0 * C4Rep 1 =
      C4Rep (C4Act 0 1) * evalWord C5Gen (C4Factor 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C4Step_1_0 :
    C4Gen 1 * C4Rep 0 =
      C4Rep (C4Act 1 0) * evalWord C5Gen (C4Factor 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C4Step_1_1 :
    C4Gen 1 * C4Rep 1 =
      C4Rep (C4Act 1 1) * evalWord C5Gen (C4Factor 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C4Step_2_0 :
    C4Gen 2 * C4Rep 0 =
      C4Rep (C4Act 2 0) * evalWord C5Gen (C4Factor 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C4Step_2_1 :
    C4Gen 2 * C4Rep 1 =
      C4Rep (C4Act 2 1) * evalWord C5Gen (C4Factor 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C4Step_3_0 :
    C4Gen 3 * C4Rep 0 =
      C4Rep (C4Act 3 0) * evalWord C5Gen (C4Factor 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem C4Step_3_1 :
    C4Gen 3 * C4Rep 1 =
      C4Rep (C4Act 3 1) * evalWord C5Gen (C4Factor 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem C4Step (i : Fin 4) (r : Fin 2) :
    C4Gen i * C4Rep r =
      C4Rep (C4Act i r) * evalWord C5Gen (C4Factor i r) := by
  fin_cases i <;> fin_cases r
  · exact C4Step_0_0
  · exact C4Step_0_1
  · exact C4Step_1_0
  · exact C4Step_1_1
  · exact C4Step_2_0
  · exact C4Step_2_1
  · exact C4Step_3_0
  · exact C4Step_3_1

public theorem C4H_card : Nat.card C4H = 2 * Nat.card C5H :=
  wordSubgroup_card_eq_mul_next C4Gen C4Inv C4Inv_spec
    C5Gen C5Inv C5Inv_spec C4Rep C4Act C4Factor
    29 C4Point 0 C4Rep_mem C5H_le C4Rep_base
    C4Rep_point C4Point_injective C5H_fix C4Step

public theorem C4H_decompose (g : C4H) :
    ∃ r, ∃ k : C5H, (g : Equiv.Perm (Fin 6156)) = C4Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : C5H, evalWord C4Gen w = C4Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, C4Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨C4Act i r, ⟨evalWord C5Gen (C4Factor i r) * k,
      C5H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change C4Gen i * evalWord C4Gen w = _
    rw [hk, ← mul_assoc, C4Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
