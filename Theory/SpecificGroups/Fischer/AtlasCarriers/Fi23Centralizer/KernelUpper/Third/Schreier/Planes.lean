module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Schreier.PlaneData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Separating the Fi23 letters by fifteen checked bitplanes

The bitplanes store the binary digits of each letter. Equality on these fifteen
tests therefore detects equality of letters. This converts whole-bitvector word
certificates into the exact pointwise identities in `Third.Reduction`.

Source application: ATLAS F23G1-p31671B0; GLS3 Table 5.3u.
-/

set_option Elab.async false

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.Schreier
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

private def planeTest (b : Fin 15) (i : Nat) : Bool :=
  decide ((plane b).testBit (i % 31671) = (i % 31671).testBit b.val)

private theorem plane_checked_0 :
    checkPow (planeTest 0) 0 15 = true := by decide +kernel

private theorem plane_checked_1 :
    checkPow (planeTest 1) 0 15 = true := by decide +kernel

private theorem plane_checked_2 :
    checkPow (planeTest 2) 0 15 = true := by decide +kernel

private theorem plane_checked_3 :
    checkPow (planeTest 3) 0 15 = true := by decide +kernel

private theorem plane_checked_4 :
    checkPow (planeTest 4) 0 15 = true := by decide +kernel

private theorem plane_checked_5 :
    checkPow (planeTest 5) 0 15 = true := by decide +kernel

private theorem plane_checked_6 :
    checkPow (planeTest 6) 0 15 = true := by decide +kernel

private theorem plane_checked_7 :
    checkPow (planeTest 7) 0 15 = true := by decide +kernel

private theorem plane_checked_8 :
    checkPow (planeTest 8) 0 15 = true := by decide +kernel

private theorem plane_checked_9 :
    checkPow (planeTest 9) 0 15 = true := by decide +kernel

private theorem plane_checked_10 :
    checkPow (planeTest 10) 0 15 = true := by decide +kernel

private theorem plane_checked_11 :
    checkPow (planeTest 11) 0 15 = true := by decide +kernel

private theorem plane_checked_12 :
    checkPow (planeTest 12) 0 15 = true := by decide +kernel

private theorem plane_checked_13 :
    checkPow (planeTest 13) 0 15 = true := by decide +kernel

private theorem plane_checked_14 :
    checkPow (planeTest 14) 0 15 = true := by decide +kernel

private theorem plane_checked (b : Fin 15) :
    checkPow (planeTest b) 0 15 = true := by
  fin_cases b
  · exact plane_checked_0
  · exact plane_checked_1
  · exact plane_checked_2
  · exact plane_checked_3
  · exact plane_checked_4
  · exact plane_checked_5
  · exact plane_checked_6
  · exact plane_checked_7
  · exact plane_checked_8
  · exact plane_checked_9
  · exact plane_checked_10
  · exact plane_checked_11
  · exact plane_checked_12
  · exact plane_checked_13
  · exact plane_checked_14

theorem plane_testBit (b : Fin 15) (x : Fin 31671) :
    (plane b).testBit x.val = x.val.testBit b.val := by
  have h := checkPow_sound (planeTest b) 15 0 (plane_checked b) x.val
    (Nat.zero_le _) (Nat.lt_trans x.isLt (by decide))
  simpa only [planeTest, Nat.mod_eq_of_lt x.isLt, decide_eq_true_eq] using h

theorem plane_ext {x y : Fin 31671}
    (h : ∀ b : Fin 15, (plane b).testBit x.val = (plane b).testBit y.val) : x = y := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 15
  · simpa only [plane_testBit] using h ⟨b, hb⟩
  · have hpow : 2 ^ 15 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
    have hx : x.val < 2 ^ b := lt_of_lt_of_le (Nat.lt_trans x.isLt (by decide)) hpow
    have hy : y.val < 2 ^ b := lt_of_lt_of_le (Nat.lt_trans y.isLt (by decide)) hpow
    rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.Schreier
