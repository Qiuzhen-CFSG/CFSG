module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.Arithmetic
/-!
# Row certificates with checked one-coordinate shortcuts

A one-coordinate input selects one stored row; every other input uses the
existing sequential XOR checker. Hints are checked, and their soundness is
proved against the literal binary matrix decoder. Thus sparse rows can bypass
an entire scan without trusting the certificate generator.

The consumer is the degree-1242 ATLAS involution certificate. Matrix sources
and row conventions are documented in `../../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
open Thompson.BinaryMatrix

theorem shiftRow_zero (bs : List Nat) : shiftRow 0 bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [shiftRow, ih]

theorem shiftRow_single (bs : List Nat) (k : Nat) : shiftRow (2^k) bs = bs[k]! := by
  induction bs generalizing k with
  | nil => simp [shiftRow]
  | cons b bs ih =>
    cases k with
    | zero => simp [shiftRow, shiftRow_zero]
    | succ k =>
      rw [shiftRow]
      have he : (2^(k+1)).testBit 0 = false := by simp
      simp only [he, Bool.false_eq_true, ↓reduceIte, Nat.zero_xor]
      rw [pow_succ, Nat.mul_div_left _ (by decide), ih]
      rfl

def check : List Nat → List Nat → List Nat → List (Option Nat) → Bool
  | [], _, [], [] => true
  | a::as, bs, c::cs, hint::hs =>
    (match hint with
      | some k => (a == 2^k) && (bs[k]! == c)
      | none => shiftRow a bs == c) && check as bs cs hs
  | _, _, _, _ => false

theorem check_sound (as bs cs : List Nat) (hs : List (Option Nat))
    (h : check as bs cs hs = true) : checkRows as bs cs = true := by
  induction as generalizing cs hs with
  | nil =>
    cases cs <;> cases hs <;> simp_all [check, checkRows]
  | cons a as ih =>
    cases cs with
    | nil => cases hs <;> simp [check] at h
    | cons c cs =>
      cases hs with
      | nil => simp [check] at h
      | cons hint hs =>
        simp only [check, Bool.and_eq_true] at h
        rw [checkRows, Bool.and_eq_true, beq_iff_eq]
        refine ⟨?_, ih cs hs h.2⟩
        cases hint with
        | none => exact of_decide_eq_true h.1
        | some k =>
          have hh : a = 2^k ∧ bs[k]! = c := by simpa using h.1
          rw [hh.1, shiftRow_single, hh.2]


/-- Concatenate independently checked row blocks. -/
theorem check_append (a₁ a₂ bs c₁ c₂ : List Nat) (h₁ h₂ : List (Option Nat))
    (p₁ : check a₁ bs c₁ h₁ = true) (p₂ : check a₂ bs c₂ h₂ = true) :
    check (a₁ ++ a₂) bs (c₁ ++ c₂) (h₁ ++ h₂) = true := by
  induction a₁ generalizing c₁ h₁ with
  | nil =>
    cases c₁ <;> cases h₁ <;> simp_all [check]
  | cons a as ih =>
    cases c₁ with
    | nil => cases h₁ <;> simp [check] at p₁
    | cons c cs =>
      cases h₁ with
      | nil => simp [check] at p₁
      | cons hint hs =>
        simp only [check, Bool.and_eq_true] at p₁
        simp only [List.cons_append, check, Bool.and_eq_true]
        exact ⟨p₁.1, ih cs hs p₁.2⟩

theorem product (n : Nat) (as bs cs : List Nat) (hs : List (Option Nat))
    (ha : as.length = n) (hb : bs.length = n) (h : check as bs cs hs = true) :
    decode n as.toArray * decode n bs.toArray = decode n cs.toArray :=
  product_sound_list n as bs cs ha hb (check_sound as bs cs hs h)
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
