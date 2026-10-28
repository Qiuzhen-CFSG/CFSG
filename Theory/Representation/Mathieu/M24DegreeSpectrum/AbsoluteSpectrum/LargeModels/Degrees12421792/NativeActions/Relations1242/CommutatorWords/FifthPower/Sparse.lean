module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.TablesV
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.TablesV2
/-!
# Skip certified zero row combinations

Every lookup table sends the zero coefficient to the zero row. This follows
from its complete existing table certificate. Skipping zero six-bit blocks
therefore preserves the original checker and avoids reading large packed
constants for the many sparse input rows. The actual consumers are the three
fixed fifth-power products; see `source/README.md`.
-/

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Sparse

def fast (a : Nat) : List Nat → Nat
  | [] => 0
  | t::ts => if a%64 = 0 then fast (a/64) ts
      else Arithmetic.lookup 1242 t (a%64) ^^^ fast (a/64) ts

def zeros (ts : List Nat) : Bool := ts.all fun t => Arithmetic.lookup 1242 t 0 == 0

theorem zeros_of_checked (bss : List (List Nat)) (ts : List Nat)
    (h : Arithmetic.tablesCheck 6 1242 bss ts = true) : zeros ts = true := by
  induction bss generalizing ts with
  | nil => cases ts <;> simp_all [zeros, Arithmetic.tablesCheck]
  | cons bs bss ih =>
    cases ts with
    | nil => simp [Arithmetic.tablesCheck] at h
    | cons t ts =>
      simp only [Arithmetic.tablesCheck, Bool.and_eq_true] at h
      have ht := h.1
      simp only [Arithmetic.tableCheck, Bool.and_eq_true] at ht
      have hz : Arithmetic.lookup 1242 t 0 = shiftRow 0 bs :=
        of_decide_eq_true (List.all_eq_true.mp ht.2 0 (List.mem_range.mpr (by decide)))
      rw [shiftRow_zero] at hz
      simp only [zeros, List.all_cons, Bool.and_eq_true, beq_iff_eq]
      exact ⟨hz, ih ts h.2⟩

theorem fast_eq (a : Nat) (ts : List Nat) (h : zeros ts = true) :
    fast a ts = Arithmetic.fast 6 1242 a ts := by
  induction ts generalizing a with
  | nil => rfl
  | cons t ts ih =>
    have hh : Arithmetic.lookup 1242 t 0 = 0 ∧ zeros ts = true := by
      simpa only [zeros, List.all_cons, Bool.and_eq_true, beq_iff_eq] using h
    rw [fast, Arithmetic.fast]
    change (if a%64 = 0 then fast (a/64) ts else
      Arithmetic.lookup 1242 t (a%64) ^^^ fast (a/64) ts) =
      Arithmetic.lookup 1242 t (a%64) ^^^ Arithmetic.fast 6 1242 (a/64) ts
    rw [ih _ hh.2]
    split_ifs with ha
    · rw [ha, hh.1, Nat.zero_xor]
    · rfl

def check (ts : List Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | a::as, c::cs => (fast a ts == c) && check ts as cs
  | _, _ => false

theorem check_sound (ts as cs : List Nat) (hz : zeros ts = true)
    (h : check ts as cs = true) : Arithmetic.check 6 1242 ts as cs = true := by
  induction as generalizing cs with
  | nil => cases cs <;> simp_all [check, Arithmetic.check]
  | cons a as ih =>
    cases cs with
    | nil => simp [check] at h
    | cons c cs =>
      simp only [check, Bool.and_eq_true] at h
      simp only [Arithmetic.check, Bool.and_eq_true]
      exact ⟨by simpa only [fast_eq _ _ hz] using h.1, ih cs h.2⟩

theorem v_zeros : zeros TablesV.tables = true := zeros_of_checked _ _ TablesV.checked
theorem v2_zeros : zeros TablesV2.tables = true := zeros_of_checked _ _ TablesV2.checked
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Sparse
