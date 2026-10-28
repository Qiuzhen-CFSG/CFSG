module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Contracts

/-!
# Sound finite checks for the literal J₂ walks

Extraction from a whole packed natural agrees with the original 128-entry
blocks. Boolean interval checks imply every constituent equality, and adjacent
intervals combine without re-evaluating previously checked entries.

Source conventions: Coordinates/source/README.md. These general arithmetic
lemmas support the literal fixed-table certificate only.
-/

@[expose] public section

namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Orbits

def entry (width packed n : ℕ) : ℕ := (packed >>> (width*n)) % 2^width

lemma shift_mod (v a b c : ℕ) (h : a + b ≤ c) :
    ((v % 2^c) >>> a) % 2^b = (v >>> a) % 2^b := by
  simp only [Nat.shiftRight_eq_div_pow]
  have hc : c = a + (c-a) := by omega
  rw [hc, Nat.pow_add, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

lemma entry_block (width packed n : ℕ) :
    entry width (entry (width*128) packed (n/128)) (n%128) = entry width packed n := by
  unfold entry
  rw [shift_mod]
  · rw [← Nat.shiftRight_add]
    congr 2
    calc
      width * 128 * (n / 128) + width * (n % 128) =
          width * (128 * (n / 128) + n % 128) := by ring
      _ = width * n := by rw [Nat.div_add_mod]
  · have h : n % 128 + 1 ≤ 128 := by omega
    simpa only [Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left width h

lemma entry_eq_lookup (width packed n : ℕ) (a : Array ℕ)
    (h : entry (width*128) packed (n/128) = a[n/128]!) :
    entry width packed n = lookup width a n := by
  rw [← entry_block width packed n, h]
  rfl

def checkRange (f : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => checkRange f start n && f (start+n)

lemma checkRange_sound {f : ℕ → Bool} {start n : ℕ}
    (h : checkRange f start n = true) {j : ℕ} (h0 : start ≤ j) (h1 : j < start+n) :
    f j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨hn, hl⟩ := Bool.and_eq_true_iff.mp h
    by_cases hj : j < start+n
    · exact ih hn hj
    · have : j = start+n := by omega
      simpa only [this] using hl

lemma checkRange_complete {f : ℕ → Bool} {start n : ℕ}
    (h : ∀ j, start ≤ j → j < start+n → f j = true) :
    checkRange f start n = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Bool.and_eq_true_iff.mpr
    exact ⟨ih (fun j h0 h1 => h j h0 (by omega)), h (start+n) (by omega) (by omega)⟩

lemma checkRange_append {f : ℕ → Bool} {start n m : ℕ}
    (hn : checkRange f start n = true) (hm : checkRange f (start+n) m = true) :
    checkRange f start (n+m) = true := by
  apply checkRange_complete
  intro j h0 h1
  by_cases hj : j < start+n
  · exact checkRange_sound hn h0 hj
  · exact checkRange_sound hm (by omega) (by omega)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Orbits
