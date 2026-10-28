module
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.Divisibility.Basic
/-!
# Reconstructing packed fields from block comparisons

A packed table can be compared with a blocked source by checking each complete
block once. Truncation does not change any field lying within that block.
The Fi24 generator comparison applies this to the source-certified blocks of
256 fields, replacing a separate large-table reduction at every point.
-/
public section
namespace Theory.GroupAction.PackedPermutation
theorem field_mod (x w n i : Nat) (hi : i < n) :
    ((x % 2^(w*n)) >>> (w*i)) % 2^w = (x >>> (w*i)) % 2^w := by
  have hw : w*i + w*(n-i) = w*n := by
    rw [← Nat.mul_add, Nat.add_sub_of_le (Nat.le_of_lt hi)]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, ← hw,
    pow_add, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact pow_dvd_pow 2 (Nat.le_mul_of_pos_right w (Nat.sub_pos_of_lt hi))

theorem field_eq_of_chunks (x w n : Nat) (blocks : Nat → Nat)
    (hc : ∀ b < (n+255)/256,
      (x >>> (w*(256*b))) % 2^(w*256) = blocks b)
    {i : Nat} (hi : i<n) :
    (x >>> (w*i)) % 2^w = (blocks (i/256) >>> (w*(i%256))) % 2^w := by
  have hb : i/256 < (n+255)/256 := by omega
  rw [← hc (i/256) hb, field_mod _ w 256 (i%256) (Nat.mod_lt _ (by decide))]
  rw [← Nat.shiftRight_add, ← Nat.mul_add, Nat.div_add_mod]
end Theory.GroupAction.PackedPermutation
