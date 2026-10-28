module
public import Theory.GroupAction.PackedPermutation.Soundness
public import Theory.GroupAction.PackedPermutation.Periodic
import Mathlib.Tactic
/-!
# Bulk validation of packed switch masks

Three natural-number identities suffice. The adjacent-bit XOR vanishes on the
interior of every field, so each field is either all zero or all one. The mask
has zero intersection with its distance-shift, so selected pairs are disjoint.
Its high shift vanishes before the final possible lower endpoint, so no pair
crosses the table bound. These checks establish all hypotheses of the actual
finite-permutation soundness theorem, including padding; no generated routing
or selected-wire invariant is assumed.

The Fi24 centralizer certificates use width 19 and a padded table of size
2^19. This generic proof keeps their large checks as bulk bitwise operations.
-/
@[expose] public section
namespace Theory.GroupAction.PackedPermutation

def interiorMask (w n : ℕ) : ℕ := repeatField w n (2^(w-1)-1)

theorem interiorMask_bit {w n i j : ℕ} (hw : 0<w) (hi : i<n) (hj : j<w-1) :
    (interiorMask w n).testBit (w*i+j) = true := by
  have hc : 2^(w-1)-1<2^w :=
    (Nat.sub_lt (Nat.two_pow_pos _) (by decide)).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le w 1))
  have hh := congrArg (fun v => v.testBit j) (repeatField_get w n (2^(w-1)-1) i hw hc)
  have hjw : j<w := by omega
  simpa [interiorMask, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hi, hj, hjw] using hh

theorem bit_false_of_shift_zero (mask w t i j : ℕ) (h : mask >>> (w*t)=0) (hi : t ≤ i) :
    mask.testBit (w*i+j)=false := by
  have hpos : w*t ≤ w*i+j := (Nat.mul_le_mul_left w hi).trans (Nat.le_add_right _ _)
  have heq : w*t+(w*i+j-w*t)=w*i+j := Nat.add_sub_of_le hpos
  have hh := congrArg (fun v => v.testBit (w*i+j-w*t)) h
  simpa only [Nat.testBit_shiftRight, heq, Nat.zero_testBit] using hh

/-- Three bulk identities certify complete mask validity, without enumerating fields. -/
theorem Stage.valid_of_checks (s : Stage) (w n : ℕ) (hw : 0<w)
    (hu : ((s.mask ^^^ (s.mask >>> 1)) &&& interiorMask w n)=0)
    (hd : (s.mask &&& (s.mask >>> (w*s.distance)))=0)
    (hb : s.mask >>> (w*(n-s.distance))=0) : s.Valid w n := by
  refine ⟨?_,?_,?_⟩
  · intro i j hj
    by_cases hi : i<n
    · induction j with
      | zero => simp [Stage.selected]
      | succ j ih =>
        have hjw : j<w := by omega
        have hjm : j<w-1 := by omega
        have hbit := congrArg (fun v => v.testBit (w*i+j)) hu
        rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight,
          interiorMask_bit hw hi hjm, Bool.and_true, Nat.zero_testBit] at hbit
        have heq : s.mask.testBit (w*i+(j+1))=s.mask.testBit (w*i+j) := by
          have har : 1+(w*i+j)=w*i+(j+1) := by omega
          rw [har] at hbit
          cases h0 : s.mask.testBit (w*i+j) <;>
            cases h1 : s.mask.testBit (w*i+(j+1)) <;> simp_all
        exact heq.trans (ih hjw)
    · have hip : n-s.distance ≤ i := by omega
      rw [bit_false_of_shift_zero _ _ _ _ _ hb hip]
      exact (bit_false_of_shift_zero _ _ _ i 0 hb hip).symm
  · intro i hi
    have hh := congrArg (fun v => v.testBit (w*i)) hd
    have heq : w*s.distance+w*i=w*(i+s.distance) := by ring
    change s.mask.testBit (w*i)=true at hi
    change s.mask.testBit (w*(i+s.distance))=false
    simpa only [Nat.testBit_and, Nat.testBit_shiftRight, heq, Nat.zero_testBit,
      hi, Bool.true_and] using hh
  · intro i hi
    by_contra hn
    have hip : n-s.distance ≤ i := by omega
    have hh := bit_false_of_shift_zero _ _ _ i 0 hb hip
    change s.mask.testBit (w*i)=true at hi
    exact Bool.noConfusion (hi.symm.trans hh)
end Theory.GroupAction.PackedPermutation
