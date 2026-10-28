module
public import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# Sound packed-field switching layers

A table stores equal-width fields in a natural number, least significant field
first. A mask selects disjoint lower endpoints of pairs at a fixed distance.
The XOR/shift formula exchanges exactly those pairs. The proof checks each
bit, including the subtraction boundary; no arithmetic carry or finite-data
computation is assumed. The disjointness and endpoint bounds also construct
the actual finite wire permutation.

This elementary certificate interface is used by the literal Fi24 centralizer
section in Aschbacher--Smith A.2.19. Numerical masks must separately satisfy the
proved mask conditions before any packed computation is interpreted.
-/
@[expose] public section
namespace Theory.GroupAction.PackedPermutation

def get (w x i : ℕ) : ℕ := (x >>> (w*i)) % 2^w

def layer (w s mask x : ℕ) : ℕ :=
  let d := ((x >>> (w*s)) ^^^ x) &&& mask
  x ^^^ d ^^^ (d <<< (w*s))

def switchIndex (s : ℕ) (selected : ℕ → Bool) (i : ℕ) : ℕ :=
  if selected i then i+s else if s ≤ i ∧ selected (i-s) then i-s else i

theorem testBit_get (w x i j : ℕ) :
    (get w x i).testBit j = (decide (j<w) && x.testBit (w*i+j)) := by
  simp [get]

theorem layer_get (w s mask x : ℕ) (selected : ℕ → Bool)
    (hm : ∀ i j, j < w → mask.testBit (w*i+j) = selected i)
    (hd : ∀ i, selected i = true → selected (i+s) = false)
    (i : ℕ) : get w (layer w s mask x) i = get w x (switchIndex s selected i) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · simp only [testBit_get, hj, decide_true, Bool.true_and]
    have hsum : w*s+(w*i+j) = w*(i+s)+j := by simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm ]
    have hbound : w*s ≤ w*i+j ↔ s ≤ i := by
      constructor
      · intro h
        by_contra hn
        have hle : i+1 ≤ s := by omega
        have hm := Nat.mul_le_mul_left w hle
        rw [Nat.mul_add] at hm
        omega
      · intro h
        exact (Nat.mul_le_mul_left w h).trans (Nat.le_add_right _ _)
    by_cases hi : s ≤ i
    · have heq : w*i+j-w*s = w*(i-s)+j := by
        rw [Nat.mul_sub_left_distrib]
        have hle := Nat.mul_le_mul_left w hi
        omega
      have hsum' : w*s+(w*(i-s)+j) = w*i+j := by
        rw [Nat.mul_sub_left_distrib]
        have hle := Nat.mul_le_mul_left w hi
        omega
      have hback : i-s+s = i := Nat.sub_add_cancel hi
      simp only [layer, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight,
        Nat.testBit_shiftLeft, hsum, hbound, hi, decide_true, Bool.true_and, heq,
        hsum', hm i j hj, hm (i-s) j hj]
      cases hsel : selected i
      · cases hprev : selected (i-s)
        · simp [switchIndex, hsel, hprev, hi]
        · simp [switchIndex, hsel, hprev, hi]
      · have hprev : selected (i-s) = false := by
          cases hp : selected (i-s)
          · rfl
          · have hh := hd (i-s) hp
            rw [hback, hsel] at hh
            contradiction
        simp [switchIndex, hsel, hprev, Bool.xor_comm]
    · have hlt : ¬ w*s ≤ w*i+j := by simpa [hbound] using hi
      simp only [layer, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight,
        Nat.testBit_shiftLeft, hsum, hlt, decide_false, Bool.false_and,
        Bool.xor_false, hm i j hj]
      cases hsel : selected i <;> simp [switchIndex, hsel, hi, Bool.xor_comm]
  · simp [testBit_get, hj]

theorem switchIndex_involutive (s : ℕ) (selected : ℕ → Bool)
    (hd : ∀ i, selected i = true → selected (i+s) = false) :
    Function.Involutive (switchIndex s selected) := by
  intro i
  cases hsel : selected i
  · by_cases hp : s ≤ i ∧ selected (i-s) = true
    · have heq : i-s+s=i := Nat.sub_add_cancel hp.1
      simp [switchIndex, hsel, hp.1, hp.2, heq]
    · have hs : switchIndex s selected i = i := by simp [switchIndex, hsel, hp]
      rw [hs, hs]
  · have hn := hd i hsel
    have hs : s ≤ i+s := Nat.le_add_left _ _
    simp [switchIndex, hsel, hn, hs]

theorem switchIndex_lt (s n : ℕ) (selected : ℕ → Bool)
    (hb : ∀ i, selected i = true → i+s<n) {i : ℕ} (hi : i<n) :
    switchIndex s selected i < n := by
  unfold switchIndex
  split
  · exact hb i (by assumption)
  · split
    · exact (Nat.sub_le i s).trans_lt hi
    · exact hi

/-- The actual finite wire permutation justified by the disjointness and bounds. -/
def switchPerm (s n : ℕ) (selected : ℕ → Bool)
    (hd : ∀ i, selected i = true → selected (i+s) = false)
    (hb : ∀ i, selected i = true → i+s<n) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (f := fun i => ⟨switchIndex s selected i,
    switchIndex_lt s n selected hb i.isLt⟩) (by
      intro i
      apply Fin.ext
      exact switchIndex_involutive s selected hd i)
end Theory.GroupAction.PackedPermutation
