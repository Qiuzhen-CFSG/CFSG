module
public import Theory.GroupAction.PackedPermutation.Layer
public import Theory.GroupAction.PackedPermutation.Ramp
/-!
# Fixed padding preserves the original permutation action

A smaller table is padded with the identity above its original degree.
A finite permutation with that packed table fixes every added wire. Its
bijectivity therefore forces each original wire to remain in the original
segment, removing the modulo used by the existing source lookup maps.
The resulting intertwining retains the literal old action and its inclusion.
-/
@[expose] public section
namespace Theory.GroupAction.PackedPermutation

def padded (w n N x : Nat) : Nat := x ||| ((ramp w N >>> (w*n)) <<< (w*n))

theorem get_padded_low (w n N x i : Nat) (hi : i<n) :
    get w (padded w n N x) i = get w x i := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<w
  · have hle := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at hle
    have hlt : ¬w*n ≤ w*i+j := by omega
    simp only [testBit_get, hj, decide_true, Bool.true_and, padded,
      Nat.testBit_or, Nat.testBit_shiftLeft, hlt, decide_false, Bool.false_and,
      Bool.or_false]
  · simp [testBit_get, hj]

theorem get_padded_high (w n N x i : Nat) (hi : n ≤ i) (hx : x<2^(w*n)) :
    get w (padded w n N x) i = get w (ramp w N) i := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<w
  · have hle : w*n ≤ w*i+j := (Nat.mul_le_mul_left w hi).trans (Nat.le_add_right _ _)
    have hxbit : x.testBit (w*i+j)=false :=
      Nat.testBit_eq_false_of_lt (hx.trans_le (Nat.pow_le_pow_right (by decide) hle))
    have he : w*n+(w*i+j-w*n)=w*i+j := Nat.add_sub_of_le hle
    simp only [testBit_get, hj, decide_true, Bool.true_and, padded,
      Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, hle,
      hxbit, Bool.false_or, he]
  · simp [testBit_get, hj]

theorem prefix_lt_of_fixed_padding {n N : Nat} (hn : n≤N) (p : Equiv.Perm (Fin N))
    (hp : ∀ i : Fin N, n ≤ i.val → p i=i) (i : Fin n) :
    (p (Fin.castLE hn i)).val < n := by
  by_contra h
  have he := p.injective (hp (p (Fin.castLE hn i)) (by omega))
  have hev := congrArg Fin.val he
  simp only [Fin.val_castLE] at hev
  omega

theorem source_intertwining_of_padded_table
    {w n N x : Nat} (hw : 0<w) (hn : n≤N) (hN : N≤2^w) (hx : x<2^(w*n))
    (p : Equiv.Perm (Fin N)) (q : Equiv.Perm (Fin n))
    (hp : ∀ i : Fin N, get w (padded w n N x) i.val = (p i).val)
    (hq : ∀ i : Fin n, get w x i.val % n = (q i).val) :
    ∀ i : Fin n, p (Fin.castLE hn i) = Fin.castLE hn (q i) := by
  have hfix : ∀ i : Fin N, n ≤ i.val → p i=i := by
    intro i hi
    apply Fin.ext
    rw [← hp, get_padded_high w n N x i.val hi hx]
    exact get_ramp hw hN i.isLt
  intro i
  have hb := prefix_lt_of_fixed_padding hn p hfix i
  have he := hp (Fin.castLE hn i)
  simp only [Fin.val_castLE] at he
  rw [get_padded_low w n N x i.val i.isLt] at he
  apply Fin.ext
  simp only [Fin.val_castLE]
  rw [← he, ← hq i]
  exact (Nat.mod_eq_of_lt (by omega)).symm
end Theory.GroupAction.PackedPermutation
