module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks

/-!
# Extracting a column from packed rows

Pack rows in base `2 ^ s`. A mask selects bit `j` of each row. Reduction
modulo an integer for which `2 ^ s` is congruent to 2 then compacts these
selected bits into the literal `columnFromRows`. The length bound prevents
wraparound. This replaces repeated list traversals by checked integer arithmetic.

Source: the original row convention in Coefficients/Arithmetic.lean and
Columns/source/README.md; the packing argument here is elementary.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.Rows

def pack (s : Nat) : List Nat → Nat
  | [] => 0
  | r :: rs => 2 ^ s * pack s rs + r

lemma testBit_pack (s : Nat) (rs : List Nat)
    (hr : ∀ r ∈ rs, r < 2 ^ s) (i j : Nat) (hj : j < s) :
    (pack s rs).testBit (s * i + j) = (rs[i]!).testBit j := by
  induction rs generalizing i with
  | nil => simp [pack]
  | cons r rs ih =>
    have h0 := hr r (by simp)
    have hs : ∀ r ∈ rs, r < 2 ^ s := fun r h => hr r (by simp [h])
    cases i with
    | zero => simp [pack, Nat.testBit_two_pow_mul_add _ h0, hj]
    | succ i =>
      have hge : ¬ s * (i + 1) + j < s := by simp only [Nat.mul_add, Nat.mul_one]; omega
      have heq : s * (i + 1) + j - s = s * i + j := by simp only [Nat.mul_add, Nat.mul_one]; omega
      simpa only [pack, Nat.testBit_two_pow_mul_add _ h0, if_neg hge, heq,
        List.getElem!_cons_succ] using ih hs i

lemma testBit_pack_div (s : Nat) (hs : 0 < s) (rs : List Nat)
    (hr : ∀ r ∈ rs, r < 2 ^ s) (t : Nat) :
    (pack s rs).testBit t = (rs[t / s]!).testBit (t % s) := by
  have h := testBit_pack s rs hr (t / s) (t % s) (Nat.mod_lt _ hs)
  have ht := Nat.mod_add_div t s
  convert h using 1
  congr 1
  omega

lemma map_bit_get (rs : List Nat) (j i : Nat) :
    (rs.map (fun r => (r.testBit j).toNat))[i]! = ((rs[i]!).testBit j).toNat := by
  induction rs generalizing i with
  | nil => simp
  | cons r rs ih =>
    cases i with
    | zero => simp only [List.map_cons, List.getElem!_cons_zero]
    | succ i => simpa only [List.map_cons, List.getElem!_cons_succ] using ih i

lemma replicate_get (n i : Nat) :
    (List.replicate n 1 : List Nat)[i]! = if i < n then 1 else 0 := by
  by_cases h : i < n
  · simp [getElem!_pos, h]
  · simp [getElem!_neg, h]

lemma masked_pack (s : Nat) (hs : 0 < s) (rs : List Nat)
    (hr : ∀ r ∈ rs, r < 2 ^ s) (j : Nat) (hj : j < s) :
    (pack s rs >>> j) &&& pack s (List.replicate rs.length 1) =
      pack s (rs.map (fun r => (r.testBit j).toNat)) := by
  have h2 : 1 < 2 ^ s := Nat.one_lt_two_pow_iff.mpr (by omega)
  have hm : ∀ r ∈ List.replicate rs.length 1, r < 2 ^ s := by
    intro r h
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp h
    exact h2
  have hb : ∀ r ∈ rs.map (fun r => (r.testBit j).toNat), r < 2 ^ s := by
    intro r h
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
    exact lt_of_le_of_lt (by cases a.testBit j <;> decide) h2
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and, Nat.testBit_shiftRight,
    testBit_pack_div s hs _ hm, testBit_pack_div s hs _ hb,
    replicate_get, map_bit_get, Nat.testBit_bool_toNat]
  by_cases hz : t % s = 0
  · have ht := Nat.mod_add_div t s
    have hx : (pack s rs).testBit (j + t) = (rs[t / s]!).testBit j := by
      rw [show j + t = s * (t / s) + j by omega]
      exact testBit_pack s rs hr _ _ hj
    rw [hx]
    by_cases hi : t / s < rs.length
    · simp [hz, hi]
    · simp [hz, hi]
  · have h1 : (1 : Nat).testBit (t % s) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact hz (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h)
    split <;> simp [h1, hz]

lemma pack_mod (s m : Nat) (h : 2 ^ s % m = 2 % m) (rs : List Nat) :
    pack s rs % m = pack 1 rs % m := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [pack, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, h, ih, pow_one]

lemma binary_pack (rs : List Nat) (j : Nat) :
    pack 1 (rs.map (fun r => (r.testBit j).toNat)) = columnFromRows j rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, pack, pow_one, ih, columnFromRows]
    have h := Nat.shiftLeft_add_eq_or_of_lt (i := 1)
      (show (r.testBit j).toNat < 2 ^ 1 by cases r.testBit j <;> decide)
      (columnFromRows j rs)
    have hb : (r.testBit j).toNat = if r.testBit j then 1 else 0 := by
      cases r.testBit j <;> rfl
    simpa only [Nat.shiftLeft_eq, pow_one, Nat.mul_comm, hb, Nat.or_comm] using h

lemma column_lt (rs : List Nat) (j : Nat) : columnFromRows j rs < 2 ^ rs.length := by
  rw [← binary_pack]
  induction rs with
  | nil => simp [pack]
  | cons r rs ih =>
    simp only [List.map_cons, pack, List.length_cons, pow_succ]
    have hb : (r.testBit j).toNat ≤ 1 := by cases r.testBit j <;> decide
    omega

lemma fast_column (s m : Nat) (hs : 0 < s) (rs : List Nat)
    (hr : ∀ r ∈ rs, r < 2 ^ s) (hpow : 2 ^ s % m = 2 % m)
    (hlen : 2 ^ rs.length ≤ m) (j : Nat) (hj : j < s) :
    ((pack s rs >>> j) &&& pack s (List.replicate rs.length 1)) % m =
      columnFromRows j rs := by
  rw [masked_pack s hs rs hr j hj, pack_mod s m hpow, binary_pack]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (column_lt rs j) hlen)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.Rows
