module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# A list traversal checker for packed binary products

The original indexed row checker repeatedly looks up rows in a literal array.
This checker traverses the right matrix's list once, XORing the selected rows.
Induction shows that each bit is the corresponding matrix dot product; hence
kernel reduction of this checker certifies the same ordinary matrix product.
This avoids repeated indexed traversal while retaining kernel-checked proofs.
-/

@[expose] public section

open scoped BigOperators
namespace Thompson.BinaryMatrix

def listProduct (a : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | b :: bs, k => (if a.testBit k then b else 0) ^^^ listProduct a bs (k+1)

theorem bit_listProduct (a : ℕ) (bs : List ℕ) (j k : ℕ) :
    bit (listProduct a bs k) j =
      ∑ i : Fin bs.length, bit a (k + i.val) * bit bs[i.val] j := by
  induction bs generalizing k with
  | nil => simp [listProduct, bit]
  | cons b bs ih =>
    rw [listProduct, bit_xor, ih]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero,
      List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    congr 1
    · cases h : a.testBit k <;> simp [bit, h]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Nat.add_assoc, Nat.add_comm 1]

theorem decode_mul_list (n : ℕ) (a b c : Array ℕ) (hb : b.size = n)
    (h : ∀ i : Fin n, listProduct a[i.val]! b.toList 0 = c[i.val]!) :
    decode n a * decode n b = decode n c := by
  subst n
  ext i j
  change (∑ k : Fin b.size, bit a[i.val]! k.val * bit b[k.val]! j.val) =
    bit c[i.val]! j.val
  rw [← h i, bit_listProduct]
  simp only [Array.length_toList, Nat.zero_add, Array.getElem_toList]
  congr 1
  funext k
  rw [getElem!_pos b k.val k.isLt]

theorem decode_mul_one_list (n : ℕ) (a b : Array ℕ) (hb : b.size = n)
    (h : ∀ i : Fin n, listProduct a[i.val]! b.toList 0 = 2 ^ i.val) :
    decode n a * decode n b = 1 := by
  subst n
  ext i j
  have he : (∑ k : Fin b.size, bit a[i.val]! k.val * bit b[k.val]! j.val) =
      bit (listProduct a[i.val]! b.toList 0) j.val := by
    rw [bit_listProduct]
    simp only [Array.length_toList, Nat.zero_add, Array.getElem_toList]
    congr 1
    funext k
    rw [getElem!_pos b k.val k.isLt]
  change (∑ k : Fin b.size, bit a[i.val]! k.val * bit b[k.val]! j.val) = _
  rw [he, h i]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
end Thompson.BinaryMatrix
