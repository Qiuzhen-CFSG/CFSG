module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Packed
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Sections

/-!
# Soundness of rectangular packed section checks

The sequential XOR checker computes rectangular products over GF(2).
The right inverse uses the kernel-then-lift indexing of `Small.Sections`;
its two row checks prove independence without changing that public convention.
These lemmas are applied to the numerical witnesses in `SectionCertificates`.
Source data and attribution: `Binary/source/README.md`.
-/

@[expose] public section
open Matrix Thompson.BinaryMatrix PackedBinaryRows
open Representation.HigmanSims.LargeModels.Binary.Small
namespace Representation.HigmanSims.LargeModels.Binary.Small.SectionCertificates

def rect (m n : ℕ) (a : Array ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit a[i.val]! j.val

theorem mul_apply_list {m n p : ℕ} (a b : Array ℕ) (hb : b.size = n)
    (i : Fin m) (j : Fin p) :
    (rect m n a * rect n p b) i j = bit (listProduct a[i.val]! 0 b.toList) j.val := by
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => bit a[i.val]! k * bit b[k]! j.val),
    ← bit_rowProduct, Packed.rowProduct_list _ _ _ hb]

theorem mul_eq_checked {m n p q : ℕ} (a b c d : Array ℕ)
    (hb : b.size = n) (hd : d.size = q)
    (h : ∀ i : Fin m, listProduct a[i.val]! 0 b.toList =
      listProduct c[i.val]! 0 d.toList) :
    rect m n a * rect n p b = rect m q c * rect q p d := by
  ext i j
  rw [mul_apply_list _ _ hb, mul_apply_list _ _ hd, h i]

theorem mul_eq_add_checked {m n p q t : ℕ} (a b c d e f : Array ℕ)
    (hb : b.size = n) (hd : d.size = q) (hf : f.size = t)
    (h : ∀ i : Fin m, listProduct a[i.val]! 0 b.toList =
      listProduct c[i.val]! 0 d.toList ^^^ listProduct e[i.val]! 0 f.toList) :
    rect m n a * rect n p b = rect m q c * rect q p d + rect m t e * rect t p f := by
  ext i j
  simp only [Matrix.add_apply, mul_apply_list _ _ hb, mul_apply_list _ _ hd,
    mul_apply_list _ _ hf, h i, bit_xor]

def rightInverse (r n : ℕ) (a : Array ℕ) :
    Matrix (Fin 190) (Fin r ⊕ Fin n) (ZMod 2) :=
  (rect 190 (r+n) a).submatrix id finSumFinEquiv

theorem independent_checked {r n : ℕ} (a b c : Array ℕ) (hc : c.size = 190)
    (hN : ∀ i : Fin r, listProduct a[i.val]! 0 c.toList = 2 ^ i.val)
    (hU : ∀ i : Fin n, listProduct b[i.val]! 0 c.toList = 2 ^ (r+i.val)) :
    sectionRows (rect r 190 a) (rect n 190 b) * rightInverse r n c = 1 := by
  have h (i j : Fin r ⊕ Fin n) :
      (sectionRows (rect r 190 a) (rect n 190 b) * rightInverse r n c) i j =
      bit (2 ^ (finSumFinEquiv i : Fin (r+n)).val) (finSumFinEquiv j : Fin (r+n)).val := by
    cases i with
    | inl i =>
      change (rect r 190 a * rect 190 (r+n) c) i (finSumFinEquiv j) = _
      rw [mul_apply_list _ _ hc, hN]
      rfl
    | inr i =>
      change (rect n 190 b * rect 190 (r+n) c) i (finSumFinEquiv j) = _
      rw [mul_apply_list _ _ hc, hU]
      rfl
  ext i j
  rw [h]
  simp only [bit, Nat.testBit_two_pow, Matrix.one_apply]
  have he : ((finSumFinEquiv i : Fin (r+n)).val = (finSumFinEquiv j : Fin (r+n)).val) ↔ i = j := by
    rw [← Fin.ext_iff, Equiv.apply_eq_iff_eq]
  simp only [he, decide_eq_true_eq]

end Representation.HigmanSims.LargeModels.Binary.Small.SectionCertificates
