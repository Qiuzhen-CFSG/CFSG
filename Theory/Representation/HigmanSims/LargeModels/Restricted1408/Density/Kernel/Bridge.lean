module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Data
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Packed

/-!
# Connection of checked rows to the literal singular matrix

The fast XOR product is transported through the existing packed decoder.
A checked row table therefore denotes exactly `1 + B + A*B + B*A`.
The solution predicate used by elimination is its ordinary right kernel.
See `source/README.md` for the numerical source and certificate generation.
-/

@[expose] public section

namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData
open Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
open Thompson.BinaryMatrix
open PackedBinaryRows

lemma bit_fastProduct (n : Nat) (rows : Array Nat) (x j : Nat) (hlen : rows.size = n) :
    bit (fastProduct x rows.toList) j =
      ∑ k : Fin n, bit x k.val * bit rows[k.val]! j := by
  rw [fastProduct_eq, ← rowProduct_eq_listProduct x rows n hlen,
    Fin.sum_univ_eq_sum_range (fun k => bit x k * bit rows[k]! j)]
  exact bit_rowProduct x rows n j

lemma separating_decode (n : Nat) (a b s : Array Nat)
    (ha : a.size = n) (hb : b.size = n)
    (h : ∀ i : Fin n, 2^i.val ^^^ b[i.val]! ^^^
      fastProduct a[i.val]! b.toList ^^^ fastProduct b[i.val]! a.toList = s[i.val]!) :
    (1 + decode n b + decode n a * decode n b + decode n b * decode n a) = decode n s := by
  ext i j
  have hone : (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j = bit (2^i.val) j.val := by
    simp [Matrix.one_apply, bit, Nat.testBit_two_pow, Fin.ext_iff]
  change (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j + bit b[i.val]! j.val +
    (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) +
    (∑ k : Fin n, bit b[i.val]! k.val * bit a[k.val]! j.val) = bit s[i.val]! j.val
  rw [hone, ← h i, bit_xor, bit_xor, bit_xor, bit_fastProduct n b _ _ hb,
    bit_fastProduct n a _ _ ha]

lemma separatingMatrix_eq_decode (h : checkRange rowCheck 0 1408 = true) :
    separatingMatrix = decode 1408 sRows := by
  apply separating_decode 1408 aRows bRows sRows aRows_size bRows_size
  intro i
  simpa only [Nat.zero_add, rowCheck, beq_iff_eq] using
    (checkRange_spec _ _ _).mp h i.val i.isLt

lemma sRows_size : sRows.size = 1408 := by decide +kernel

lemma initial_solutions_iff (w : Vector) :
    stateSolutions 1408 state0000 w ↔ (decode 1408 sRows).mulVec w = 0 := by
  simp only [stateSolutions, state0000, solutions_nil, true_and]
  constructor
  · intro h
    funext i
    exact h sRows[i.val]! (by
      have hi : i.val < sRows.size := by rw [sRows_size]; exact i.isLt
      simpa only [getElem!_pos sRows i.val hi] using Array.getElem_mem_toList hi)
  · intro h r hr
    obtain ⟨i, hi, hr⟩ := List.mem_iff_getElem.mp hr
    have hin : i < 1408 := by simpa only [Array.length_toList, sRows_size] using hi
    have his : i < sRows.size := by rwa [sRows_size]
    have hrs : sRows[i]! = r := by
      simpa only [Array.getElem_toList, getElem!_pos sRows i his] using hr
    have he := congrFun h ⟨i, hin⟩
    change (fun j : Fin 1408 => bit sRows[i]! j.val) ⬝ᵥ w = 0 at he
    simpa only [hrs] using he

end Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData
