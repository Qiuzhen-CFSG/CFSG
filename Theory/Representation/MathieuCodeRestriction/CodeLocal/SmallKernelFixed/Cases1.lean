module
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Data

/-!
# Kernel certificates for translation indices 4 through 7

This is one independent part of the native fixed-word calculation. All entries
are verified by kernel reduction. The four parts allow Lake to check the finite
certificates independently. Source: Aschbacher--Smith, H.16.2 and H.16.8.
-/

public section
namespace MathieuCode.SmallKernelFixed

set_option maxRecDepth 100000 in
theorem maskCheck1 : ∀ n : Fin 16, n.val / 4 = 1 →
    (List.finRange 4096).all (fun u =>
      decide (encode16 (differenceRows n) u = 0 ↔ (fixedMasks n).getLsb u = true)) = true := by
  simp only [BitVec.getLsb, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  decide +kernel

set_option maxRecDepth 100000 in
theorem sizeCheck1 : ∀ n : Fin 16, n.val / 4 = 1 → n ≠ 0 →
    (fixedMasks n).cpop.toNat = 256 := by
  simp_rw [← Sporadic.Mathieu.bitVec_support_card]
  simp only [BitVec.getLsb, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  decide +kernel

set_option maxRecDepth 100000 in
theorem pairCheck1 : ∀ n m : Fin 16, n.val / 4 = 1 →
    n ≠ 0 → m ≠ 0 → n ≠ m → ((fixedMasks n) &&& (fixedMasks m)).cpop.toNat = 32 := by
  simp_rw [← Sporadic.Mathieu.bitVec_support_card, bitand_true]
  simp only [BitVec.getLsb, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  decide +kernel

end MathieuCode.SmallKernelFixed
