module

public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Cases0
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Cases1
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Cases2
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Cases3

/-!
# Native fixed-word counts

The checked masks count 256 words fixed by any nonzero translation, and 32
words fixed by two distinct nonzero translations. The certificates are divided
among four independent modules for compilation; this module combines them.
The comparison with actual native Golay words is proved in `Words.lean`.
Source: Aschbacher--Smith, H.16.2 and H.16.8, printed pp.402--405.
-/

public section
namespace MathieuCode.SmallKernelFixed

private theorem four_chunks (n : Fin 16) :
    n.val / 4 = 0 ∨ n.val / 4 = 1 ∨ n.val / 4 = 2 ∨ n.val / 4 = 3 := by omega

/-- The mask is exactly the kernel of the encoded translation difference. -/
theorem difference_zero_iff_mask (n : Fin 16) (u : Fin 4096) :
    encode16 (differenceRows n) u = 0 ↔ (fixedMasks n).getLsb u = true := by
  have h : (List.finRange 4096).all (fun b =>
      decide (encode16 (differenceRows n) b = 0 ↔ (fixedMasks n).getLsb b = true)) = true := by
    rcases four_chunks n with h | h | h | h
    · exact maskCheck0 n h
    · exact maskCheck1 n h
    · exact maskCheck2 n h
    · exact maskCheck3 n h
  exact of_decide_eq_true ((List.all_eq_true.mp h) u (List.mem_finRange u))

/-- Every nonzero translation has 256 fixed messages. -/
theorem fixedMasks_size (n : Fin 16) (hn : n ≠ 0) : (fixedMasks n).cpop.toNat = 256 := by
  rcases four_chunks n with h | h | h | h
  · exact sizeCheck0 n h hn
  · exact sizeCheck1 n h hn
  · exact sizeCheck2 n h hn
  · exact sizeCheck3 n h hn

/-- Two independent translations have 32 common fixed messages. -/
theorem fixedMasks_pair_size (n m : Fin 16) (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    ((fixedMasks n) &&& (fixedMasks m)).cpop.toNat = 32 := by
  rcases four_chunks n with h | h | h | h
  · exact pairCheck0 n m h hn hm hnm
  · exact pairCheck1 n m h hn hm hnm
  · exact pairCheck2 n m h hn hm hnm
  · exact pairCheck3 n m h hn hm hnm

end MathieuCode.SmallKernelFixed
