module

public import Theory.Representation.BinaryCubicPairs.FixedCount
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Pi

/-!
# The full-support predicate from actual matrix displacement

The standard cubic moves precisely the first coordinate plane. If its
moved space and that of a second cubic span the four-space, projection on
the last two coordinates makes the second displacement surjective there.
This is exactly the full-support predicate used by the finite checker.

Source application: Aschbacher--Smith E.6.24, printed p.255.
-/

public section
namespace BinaryCubicPairs
open Packed

private theorem cubic_tail (x : BitVec 4) :
    (mv cubic x ^^^ x).extractLsb' 2 2 = 0 := by
  have h : ∀ x : BitVec 4, (mv cubic x ^^^ x).extractLsb' 2 2 = 0 := by decide +kernel
  exact h x

private theorem tail_xor (x y : BitVec 4) :
    (x ^^^ y).extractLsb' 2 2 = x.extractLsb' 2 2 ^^^ y.extractLsb' 2 2 := by
  have h : ∀ x y : BitVec 4,
      (x ^^^ y).extractLsb' 2 2 = x.extractLsb' 2 2 ^^^ y.extractLsb' 2 2 := by decide +kernel
  exact h x y

/-- Every genuine full-support noncommuting cubic pair satisfies the
literal Boolean hypotheses of the exhaustive word certificate. -/
theorem ready_of_matrices (m : BitVec 16)
    (hpow : (toMat m) ^ 3 = 1)
    (hfixed : Module.finrank (ZMod 2) (fixedKernel (toMat m)) = 2)
    (hfull : ∀ v : CoordinateVector, ∃ x y : CoordinateVector,
      (toMat cubic).mulVec x - x + ((toMat m).mulVec y - y) = v)
    (hnc : toMat cubic * toMat m ≠ toMat m * toMat cubic) : readyB m = true := by
  have hm : mm (mm m m) m = ident := by
    apply toMat_injective
    simpa only [toMat_mm, ident, toMat_one, pow_succ, pow_zero, one_mul] using hpow
  have hcount := fixed_count_four m hfixed
  have htail : (List.range 4).all (fun q => (List.range 16).any fun z =>
      (mv m (BitVec.ofNat 4 z) ^^^ BitVec.ofNat 4 z).extractLsb' 2 2 == BitVec.ofNat 2 q) = true := by
    apply List.all_eq_true.mpr
    intro q hq
    have hqlt := List.mem_range.mp hq
    let v : BitVec 4 := (BitVec.ofNat 2 q) ++ (0 : BitVec 2)
    obtain ⟨x, y, hxy⟩ := hfull (toVec v)
    obtain ⟨u, hu⟩ := toVec_surjective x
    obtain ⟨w, hw⟩ := toVec_surjective y
    have he : (mv cubic u ^^^ u) ^^^ (mv m w ^^^ w) = v := by
      apply toVec_injective
      simpa only [toVec_xor, toVec_mv, hu, hw, CharTwo.sub_eq_add] using hxy
    have hh := congrArg (fun z : BitVec 4 => z.extractLsb' 2 2) he
    rw [tail_xor, cubic_tail] at hh
    have hzxor : ∀ z : BitVec 2, (0 : BitVec 2) ^^^ z = z := by decide +kernel
    rw [hzxor] at hh
    have hv : v.extractLsb' 2 2 = BitVec.ofNat 2 q := BitVec.extractLsb'_append_eq_left
    rw [hv] at hh
    apply List.any_eq_true.mpr
    refine ⟨w.toNat, List.mem_range.mpr w.isLt, ?_⟩
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, beq_iff_eq] using hh
  have hcomm : mm cubic m ≠ mm m cubic := by
    intro he
    apply hnc
    exact (toMat_mm _ _).symm.trans ((congrArg toMat he).trans (toMat_mm _ _))
  simp only [readyB, hm, hcount, htail, beq_self_eq_true, Bool.true_and,
    Bool.and_true, Bool.not_eq_true', Bool.eq_false_iff]
  exact fun he => hcomm (beq_iff_eq.mp he)

end BinaryCubicPairs
