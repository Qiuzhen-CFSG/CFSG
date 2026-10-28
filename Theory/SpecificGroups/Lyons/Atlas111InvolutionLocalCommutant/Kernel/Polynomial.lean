module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Polynomial.Weighted
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Polynomial.Subtract

/-!
# Identification of the local annihilator polynomial

Each word matrix is certified along the binary word tree. Carry-free row
arithmetic then certifies the weighted sum and entrywise subtraction. Thus the
decoded annihilator is exactly the polynomial appearing in the kernel contract.
Source and candidate generation: `Kernel/source/GeneratePolynomial.py`.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Kernel
open Atlas111WordCertificate Matrix
open scoped BigOperators

private theorem sum_eq :
    (∑ k : Fin 111, coefficients k • decode (wordRows k)) = sumMatrix := by
  ext i j
  rw [Matrix.sum_apply]
  change (∑ k : Fin 111, (digit qPacked k.val : ZMod 5) *
    (digit (wordRows k i) j.val : ZMod 5)) = (digit (sumRows i) j.val : ZMod 5)
  simp only [← Nat.cast_mul]
  rw [← Nat.cast_sum, ← rowProduct_digit _ _ q_small (fun k => word_small k i) j,
    ← ZMod.natCast_mod, digitsEq_sound _ _ _ (weighted_rows i) j.val j.isLt]

private theorem subtract_eq : w111Matrix - sumMatrix = rMatrix := by
  ext i j
  have h := beq_iff_eq.mp (allRows_sound (subtract_rows i) j)
  have hc := congrArg (fun n : ℕ => (n : ZMod 5)) h
  simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc
  change (digit (w111Rows i) j.val : ZMod 5) -
    (digit (sumRows i) j.val : ZMod 5) = (digit (rRows i) j.val : ZMod 5)
  have hfour : (4 : ZMod 5) = -1 := by decide +kernel
  rw [hfour] at hc
  simpa only [neg_one_mul, ← sub_eq_add_neg] using hc

/-- The packed annihilator is the exact word polynomial required by the contract. -/
public theorem polynomial_eq :
    localAnnihilator abMatrix Words.localBMatrix coefficients = rMatrix := by
  unfold localAnnihilator
  have hlead := word111
  rw [localWord] at hlead
  norm_num only [Nat.reduceMod, Nat.reduceDiv, ite_true, ite_false] at hlead
  rw [hlead]
  simp_rw [word_eq]
  rw [sum_eq]
  exact subtract_eq

end Lyons.SimplicityCertificate.LocalCommutant.Kernel
