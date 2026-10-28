module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.Program
import Mathlib.Tactic.FinCases

/-!
# The marked quotient words in the checked program

These equations identify the certificate's three nonidentity targets with
X, (XY)^7, and ((XY)^5 Y)^4. Their equality with the published images q(lift j)
then follows from the existing quotient-map and conjugation certificates.
-/

set_option maxRecDepth 100000

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound QuotientOrderCertificate

def markedIndex : Fin 4 → Fin 7392 := ![0, 1, 16, 50]

theorem element_basic (i : Fin 4) : element (Fin.ofNat 7392 i.val) = basic i := by
  apply Subtype.ext
  apply Units.ext
  rw [element_val]
  fin_cases i <;> decide +kernel

private theorem xy_eq : basic 1 * basic 2 = element 4 := by
  rw [← element_basic 1, ← element_basic 2]
  exact productCheck_sound (by decide +kernel)

private theorem xy_pow2 : (basic 1 * basic 2)^2 = element 6 := by
  rw [pow_succ, pow_one, xy_eq]
  exact productCheck_sound (by decide +kernel)

private theorem xy_pow3 : (basic 1 * basic 2)^3 = element 8 := by
  rw [pow_succ, xy_pow2, xy_eq]
  exact productCheck_sound (by decide +kernel)

private theorem xy_pow4 : (basic 1 * basic 2)^4 = element 10 := by
  rw [pow_succ, xy_pow3, xy_eq]
  exact productCheck_sound (by decide +kernel)

private theorem xy_pow5 : (basic 1 * basic 2)^5 = element 12 := by
  rw [pow_succ, xy_pow4, xy_eq]
  exact productCheck_sound (by decide +kernel)

private theorem xy_pow6 : (basic 1 * basic 2)^6 = element 14 := by
  rw [pow_succ, xy_pow5, xy_eq]
  exact productCheck_sound (by decide +kernel)

private theorem xy_pow7 : (basic 1 * basic 2)^7 = element 16 := by
  rw [pow_succ, xy_pow6, xy_eq]
  exact productCheck_sound (by decide +kernel)

private theorem v_eq : (basic 1 * basic 2)^5 * basic 2 = element 17 := by
  rw [xy_pow5, ← element_basic 2]
  exact productCheck_sound (by decide +kernel)

private theorem v_pow2 : ((basic 1 * basic 2)^5 * basic 2)^2 = element 28 := by
  rw [pow_succ, pow_one, v_eq]
  exact productCheck_sound (by decide +kernel)

private theorem v_pow3 : ((basic 1 * basic 2)^5 * basic 2)^3 = element 39 := by
  rw [pow_succ, v_pow2, v_eq]
  exact productCheck_sound (by decide +kernel)

private theorem v_pow4 : ((basic 1 * basic 2)^5 * basic 2)^4 = element 50 := by
  rw [pow_succ, v_pow3, v_eq]
  exact productCheck_sound (by decide +kernel)

private theorem element_marked_small (j : Fin 4) : element (markedIndex j) = marked j := by
  fin_cases j
  · change element 0 = 1
    exact element_zero
  · apply Subtype.ext
    apply Units.ext
    rw [element_val]
    decide +kernel
  · change element 16 = (basic 1 * basic 2)^7
    exact xy_pow7.symm
  · change element 50 = ((basic 1 * basic 2)^5 * basic 2)^4
    exact v_pow4.symm

theorem element_marked (j : Fin 4) : element (markedIndex j) = q (lift j) :=
  (element_marked_small j).trans (marked_eq j)

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
