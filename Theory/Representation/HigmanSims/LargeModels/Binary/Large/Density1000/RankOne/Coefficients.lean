module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Data
/-!
# The source polynomial's coefficient mask

A sequential check compares each natural coefficient with the next bit of the
mask, consuming the mask by division by two. Its soundness theorem proves the
coordinatewise equality in `ZMod 2` without repeating large-array indexing
inside a finite universal computation. This fixes the increasing-exponent
convention used by `Setup.polynomialMatrix` and `Values.polynomial_row`.

Source: `Binary/source/density1000.json`; ATLAS attribution and rights are
retained in `Binary/source/README.md`. Original Lean code is Apache-2.0.
-/

@[expose] public section
open Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

def checkCoefficients (x : ℕ) : List ℕ → Bool
  | [] => true
  | c :: cs => (c == if x.testBit 0 then 1 else 0) && checkCoefficients (x / 2) cs

theorem checkCoefficients_get (x : ℕ) (cs : List ℕ)
    (h : checkCoefficients x cs = true) (i : ℕ) (hi : i < cs.length) :
    (cs[i]! : ZMod 2) = bit x i := by
  induction cs generalizing x i with
  | nil => simp at hi
  | cons c cs ih =>
    simp only [checkCoefficients, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero =>
      simp only [List.getElem!_cons_zero, h.1, bit]
      split <;> rfl
    | succ i =>
      simpa only [List.getElem!_cons_succ, bit, Nat.testBit_div_two] using
        ih (x / 2) h.2 i (by simpa using hi)

theorem coefficient_check : checkCoefficients polynomialMask Data.coefficients.toList = true := by
  decide +kernel

theorem coefficient_eq_mask (i : Fin 1000) : coefficient i = bit polynomialMask i.val := by
  have hs : Data.coefficients.size = 1000 := by decide +kernel
  have hi : i.val < Data.coefficients.toList.length := by
    rw [Array.length_toList, hs]
    exact i.isLt
  have he := checkCoefficients_get polynomialMask Data.coefficients.toList coefficient_check i.val hi
  simpa only [Array.getElem!_toList, coefficient] using he

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
