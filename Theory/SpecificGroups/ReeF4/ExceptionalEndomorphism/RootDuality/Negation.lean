module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality

-- Internal extension of the F4 duality proof: reuse its root-fingerprint certificate.
import all Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.F4ModelAdapter

/-!
# Opposition and the exceptional F4 duality

The exceptional permutation commutes with root negation. The proof uses the
classification's root-fingerprint certificate: positivity and the four Coxeter
products determine a root, and negation preserves all those products. Geometric
root length is unchanged under negation, so the exceptional parameter formula
also agrees on opposite roots.

This extends the root datum used in Aschbacher–Smith, Remark A.2.4, with the
opposition identities needed for the negative simple-root curves.
-/

public section

namespace ReeF4

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped Classical

noncomputable local instance : Fintype typeF4Roots := Fintype.ofFinite _

theorem exceptionalRootPermutation_neg (r : typeF4Roots) :
    letI := typeF4RootPairing.indexNeg
    exceptionalRootPermutation (-r) = -exceptionalRootPermutation r := by
  let := typeF4RootPairing.indexNeg
  have hs := (typeF4RootPairing.isPositiveRootDuality_iff
    typeF4RootPairing_base exceptionalRootPermutation).mp exceptionalRootPermutation_spec
  apply f4Root_eq_of_sign_and_coxeter typeF4RootPairing.toInvariantForm
    typeF4RootPairing_base typeF4RootPairing_baseEquiv.symm
    (fun i j => typeF4RootPairing_base_cartan_apply i j)
  · rw [← hs.2.1,
      RootPairing.Base.IsPos.neg_iff_not, RootPairing.Base.IsPos.neg_iff_not,
      hs.2.1]
  · intro j
    have h₁ := hs.2.2.2.2 (-r)
      (typeF4SimpleRootIndex (Fin.revPerm j))
    have h₂ := hs.2.2.2.2 r
      (typeF4SimpleRootIndex (Fin.revPerm j))
    simp only [exceptionalRootPermutation_simple, Fin.revPerm_apply, Fin.rev_rev] at h₁ h₂
    simp only [RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left,
      RootPairing.pairingIn_reflectionPerm_self_right, neg_mul_neg] at h₁ ⊢
    exact h₁.trans h₂.symm

theorem isLongRoot_neg_iff (r : typeF4Roots) :
    letI := typeF4RootPairing.indexNeg
    IsLongRoot (-r) ↔ IsLongRoot r := by
  let := typeF4RootPairing.indexNeg
  have hval : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  have hn : dot (-r).val (-r).val = dot r.val r.val := by
    rw [hval]
    simp [dot]
  by_cases hr : IsLongRoot r <;> by_cases hs : IsLongRoot (-r)
  · simp only [hr, hs]
  · have h₁ := isLongRoot_norm r hr
    have h₂ := isShortRoot_norm (-r) hs
    rw [hn, h₁] at h₂
    norm_num at h₂
  · have h₁ := isShortRoot_norm r hr
    have h₂ := isLongRoot_norm (-r) hs
    rw [hn, h₁] at h₂
    norm_num at h₂
  · simp only [hr, hs]

theorem isShortRoot_neg_iff (r : typeF4Roots) :
    letI := typeF4RootPairing.indexNeg
    IsShortRoot (-r) ↔ IsShortRoot r := by
  let := typeF4RootPairing.indexNeg
  exact not_congr (isLongRoot_neg_iff r)

/-- Duality reverses the numbered diagram on the negative simple roots as well. -/
theorem exceptionalRootPermutation_neg_simple (i : Fin 4) :
    letI := typeF4RootPairing.indexNeg
    exceptionalRootPermutation (-typeF4SimpleRootIndex i) =
      -typeF4SimpleRootIndex (Fin.revPerm i) := by
  let := typeF4RootPairing.indexNeg
  rw [exceptionalRootPermutation_neg, exceptionalRootPermutation_simple]

/-- Opposite root curves have the same exceptional parameter exponent. -/
theorem exceptionalParameter_neg {K : Type*} [Monoid K]
    (r : typeF4Roots) (t : K) :
    letI := typeF4RootPairing.indexNeg
    exceptionalParameter (-r) t = exceptionalParameter r t := by
  let := typeF4RootPairing.indexNeg
  by_cases hr : IsLongRoot r
  · rw [exceptionalParameter_of_long hr,
      exceptionalParameter_of_long ((isLongRoot_neg_iff r).mpr hr)]
  · rw [exceptionalParameter_of_short hr,
      exceptionalParameter_of_short ((isShortRoot_neg_iff r).mpr hr)]

end ReeF4
