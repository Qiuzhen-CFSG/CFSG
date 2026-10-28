/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Loop
public import Theory.AtlasPort.OtherSporadic.Algebra.BinaryCocycleSplitting

/-!
# Sign corrections for Parker-loop permutations

A lift of a linear code map is a loop permutation precisely when its sign
correction satisfies the factor-set equation. Every multiplicative permutation
fixing signs has this normal form. This supplies the lifting calculation behind
Aschbacher, Lemma 12.16 and the standard automorphisms in Section 14.

Adapted from Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerLoopLifts.lean`, `Atlas/Fischer/ParkerSignNormalForm.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Changes: CFSG module imports, local triality namespace, Lean 4.33 proof syntax,
and compatibility with the existing concrete `IsStandard` predicate.
-/

@[expose] public section

namespace Sporadic.Monster.Construction.TrialitySpin
open Atlas.Fischer Atlas.Codes

/-- An actual permutation of the loop, with the required sign correction. -/
def parkerLoopLift (g : golay ≃ₗ[Bit] golay) (η : golay → Bit) : Equiv.Perm ParkerLoop where
  toFun x := (g x.1, x.2 + η x.1)
  invFun x := (g.symm x.1, x.2 + η (g.symm x.1))
  left_inv x := by
    apply Prod.ext
    · exact g.symm_apply_apply _
    · simp only [g.symm_apply_apply]
      have h : ∀ b : Bit, b + b = 0 := by decide
      simp only [add_assoc, h, add_zero]
  right_inv x := by
    apply Prod.ext
    · exact g.apply_symm_apply _
    · have h : ∀ b : Bit, b + b = 0 := by decide
      simp only [add_assoc, h, add_zero]

theorem parkerLoopLift_preserves_multiply (g : golay ≃ₗ[Bit] golay) (η : golay → Bit)
    (hη : ∀ a b, η (a + b) + η a + η b =
      parkerGolayFactorSet (g a) (g b) + parkerGolayFactorSet a b) (x y : ParkerLoop) :
    parkerLoopLift g η (parkerLoopMultiply x y) =
      parkerLoopMultiply (parkerLoopLift g η x) (parkerLoopLift g η y) := by
  apply Prod.ext
  · exact g.map_add _ _
  · change x.2 + y.2 + parkerGolayFactorSet x.1 y.1 + η (x.1 + y.1) =
      x.2 + η x.1 + (y.2 + η y.1) + parkerGolayFactorSet (g x.1) (g y.1)
    have h := congrArg (fun z => z + x.2 + y.2 + η x.1 + η y.1 +
      parkerGolayFactorSet x.1 y.1) (hη x.1 y.1)
    convert h using 1 <;> ring_nf <;>
      simp only [show (2 : Bit) = 0 from rfl, mul_zero, add_zero]

theorem parkerLoopLift_sign (g : golay ≃ₗ[Bit] golay) (η : golay → Bit)
    (s : Bit) (x : ParkerLoop) :
    parkerLoopLift g η (parkerSign s x) = parkerSign s (parkerLoopLift g η x) := by
  apply Prod.ext
  · rfl
  · change x.2 + s + η x.1 = x.2 + η x.1 + s
    ring

theorem parkerLoopLift_fixes_sign (g : golay ≃ₗ[Bit] golay) (η : golay → Bit)
    (hη : η 0 = 0) (s : Bit) : parkerLoopLift g η (0, s) = (0, s) := by
  simp [parkerLoopLift, hη]

end Sporadic.Monster.Construction.TrialitySpin

namespace Sporadic.Monster.Construction.TrialitySpin
open Atlas.Fischer Atlas.Codes

/-- The sign coordinate of a loop permutation on the zero-sign representatives. -/
def parkerPermutationCorrection (e : Equiv.Perm ParkerLoop) (a : golay) : Bit := (e (a,0)).2

theorem parkerPermutationCorrection_zero (e : Equiv.Perm ParkerLoop)
    (hfix : ∀ s, e (0,s)=(0,s)) : parkerPermutationCorrection e 0=0 :=
  congrArg Prod.snd (hfix 0)

/-- A multiplicative loop permutation fixing the central signs is determined
by its induced code map and its correcting function on zero-sign representatives. -/
theorem parkerPermutation_normal_form (e : Equiv.Perm ParkerLoop)
    (g : golay ≃ₗ[Bit] golay)
    (hmul : ∀ x y, e (parkerLoopMultiply x y)=parkerLoopMultiply (e x) (e y))
    (hfix : ∀ s, e (0,s)=(0,s)) (hcode : ∀ x, (e x).1=g x.1)
    (x : ParkerLoop) : e x=(g x.1,x.2+parkerPermutationCorrection e x.1) := by
  have hx : parkerLoopMultiply (0,x.2) (x.1,0)=x := by
    apply Prod.ext <;> simp [parkerLoopMultiply,parkerMultiply]
  rw [← hx,hmul,hfix]
  apply Prod.ext
  · change 0+(e (x.1,0)).1=g (parkerLoopMultiply (0,x.2) (x.1,0)).1
    rw [hcode]
    simp [parkerLoopMultiply,parkerMultiply]
  · change x.2+(e (x.1,0)).2+parkerGolayFactorSet 0 (e (x.1,0)).1 =
      (parkerLoopMultiply (0,x.2) (x.1,0)).2+
        parkerPermutationCorrection e (parkerLoopMultiply (0,x.2) (x.1,0)).1
    rw [hx]
    simp [parkerPermutationCorrection]

/-- The sign function of every actual standard loop automorphism satisfies
the exact factor-set correction equation. -/
theorem parkerPermutationCorrection_equation (e : Equiv.Perm ParkerLoop)
    (g : golay ≃ₗ[Bit] golay)
    (hmul : ∀ x y, e (parkerLoopMultiply x y)=parkerLoopMultiply (e x) (e y))
    (hfix : ∀ s, e (0,s)=(0,s)) (hcode : ∀ x, (e x).1=g x.1) (a b : golay) :
    parkerPermutationCorrection e (a+b)+parkerPermutationCorrection e a+
      parkerPermutationCorrection e b=
        parkerGolayFactorSet (g a) (g b)+parkerGolayFactorSet a b := by
  have h := hmul (a,0) (b,0)
  rw [parkerPermutation_normal_form e g hmul hfix hcode,
    parkerPermutation_normal_form e g hmul hfix hcode,
    parkerPermutation_normal_form e g hmul hfix hcode] at h
  have he := congrArg Prod.snd h
  change (0+0+parkerGolayFactorSet a b)+parkerPermutationCorrection e (a+b)=
    (0+parkerPermutationCorrection e a)+(0+parkerPermutationCorrection e b)+
      parkerGolayFactorSet (g a) (g b) at he
  simp only [zero_add] at he
  have hh := congrArg (fun z => z+parkerGolayFactorSet a b+
    parkerPermutationCorrection e a+parkerPermutationCorrection e b) he
  convert hh using 1 <;> ring_nf <;>
    simp only [show (2 : Bit)=0 from rfl,mul_zero,add_zero]

end Sporadic.Monster.Construction.TrialitySpin
