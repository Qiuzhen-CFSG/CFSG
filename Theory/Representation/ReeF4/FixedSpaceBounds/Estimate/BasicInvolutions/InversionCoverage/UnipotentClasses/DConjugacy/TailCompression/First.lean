module
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Reduction
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.TailCompression.Collection
/-!
# First-curve conjugation on the Ree elementary tail

Specialize the checked split-root exchanges to field parameters and their
half-Frobenius images. This gives the full action of x₁(t)⁻¹ on
x₆(a)x₄(b)y₅(c)y₇(d)y₃(e), including every central correction.
`TailCompression` uses this action twice to obtain the central first-curve
action, and then eliminates the two unwanted tail coordinates.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
The consumer is the involution-class calculation in Guralnick–Malle,
Classification of 2F-modules II, Lemma 8.8, internal p.57.
-/

@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.TailCompression
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open NormalizedRootCentralizers.CenterExponent
open ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open Theory.AlgebraicGroup.StandardRootSystem

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong i), halfFrobenius]

private theorem word_first (m : ℕ) (t : CoefficientField m) :
    rootWord m 0 t = X m 0 t * X m 1 (halfFrobenius m t) *
      X m 2 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem tail_coe (m : ℕ) (a b c d e : CoefficientField m) :
    toSplitGroup m (tailElement m ![a,b,c,d,e]) =
      X m 16 a * X m 17 (halfFrobenius m a) *
      (X m 10 b * X m 11 (halfFrobenius m b)) *
      (X m 15 c * X m 14 (halfFrobenius m c)) *
      (X m 21 d * X m 20 (halfFrobenius m d)) *
      (X m 9 e * X m 8 (halfFrobenius m e)) := by
  simp only [tailElement_eq_product, map_mul, mainElement_coe, centralElement_coe,
    Matrix.cons_val_zero, Matrix.cons_val]
  simp only [rootWord, centralWord, fieldEnd_half]
  change (_ * _ * 1) * (_ * _ * 1) * (_ * _) * (_ * _) * (_ * _) = _
  simp only [mul_one]
  rfl

attribute [local irreducible] MatrixRelations.LongCommutators.X
/-- The full first-curve action on the elementary five-coordinate tail. -/
theorem first_conj_tail (m : ℕ) (t a b c d e : CoefficientField m) :
    (mainElement m 0 t)⁻¹ * tailElement m ![a,b,c,d,e] * mainElement m 0 t =
      tailElement m ![a+t*d, b+(a+t*d)*titsEnd m t,
        c+t*titsEnd m a, d, e+t*b+t^2*titsEnd m t*d] := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, mainElement_coe, tail_coe, word_first, mul_inv_rev, xi]
  have h := collect_first_tail m ![a, halfFrobenius m a, b, halfFrobenius m b,
    c, halfFrobenius m c, d, halfFrobenius m d, e, halfFrobenius m e,
    t, halfFrobenius m t, 0,0,0,0,0,0,0,0,0,0,0,0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val, mul_one, mul_assoc] at h
  simp only [mul_assoc]
  rw [h]
  rw [(xc m 15 14 (by norm_num [V, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]) _ _).left_comm,
    (xc m 21 20 (by norm_num [V, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]) _ _).left_comm,
    (xc m 9 8 (by norm_num [V, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]) _ _).eq]
  simp only [map_add, map_mul, map_pow, halfFrobenius_titsEnd]
  simp only [← halfFrobenius_sq]
  repeat' apply congrArg₂ (· * ·)
  all_goals congr 1 <;> ring

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.TailCompression
