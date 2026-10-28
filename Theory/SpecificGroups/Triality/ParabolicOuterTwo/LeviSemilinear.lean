module

public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.LeviSemilinear.Coefficients
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.LeviSemilinear.Parabolic
public import Theory.SpecificGroups.Triality.StandardTwoRank.FourSemilinear.HighestRoot

/-!
# Semilinear detection on the genuine triality local quotients

The original arms quotient sees the entire coefficient automorphism of GF(q³).
The central quotient sees its restriction to the actual q-Frobenius fixed field,
transported through the original GF(q) identification. If that restriction is
trivial, the coefficient is an automorphism of a cubic extension, so its cube
is one. The possible order-three kernel is retained.

Conjugation by every element of the actual parabolic acts internally on the
local two-core quotient. Consequently the same coefficient detection applies
after multiplying by any such parabolic conjugation. These corollaries use the
literal `localQuotientAction`, `parabolicInner`, and `coefficientStabilizer` maps
needed for the outer-two local argument; every extra action premise of the
intermediate equivariance and torus calculations is discharged.

Sources: Aschbacher–Smith F.1.12, printed pp.263–264, `refs/quasithin.pdf`;
GLS3 §§2.5–2.6, especially the cubic-field convention in 2.5.12(d),
`refs/KGroup/GLS3/chapter2.tex`. The results hold at all positive binary
exponents, in particular the n ≥ 2 range used in the source assembly.
-/

public section
noncomputable section
namespace Triality.Standard.ParabolicOuterTwo
open Parabolics OuterOdd

theorem coefficient_cube_eq_one_of_fixes_fixedField (P : Parameters) (e : CoefficientAut P)
    (h : ∀ t : fixedField P, e t.val = t.val) : e ^ 3 = 1 := by
  let f : ExtensionField P ≃ₐ[fixedField P] ExtensionField P :=
    AlgEquiv.ofRingEquiv (f := e) h
  have hc : Nat.card (ExtensionField P ≃ₐ[fixedField P] ExtensionField P) = 3 := by
    rw [IsGalois.card_aut_eq_finrank, TwoRank.FourSemilinear.extensionField_finrank_fixedField P]
  have hf : f ^ 3 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := f))
  exact congrArg AlgEquiv.toRingEquiv hf

theorem coefficient_cube_eq_one_of_central_inner (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P)
    (h : coefficientLocalTwoQuotient P e .central ∈
      MulAut.innerSubgroup (LocalTwoQuotient P .central)) : e ^ 3 = 1 :=
  coefficient_cube_eq_one_of_fixes_fixedField P e
    (coefficient_fixes_fixedField_of_central_inner P hp e h)

private theorem coefficient_inner_of_parabolic_mul_inner
    (P : Parameters) (hp : P.prime = 2) (a : Node)
    (g : parabolic P a) (e : CoefficientAut P)
    (h : localQuotientAction P a (parabolicInner P a g * coefficientStabilizer P a e) ∈
      MulAut.innerSubgroup (LocalTwoQuotient P a)) :
    coefficientLocalTwoQuotient P e a ∈ MulAut.innerSubgroup (LocalTwoQuotient P a) := by
  rw [map_mul, localQuotientAction_coefficient] at h
  exact ((MulAut.innerSubgroup (LocalTwoQuotient P a)).mul_mem_cancel_left
    (localQuotientAction_parabolicInner P hp a g)).mp h

theorem coefficient_eq_one_of_parabolic_mul_arms_inner
    (P : Parameters) (hp : P.prime = 2) (g : parabolic P .arms) (e : CoefficientAut P)
    (h : localQuotientAction P .arms
      (parabolicInner P .arms g * coefficientStabilizer P .arms e) ∈
        MulAut.innerSubgroup (LocalTwoQuotient P .arms)) : e = 1 :=
  coefficient_eq_one_of_arms_inner P hp e
    (coefficient_inner_of_parabolic_mul_inner P hp .arms g e h)

theorem coefficient_fixes_fixedField_of_parabolic_mul_central_inner
    (P : Parameters) (hp : P.prime = 2) (g : parabolic P .central) (e : CoefficientAut P)
    (h : localQuotientAction P .central
      (parabolicInner P .central g * coefficientStabilizer P .central e) ∈
        MulAut.innerSubgroup (LocalTwoQuotient P .central)) :
    ∀ t : fixedField P, e t.val = t.val :=
  coefficient_fixes_fixedField_of_central_inner P hp e
    (coefficient_inner_of_parabolic_mul_inner P hp .central g e h)

theorem coefficient_cube_eq_one_of_parabolic_mul_central_inner
    (P : Parameters) (hp : P.prime = 2) (g : parabolic P .central) (e : CoefficientAut P)
    (h : localQuotientAction P .central
      (parabolicInner P .central g * coefficientStabilizer P .central e) ∈
        MulAut.innerSubgroup (LocalTwoQuotient P .central)) : e ^ 3 = 1 :=
  coefficient_cube_eq_one_of_fixes_fixedField P e
    (coefficient_fixes_fixedField_of_parabolic_mul_central_inner P hp g e h)

end Triality.Standard.ParabolicOuterTwo
