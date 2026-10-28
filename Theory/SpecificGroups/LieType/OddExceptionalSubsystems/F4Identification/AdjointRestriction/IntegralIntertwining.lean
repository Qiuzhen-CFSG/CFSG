module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.IntegralIntertwining.Operators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.IntegralIntertwining.DividedPowers

/-!
# From integral Geck operators to the folded adjoint curve identity

The first-order E6 operator is the sum on each of the two orthogonal pairs,
with single operators on the other two nodes. The paired operators commute,
as follows by taking degree two in the proved commutation of their curves.
The integral factorial and binomial identities then supply all coefficients
of the product curve, including degrees four through six.

This proves the complete higher-degree reduction and its specialization to
literal column actions. The eight first-order equalities on `latticeMatrix`
remain explicit hypotheses; this module does not yet assert their proof or
the unconditional folded adjoint restriction. No division is performed in the
coefficient ring, so the reduction includes characteristic three and preserves
both signs and the original parameter.

Sources: integral Geck divided powers; GLS3 §§2.2--2.6; the F4 subgroup used
in Aschbacher--Smith A.2.17, printed p.39.
-/

public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup RootPairing.IntegralGeckConstruction
open RootPairing.SimpleGeckGroup.IntegralCubicFamily.Intertwining
open Matrix
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : TwistedE6.Pairing.IsIrreducible := TheoremDRootNormalizer.pairing_irreducible

private theorem source_factorial (s : Bool) (i : Fin 4) (k : ℕ) :
    sourceOperator s i ^ k = k.factorial •
      (simpleFamily (b := typeF4RootPairing_base)).dividedPower (s, sourceIndex i) k := by
  cases s
  · simpa only [sourceOperator, simpleFamily, fDividedPower_one] using
      fMatrix_pow_eq_factorial_smul (sourceIndex i) k
  · exact eMatrix_pow_eq_factorial_smul (sourceIndex i) k

private theorem target_factorial (s : Bool) (i : Fin 6) (k : ℕ) :
    targetOperator s i ^ k = k.factorial •
      (simpleFamily (b := TwistedE6.Base)).dividedPower (s, simpleIndex i) k := by
  cases s
  · simpa only [targetOperator, simpleFamily, fDividedPower_one] using
      fMatrix_pow_eq_factorial_smul (simpleIndex i) k
  · exact eMatrix_pow_eq_factorial_smul (simpleIndex i) k

/-- Orthogonal signed E6 simple operators commute over ℤ. -/
theorem targetOperator_commute (s : Bool) (i j : Fin 6)
    (hij : i ≠ j) (hc : typeE6CartanMatrix j i = 0) :
    Commute (targetOperator s i) (targetOperator s j) := by
  have hn : simpleIndex i ≠ simpleIndex j := fun h =>
    hij (typeE6RootPairing_baseEquiv.injective h)
  have hz : TwistedE6.Base.cartanMatrix (simpleIndex j) (simpleIndex i) = 0 :=
    (typeE6RootPairing_base_cartan_apply j i).trans hc
  apply commute_first_of_curves (simpleFamily (b := TwistedE6.Base))
    (s, simpleIndex i) (s, simpleIndex j)
  · simpa using (target_factorial s i 0).symm
  · simpa using (target_factorial s j 0).symm
  · cases s
    · exact congrArg (fun g : Carrier TwistedE6.Base (Polynomial ℤ) => g.val.val)
        (commute_negative_negative_of_cartan_eq_zero
          (simpleIndex i) (simpleIndex j) hn hz Polynomial.X Polynomial.X).eq
    · exact congrArg (fun g : Carrier TwistedE6.Base (Polynomial ℤ) => g.val.val)
        (commute_positive_positive_of_cartan_eq_zero
          (simpleIndex i) (simpleIndex j) hn hz Polynomial.X Polynomial.X).eq

/-- A first-order comparison gives the entire integral polynomial identity,
including every coefficient of the paired products. -/
theorem integral_polynomial_intertwines_of_operator (s : Bool) (i : Fin 4)
    (h : foldedOperator s i * latticeMatrix = latticeMatrix * sourceOperator s i) :
    foldedCurve (Polynomial ℤ) s i Polynomial.X * matrix (Polynomial ℤ) =
      matrix (Polynomial ℤ) * sourceCurve (Polynomial ℤ) s i Polynomial.X := by
  fin_cases i
  · change targetCurve _ s 3 _ * matrix _ = _
    apply curve_intertwines (simpleFamily (b := TwistedE6.Base))
      (simpleFamily (b := typeF4RootPairing_base)) (s, simpleIndex 3)
      (s, sourceIndex 0) latticeMatrix (target_factorial s 3) (source_factorial s 0)
    exact h
  · change targetCurve _ s 2 _ * matrix _ = _
    apply curve_intertwines (simpleFamily (b := TwistedE6.Base))
      (simpleFamily (b := typeF4RootPairing_base)) (s, simpleIndex 2)
      (s, sourceIndex 1) latticeMatrix (target_factorial s 2) (source_factorial s 1)
    exact h
  · change (targetCurve _ s 1 _ * targetCurve _ s 4 _) * matrix _ = _
    apply curve_product_intertwines (simpleFamily (b := TwistedE6.Base))
      (simpleFamily (b := typeF4RootPairing_base)) (s, simpleIndex 1)
      (s, simpleIndex 4) (s, sourceIndex 2) latticeMatrix
      (target_factorial s 1) (target_factorial s 4) (source_factorial s 2)
      (targetOperator_commute s 1 4 (by decide) (by decide))
    exact h
  · change (targetCurve _ s 0 _ * targetCurve _ s 5 _) * matrix _ = _
    apply curve_product_intertwines (simpleFamily (b := TwistedE6.Base))
      (simpleFamily (b := typeF4RootPairing_base)) (s, simpleIndex 0)
      (s, simpleIndex 5) (s, sourceIndex 3) latticeMatrix
      (target_factorial s 0) (target_factorial s 5) (source_factorial s 3)
      (targetOperator_commute s 0 5 (by decide) (by decide))
    exact h

/-- Specialize the integral reduction to any commutative coefficient ring. -/
theorem curve_intertwines_of_operators (R : Type*) [CommRing R]
    (h : ∀ s i, foldedOperator s i * latticeMatrix = latticeMatrix * sourceOperator s i)
    (s : Bool) (i : Fin 4) (t : R) :
    foldedCurve R s i t * matrix R = matrix R * sourceCurve R s i t :=
  curve_intertwines_of_integral_polynomial R
    (fun s i => integral_polynomial_intertwines_of_operator s i (h s i)) s i t

/-- The reduction acts on the literal generator columns with the original parameter. -/
theorem simple_mulVec_intertwines_of_operators (F : Type*) [Field F]
    (h : ∀ s i, foldedOperator s i * latticeMatrix = latticeMatrix * sourceOperator s i)
    (s : Bool) (i : Fin 4) (t : F) (x : SourceIndex → F) :
    (f4Simple F s i t).val.val.val *ᵥ linearMap F x =
      linearMap F ((coverSimple F s i t).val.val *ᵥ x) :=
  simple_mulVec_intertwines_of_integral_polynomial F
    (fun s i => integral_polynomial_intertwines_of_operator s i (h s i)) s i t x

end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
