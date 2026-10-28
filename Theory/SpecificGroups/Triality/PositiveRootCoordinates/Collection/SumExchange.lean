module
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.Relations
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.SimpleCoefficients
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.CanonicalCoefficients
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.PolynomialExchange

/-!
# Sum exchanges for the canonical binary D₄ curves

Reducing integral divided powers modulo two commutes with extension to every
characteristic-two coefficient ring. Together with the two-variable polynomial
identity, this yields the requested exchange relation in the actual split
Geck group, for every positive binary parameter, including exponent one.

The full coefficient comparison follows the chosen integral Tits route, and
the polynomial identity covers every positive root-sum pair on all 28 lattice
coordinates. The theorem `sumExchange_binary` combines these two proofs with
scalar extension and reindexing to establish the exchange in the actual group.

Source: GLS3 2.3.6–7 and §§2.4–2.6
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open RootPairing.IntegralGeckConstruction
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b
namespace Triality.Standard.PositiveCoordinates
open SumExchangeData

local instance (n : ℕ) (hn : 0 < n) : CharP (ExtensionField (binaryParameters n hn)) 2 :=
  inferInstanceAs (CharP (ExtensionField (binaryParameters n hn)) (binaryParameters n hn).prime)

private theorem cast_mod_two {F : Type*} [CommRing F] [CharP F 2] (z : ℤ) :
    scalarMap F (z : ZMod 2) = (z : F) := by
  exact map_intCast _ _

/-- Extend the integral coefficient comparison from the prime field to any
commutative ring of characteristic two. -/
theorem rootCurve_matrix_of_coefficients {F : Type*} [CommRing F] [CharP F 2]
    (h : ∀ (i : Fin 12) (d : Fin 4),
      canonicalCoefficient i d = dividedCoefficient (positiveIndex i) d)
    (i : Fin 12) (t : F) :
    Matrix.reindexRingEquiv F latticeEnumeration.symm
      (rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) (rootIndex i) t).val = matrixCurve (positiveIndex i) t := by
  have hc (d : Fin 4) :
      Matrix.reindexRingEquiv F latticeEnumeration.symm
        (specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2) (rootIndex i) d)) =
      (scalarMap F).mapMatrix
        (dividedCoefficient (positiveIndex i) d) := by
    rw [← h i d]
    ext r s
    exact (cast_mod_two _).symm
  change Matrix.reindexRingEquiv _ latticeEnumeration.symm
    (1 + t • specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2) (rootIndex i) 1) +
      t ^ 2 • specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2) (rootIndex i) 2) +
      t ^ 3 • specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2) (rootIndex i) 3)) = _
  have hr (s : F) (M : Matrix LatticeIndex LatticeIndex
      F) :
      Matrix.reindexRingEquiv _ latticeEnumeration.symm (s • M) =
        s • Matrix.reindexRingEquiv _ latticeEnumeration.symm M := rfl
  simp only [map_add, map_one, hr]
  rw [hc ⟨1, by decide⟩, hc ⟨2, by decide⟩, hc ⟨3, by decide⟩]
  simp [dividedCoefficient, matrixCurve]

/-- Conditional final assembly from the full canonical coefficient comparison
and the independent finite polynomial matrix identity. -/
theorem sumExchange_of_binary_coefficients (n : ℕ) (hn : 0 < n)
    (hcoeff : ∀ (i : Fin 12) (d : Fin 4),
      canonicalCoefficient i d = dividedCoefficient (positiveIndex i) d)
    (hexchange : ∀ (i j k : Fin 12),
      rootCoords (positiveIndex k) = rootCoords (positiveIndex i) + rootCoords (positiveIndex j) →
      polynomialCurve (positiveIndex i) 0 * polynomialCurve (positiveIndex j) 1 =
        polynomialCurve (positiveIndex j) 1 * polynomialCurve (positiveIndex i) 0 *
          matrixCurve (positiveIndex k) ((MvPolynomial.X 0 : PolynomialRing) * MvPolynomial.X 1)) :
    SumExchange (binaryParameters n hn) := by
  intro i j k h a b
  apply Subtype.ext
  apply Units.ext
  apply (Matrix.reindexRingEquiv (ExtensionField (binaryParameters n hn))
    latticeEnumeration.symm).injective
  change Matrix.reindexRingEquiv _ latticeEnumeration.symm
    ((curve (binaryParameters n hn) i a).val.val * (curve (binaryParameters n hn) j b).val.val) =
    Matrix.reindexRingEquiv _ latticeEnumeration.symm
      ((curve (binaryParameters n hn) j b).val.val * (curve (binaryParameters n hn) i a).val.val *
        (curve (binaryParameters n hn) k (a * b)).val.val)
  simp only [map_mul]
  rw [show (curve (binaryParameters n hn) i a).val.val =
      (rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) (rootIndex i) a).val from rfl]
  simp only [curve, rootCurve_matrix_of_coefficients hcoeff]
  exact matrix_exchange_of_polynomial i j k (hexchange i j k ((root_sum_iff i j k).mp h)) a b

/-- Every positive root-sum pair satisfies the exchange identity on the actual
canonical integral Geck curves, for all parameters and every positive binary
exponent, including one. -/
theorem sumExchange_binary (n : ℕ) (hn : 0 < n) :
    SumExchange (binaryParameters n hn) :=
  sumExchange_of_binary_coefficients n hn canonicalCoefficient_eq polynomial_exchange

end Triality.Standard.PositiveCoordinates
