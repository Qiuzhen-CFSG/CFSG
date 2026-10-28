module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Image
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.RootColumns
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.CartanKernel
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.RootKernel

/-!
# Short F4 root operators over the Ree coefficient field

The canonical short integral root operators specialize to matrices whose image
lies in the short-coordinate subspace and whose common kernel is zero. The
Cartan-column formula discharges the premise of root-coordinate detection;
four short-root pairing rows then detect the remaining Cartan coordinates.
Thus both operator hypotheses used in the short-coordinate faithfulness
argument hold unconditionally for the actual operators in characteristic two.

The operator convention is the Weyl-transported Geck construction in
`F4IntegralChevalleyRepresentation`, following Steinberg's integral
admissible-lattice construction.
-/

public section

namespace ReeF4.WordRelations.ShortOperators

open Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix

/-- The actual short F4 root operators have trivial common kernel over every
commutative ring of characteristic two. -/
theorem rootOperator_commonKernel {K : Type*} [CommRing K] [CharP K 2]
    (v : Coordinate → K)
    (hkernel : ∀ s : typeF4Roots, IsShortRoot s →
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom K) *ᵥ v = 0) : v = 0 :=
  eq_zero_of_rootCoordinates_eq_zero v
    (root_coordinates_eq_zero_of_common_kernel
      (fun s _hs j => rootOperator_cartanColumn s j) v hkernel) hkernel

/-- Image containment for the actual short operators over each Ree field. -/
theorem coefficientField_rootOperator_image (m : ℕ) (s : typeF4Roots)
    (hs : IsShortRoot s) :
    ∀ i, ¬IsShortCoordinate i → ∀ j,
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom (CoefficientField m)) i j = 0 :=
  rootOperator_image s hs

/-- Trivial common kernel for the actual short operators over each Ree field. -/
theorem coefficientField_rootOperator_commonKernel (m : ℕ)
    (v : Coordinate → CoefficientField m)
    (hkernel : ∀ s : typeF4Roots, IsShortRoot s →
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom (CoefficientField m)) *ᵥ v = 0) : v = 0 :=
  rootOperator_commonKernel v hkernel

end ReeF4.WordRelations.ShortOperators
