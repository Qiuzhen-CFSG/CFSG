module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.Geometry

/-!
# Matrix contract for the root-sum branches

This contract asks for an equality of the actual F4 root matrices, with an
explicit finite correction word whose roots are strictly positive integral
combinations of the two inputs. It contains no subgroup factorization or
support assertion. `Geometry` proves the required support and height facts
when the two inputs belong to a Ree positive or radical support.

The equal-length and mixed-length root-sum calculations are independent
producers of this contract. Its definition asserts neither calculation.
Source: the Chevalley collection used for Aschbacher–Smith F.1.12(I)(5),
printed p.263 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics.RadicalCoordinates
open Theory.AlgebraicGroup StandardRootSystem

/-- An actual matrix exchange with correction roots in the positive cone. -/
def MatrixExchange {K : Type*} [CommRing K] (r s : F4Chevalley.Root) (a b : K) : Prop :=
  ∃ correction : List (F4Chevalley.Root × K),
    (∀ z ∈ correction, PositiveCone r s z.1) ∧
      (F4Chevalley.rootCurve r a : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) *
          (F4Chevalley.rootCurve s b).val =
        (F4Chevalley.rootCurve s b).val * (F4Chevalley.rootCurve r a).val *
          (correction.map (fun z => (F4Chevalley.rootCurve z.1 z.2).val)).prod

end ReeF4.Parabolics.RadicalCoordinates
