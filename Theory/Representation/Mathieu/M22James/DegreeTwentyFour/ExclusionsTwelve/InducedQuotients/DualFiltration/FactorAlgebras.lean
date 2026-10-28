module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.FactorAlgebras.FortyFive
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.FactorAlgebras.Six
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.FactorAlgebras.Fifteen

/-!
# The three full matrix algebras of the dual induced point-module factors

For each published generator pair, a checked polynomial supplies a rank-one
operator. Its checked column and row orbits both span, so the algebra contains
every matrix unit. This proves fullness for the literal matrices of dimensions
45, 6 and 15, without any irreducibility or characteristic-polynomial premise.

The quotient-action identifications belong to the independent field-flag
construction, which consumes `factorMatrix_algebra_eq_top`.
Source context: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, pp.15–16 and Theorem 6.6/Table 6.7.
-/

public section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration

/-- Every subalgebra containing the two literal factor matrices is the full algebra. -/
theorem factorMatrix_algebra_eq_top (k : Fin 3)
    (Q : Subalgebra F (Matrix (Fin (factorDimension k)) (Fin (factorDimension k)) F))
    (hA : factorMatrix k 0 ∈ Q) (hB : factorMatrix k 1 ∈ Q) : Q = ⊤ := by
  fin_cases k
  · exact FactorAlgebras.FortyFive.algebra_eq_top Q hA hB
  · exact FactorAlgebras.Six.algebra_eq_top Q hA hB
  · exact FactorAlgebras.Fifteen.algebra_eq_top Q hA hB

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration
