module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData

/-!
# The complete numerical system for Janko's small degrees

This interface records integer coordinates of every irreducible, together with
orthogonality, restriction, and Suzuki identities. It contains no conclusion
about the minimum degree or the number of degree-21 rows. The principal row is
included explicitly, so rows outside the exceptional supports remain covered.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
Sections 6--7, especially the assertions on p.16.
-/

open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
open CharacterOrder

/-- The finite arithmetic data obtained from the complete irreducible family.
The five columns are the actual exceptional scalar products. -/
public structure DegreeSystem (J : Type*) [Fintype J] where
  principal : J
  degree : J → ℕ
  coefficient : Fin 5 → J → ℤ
  principal_degree : degree principal = 1
  principal_coefficient : ∀ i, coefficient i principal = exceptionalCoefficients i 0
  positive : ∀ j, 0 < degree j
  divides : ∀ j, degree j ∣ 443520
  unit : ∀ i j, coefficient i j = 0 ∨ coefficient i j = 1 ∨ coefficient i j = -1
  restriction : ∀ j, (128 : ℤ) ∣ (degree j : ℤ) + 153 * coefficient 0 j -
    202 * coefficient 1 j + 127 * coefficient 2 j + 280 * coefficient 3 j +
      45 * coefficient 4 j
  fixed_nonnegative : ∀ j, 0 ≤ (degree j : ℤ) +
    15 * columnValue (fun i => coefficient i j) 0
  faithful : ∀ j, j ≠ principal → columnValue (fun i => coefficient i j) 0 < (degree j : ℤ)
  sum_squares : ∑ j, degree j ^ 2 = 443520
  gram : ∀ i l, ∑ j, coefficient i j * coefficient l j = exceptionalGram i l
  degree_zero : ∀ i, ∑ j, coefficient i j * (degree j : ℤ) = 0
  suzuki : ∀ i, (443520 : ℚ) / 147456 *
    ∑ j, (coefficient i j : ℚ) * (columnValue (fun l => coefficient l j) 0 : ℚ)^2 /
      degree j = pairingConstants i

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
