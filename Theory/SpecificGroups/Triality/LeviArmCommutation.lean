module

public import Theory.SpecificGroups.Triality.LeviRankOne
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup.Commutation
public import Theory.AlgebraicGroup.RootSystems.TypeD4Irreducible

/-!
# Commutation of the three triality arms

The vertices `0, 2, 3` of the standard D4 base are pairwise orthogonal. Applying
the integral Geck curve commutation theorems proves the three root relations
required by `ArmRootCommutation`, directly on the actual split-group generators.
No pinned SL₂ maps or Levi identifications are assumed.

This is the matrix input for the commuting subsystem factors of GLS3,
Proposition 2.6.2(a), with the root parametrizations of §2.4
(`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.Parabolics

private theorem arm_cartan_zero (i j : Fin 4)
    (hi : i ≠ 1) (hj : j ≠ 1) (hij : i ≠ j) :
    (typeDRootPairing_base 2).cartanMatrix
      (typeDRootPairing_baseEquiv 2 j) (typeDRootPairing_baseEquiv 2 i) = 0 := by
  rw [typeDRootPairing_base_cartanMatrix]
  fin_cases i <;> fin_cases j <;> first | contradiction | decide

/-- The genuine Geck curves on distinct D4 arms commute in all three sign
combinations required by the triality Levi construction. The integral proof
works in every characteristic; this signature retains the characteristic-two
hypothesis of the Levi application. -/
theorem armRootCommutation (P : Parameters) (_hp : P.prime = 2) :
    ArmRootCommutation P := by
  let := typeD4RootPairing_isIrreducible
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj hij t u
    exact RootPairing.SimpleGeckGroup.commute_positive_positive_of_cartan_eq_zero
      _ _ (fun h => hij ((typeDRootPairing_baseEquiv 2).injective h))
      (arm_cartan_zero i j hi hj hij) t u
  · intro i j _hi _hj hij t u
    exact RootPairing.SimpleGeckGroup.commute_positive_negative
      _ _ (fun h => hij ((typeDRootPairing_baseEquiv 2).injective h)) t u
  · intro i j hi hj hij t u
    exact RootPairing.SimpleGeckGroup.commute_negative_negative_of_cartan_eq_zero
      _ _ (fun h => hij ((typeDRootPairing_baseEquiv 2).injective h))
      (arm_cartan_zero i j hi hj hij) t u

end Triality.Standard.Parabolics
