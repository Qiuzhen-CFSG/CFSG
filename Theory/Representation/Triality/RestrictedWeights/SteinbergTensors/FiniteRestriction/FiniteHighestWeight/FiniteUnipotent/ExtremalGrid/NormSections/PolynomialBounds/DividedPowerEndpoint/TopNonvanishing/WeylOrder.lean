module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.Operators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.ReflectionWords

/-!
# The D4 root order along the opposition word

The reduced word `[0,1,2,3]^3` gives positive roots at positions
`[0,4,7,9,3,11,6,5,10,8,1,2]` of the supplied twelve-root enumeration.
An operator product applies the last entry first, so the endpoint product
uses the reverse of this order. The coordinate theorem below relates this
permutation to the actual root pairing, rather than just an abstract list.

Source: the D4 Cartan matrix and the Weyl-word construction of GLS3 §1.9.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
open D4RestrictedWeight ClassBound.FixedOpposition.AmbientNormalizer
public noncomputable section

/-- Positions of the positive roots crossed by the twelve simple reflections. -/
@[expose] def convexStepOrder : Equiv.Perm (Fin 12) where
  toFun := ![0, 4, 7, 9, 3, 11, 6, 5, 10, 8, 1, 2]
  invFun := ![0, 10, 11, 4, 1, 7, 6, 2, 9, 3, 8, 5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Reverse the chronological root order because the rightmost operator acts first. -/
@[expose] def convexOperatorOrder : Equiv.Perm (Fin 12) :=
  (Fin.revPerm : Equiv.Perm (Fin 12)).trans convexStepOrder

/-- The simple root used in each step of the opposition word. -/
@[expose] def oppositionSimpleStep (i : Fin 12) : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Integral fundamental-weight coordinates of the actual supplied positive roots. -/
theorem positive_rootWeight_coordinate (S : Geometry K) (i : Fin 12) (j : Fin 4) :
    (rootWeight S (positiveCoordinateRoot S i) j : ℝ) =
      ∑ l : Fin 4, Triality.Standard.PositiveCoordinates.coefficients i l *
        typeDCartanMatrix 2 l j := by
  have hp : (rootWeight S (positiveCoordinateRoot S i) j : ℝ) =
      (typeDRootPairing 2).pairing (Triality.Standard.PositiveCoordinates.rootIndex i)
        (typeDSimpleRootIndex 2 j) := by
    simpa only [rootWeight, positiveCoordinateRoot, Equiv.apply_symm_apply,
      S.simpleRoot_index] using S.based.1 (positiveCoordinateRoot S i) (S.simpleRoot j).val
  rw [hp, ← RootPairing.root_coroot'_eq_pairing,
    Triality.Standard.PositiveCoordinates.root_expansion, map_sum]
  simp only [map_smul, RootPairing.root_coroot'_eq_pairing,
    typeDRootPairing_simpleIndex_pairing, smul_eq_mul]

private def coordinateWeightTable : Fin 12 → Weight :=
  ![![2, -1, 0, 0], ![0, -1, 2, 0], ![0, -1, 0, 2], ![-1, 2, -1, -1],
    ![1, 1, -1, -1], ![-1, 1, 1, -1], ![-1, 1, -1, 1], ![1, 0, 1, -1],
    ![-1, 0, 1, 1], ![1, 0, -1, 1], ![1, -1, 1, 1], ![0, 1, 0, 0]]

private theorem coordinateWeightTable_convex : ∀ i : Fin 12, ∀ j : Fin 4,
    coordinateWeightTable (convexStepOrder i) j =
      wordAction (typeDCartanMatrix 2 (oppositionSimpleStep i))
        (oppositionWord.take i.val).reverse j := by decide +kernel

private theorem positive_rootWeight_table (S : Geometry K) (i : Fin 12) :
    rootWeight S (positiveCoordinateRoot S i) = coordinateWeightTable i := by
  funext j
  apply Int.cast_injective (α := ℝ)
  rw [positive_rootWeight_coordinate]
  have hm : typeDCartanMatrix 2 =
      !![(2 : ℤ), -1, 0, 0; -1, 2, -1, -1; 0, -1, 2, 0; 0, -1, 0, 2] := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [typeDCartanMatrix] <;> decide
  rw [hm]
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateWeightTable, Triality.Standard.PositiveCoordinates.coefficients,
      Fin.sum_univ_succ]

/-- Each crossed actual root is the corresponding simple root reflected by
all preceding steps, in the order appropriate for left conjugation. -/
theorem convexStep_rootWeight (S : Geometry K) (i : Fin 12) :
    rootWeight S (positiveCoordinateRoot S (convexStepOrder i)) =
      wordAction (typeDCartanMatrix 2 (oppositionSimpleStep i))
        (oppositionWord.take i.val).reverse := by
  rw [positive_rootWeight_table]
  funext j
  exact coordinateWeightTable_convex i j

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
