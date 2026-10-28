module
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.SpecificGroups.GL2.DeterminantTwoPower
public import Mathlib.GroupTheory.PGroup

/-!
# Two-primary centralizers in determinant levels

Over any field, the centralizer of a noncommutative subgroup of GL2,
intersected with the determinant two-power level m, is a two-group.
The assertion requires neither finiteness nor odd characteristic.

The matrix centralizer theorem makes every element scalar. The determinant
of a scalar is its square, so the level condition forces its 2^(m+1)-st
power to be one. The same exponent then annihilates the scalar matrix.

This supplies the centralizer bound in the linear and unitary model steps
of Alperin--Brauer--Gorenstein II.3 Proposition 3, article pages 27--28.
It is used with an actual noncommutative Sylow subgroup to identify the
odd complement as the odd core of its centralizer.
-/

namespace Matrix.GeneralLinearGroup

public theorem isPGroup_centralizer_inf_determinantTwoPower
    {F : Type*} [Field F]
    (U : Subgroup (GL (Fin 2) F)) (hU : ¬ IsMulCommutative U) (m : ℕ) :
    IsPGroup 2 (Subgroup.centralizer (U : Set (GL (Fin 2) F)) ⊓
      determinantTwoPower F m : Subgroup (GL (Fin 2) F)) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro A
  obtain ⟨u, hu⟩ := centralizer_le_scalar_of_noncommutative U hU A.property.1
  have hd := A.property.2
  change A.val ∈ determinantTwoPower F m at hd
  rw [mem_determinantTwoPower, ← hu, det_scalar, Fintype.card_fin] at hd
  have hp : u ^ (2 ^ (m + 1)) = 1 := by
    rw [pow_succ', pow_mul]
    exact hd
  refine ⟨m + 1, Subtype.ext ?_⟩
  change A.val ^ (2 ^ (m + 1)) = 1
  rw [← hu, ← map_pow, hp, map_one]

end Matrix.GeneralLinearGroup
