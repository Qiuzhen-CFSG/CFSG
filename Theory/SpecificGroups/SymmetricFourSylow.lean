module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.NormNum

/-!
# The Sylow two-subgroups of the four-point symmetric group

Every Sylow two-subgroup of `Equiv.Perm (Fin 4)` is isomorphic to the
order-eight dihedral group. The square's rotations and reflections give an
injective homomorphism into the symmetric group. Its image has order eight,
the full two-part of `4!`, and Sylow conjugacy gives the result for any
supplied Sylow subgroup.

This standard permutation-group calculation supports local recognition from
an `S₄` subgroup. The concrete square action also occurs in
`Stellmacher/SectionEleven/C2S4SylowPairGeometry.lean`; this independent
interface uses only Mathlib and has no campaign dependencies.
-/

namespace Equiv.Perm

private def squarePermutation : DihedralGroup 4 → Equiv.Perm (Fin 4)
  | .r i => finRotate 4 ^ i.val
  | .sr i => Equiv.swap 1 3 * finRotate 4 ^ i.val

set_option maxRecDepth 10000 in
private def squareEmbedding : DihedralGroup 4 →* Equiv.Perm (Fin 4) where
  toFun := squarePermutation
  map_one' := by decide
  map_mul' := by decide

set_option maxRecDepth 10000 in
private theorem squareEmbedding_injective : Function.Injective squareEmbedding := by
  decide

/-- Every Sylow two-subgroup of the symmetric group on four letters is the
dihedral group of order eight. -/
public theorem sylow_two_equiv_dihedral_four (S : Sylow 2 (Equiv.Perm (Fin 4))) :
    Nonempty (S ≃* DihedralGroup 4) := by
  let modelRange := MonoidHom.ofInjective squareEmbedding_injective
  have hcard : Nat.card squareEmbedding.range = 8 := by
    rw [← Nat.card_congr modelRange.toEquiv]
    norm_num [DihedralGroup.card]
  have hfull : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  let concrete : Sylow 2 (Equiv.Perm (Fin 4)) := Sylow.ofCard squareEmbedding.range (by
    rw [hcard, hfull]
    rw [show 24 = 2 ^ 3 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization])
  exact ⟨(S.equiv concrete).trans modelRange.symm⟩

end Equiv.Perm
