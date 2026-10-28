module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import Theory.Representation.BinaryPermutation.OrbitFixedSpace
public import Theory.GroupAction.AbelianPermutationOrbitBound

/-!
# Rank and equality rigidity for the full odd permutation module

The orbit formula for fixed codimension and the cardinal bound for abelian
permutation groups give the rank bound. Equality forces singleton or pair
orbits and independent swaps on the pair orbits. These results supply the
exhaustiveness argument for the full module in degrees five and seven.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.3.2, printed pp. 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.Odd

open BinaryPermutation Representation.BinaryOffender

/-- Elementary abelian subgroups cannot offend on the full odd permutation module. -/
theorem rank_le_fixedCodim_full_of_elementary {n : ℕ} (_hn : n = 5 ∨ n = 7)
    (A : Subgroup (Equiv.Perm (Fin n))) (hA : IsElementaryTwo A) :
    rank A ≤ fixedCodim (representation (Fin n)) A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  apply (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp
  rw [← hA.card_eq_two_pow_rank, fixedCodim_full_eq_card_sub_card_orbits]
  exact AbelianPermutation.card_le_two_pow_degree_sub_orbits A

/-- Equality in the full-module bound forces independent two-point orbits. -/
theorem pair_orbits_of_fixedCodim_full_eq_rank {n : ℕ} (_hn : n = 5 ∨ n = 7)
    (A : Subgroup (Equiv.Perm (Fin n))) (hA : IsElementaryTwo A)
    (heq : fixedCodim (representation (Fin n)) A = rank A) :
    (∀ x : Fin n, Nat.card (MulAction.orbit A x) ≤ 2) ∧
      (∀ x y : Fin n, y ∈ MulAction.orbit A x → Equiv.swap x y ∈ A) := by
  let _ : IsElementaryAbelian 2 A := hA.2
  apply AbelianPermutation.pair_orbits_of_card_eq A
  rw [← fixedCodim_full_eq_card_sub_card_orbits, heq]
  exact hA.card_eq_two_pow_rank

end CFSG.Quasithin.ChapterB.Offenders.Odd
