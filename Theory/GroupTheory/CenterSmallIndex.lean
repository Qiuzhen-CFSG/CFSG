module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Index

/-!
# Central subgroups of index at most four

In a finite noncommutative group, a central subgroup of index at most four
is the entire center, and its index is exactly four. Indeed, a center quotient
of order one, two, or three is cyclic; the cyclic-center-quotient criterion
would then force the group to be commutative. Index monotonicity gives index
four, and strict index monotonicity rules out a larger center.

This elementary finite-group argument supplies the center-kernel identification
needed in the characteristic-two case of Stellmacher, *Pushing up*,
Arch. Math. 46 (1986), proof of (3.3), assertion (6) to (f), p.15. It applies
to the finite subgroup `U`, without requiring its ambient amalgam to be finite.
-/

namespace Subgroup

private theorem four_le_center_index {G : Type*} [Group G] [Finite G]
    (hnoncomm : _root_.commutator G ≠ ⊥) : 4 ≤ (center G).index := by
  by_contra h
  have hpos : (center G).index ≠ 0 := index_ne_zero_of_finite
  have hsmall : (center G).index = 1 ∨ (center G).index = 2 ∨
      (center G).index = 3 := by omega
  rcases hsmall with hcard | hcard | hcard
  · exact hnoncomm ((commutator_eq_bot_iff_center_eq_top G).mpr (index_eq_one.mp hcard))
  · have : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card hcard
    exact hnoncomm ((commutator_eq_bot_iff G).mpr
      (isMulCommutative_of_isCyclic_quotient_center_self G))
  · have : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card hcard
    exact hnoncomm ((commutator_eq_bot_iff G).mpr
      (isMulCommutative_of_isCyclic_quotient_center_self G))

/-- A central subgroup of index at most four in a finite noncommutative group
is the center and has index four. -/
public theorem center_eq_and_index_four_of_central_small_index
    {G : Type*} [Group G] [Finite G] (Z : Subgroup G)
    (hZ : Z ≤ center G) (hindex : Z.index ≤ 4) (hnoncomm : _root_.commutator G ≠ ⊥) :
    center G = Z ∧ Z.index = 4 := by
  have hcenter := four_le_center_index hnoncomm
  have hle := index_antitone hZ
  have hfour : Z.index = 4 := by omega
  refine ⟨?_, hfour⟩
  by_contra hne
  have hstrict : Z < center G := lt_of_le_of_ne hZ (Ne.symm hne)
  have := index_strictAnti hstrict
  omega

end Subgroup
