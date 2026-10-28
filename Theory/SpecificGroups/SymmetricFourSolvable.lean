module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.Solvable

/-!
# Solvability of the symmetric group on four letters

The alternating subgroup of degree four has commutator subgroup the Klein
four group, hence is solvable. The sign homomorphism has this subgroup as its
kernel, so the full symmetric group on four letters is solvable. This is the
small symmetric exceptional case in Dickson's PSL₂ subgroup classification.

Source: the standard A₄ ⋊ C₂ extension and Mathlib's Klein-four
commutator calculation.
-/

private theorem alternating_four_isSolvable :
    Group.IsSolvable (alternatingGroup (Fin 4)) := by
  refine ⟨⟨2, ?_⟩⟩
  change ⁅commutator (alternatingGroup (Fin 4)),
    commutator (alternatingGroup (Fin 4))⁆ = ⊥
  rw [← alternatingGroup.kleinFour_eq_commutator (by simp)]
  exact Subgroup.commutator_self_eq_bot_iff.mpr
    (alternatingGroup.kleinFour_isKleinFour (by simp)).isMulCommutative

/-- The alternating group on four letters is solvable. -/
public theorem alternatingGroup_fin_four_isSolvable :
    Group.IsSolvable (alternatingGroup (Fin 4)) := alternating_four_isSolvable

namespace Equiv.Perm

/-- The symmetric group on four letters is solvable. -/
public theorem isSolvable_fin_four :
    Group.IsSolvable (Equiv.Perm (Fin 4)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternating_four_isSolvable
  apply Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 4)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

end Equiv.Perm
