module

public import Theory.SpecificGroups.PSL3Three.MaximalSubgroups
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Data.SetLike.Fintype

/-!
# Solvability of proper subgroups of PSL₃(3)

Every proper subgroup lies in a maximal proper subgroup because PSL₃(3) is
finite. The certified maximal-subgroup classification and the independent
solvability proofs in `MaximalSubgroups` show that this overgroup is solvable;
solvability then pulls back along the subgroup inclusion.

Source: the PSL₃(3) specialization of GLS III, Theorem 6.5.3, in
`refs/KGroup/GLS3/chapter6.tex`. This is the proper-subgroup ingredient in
the minimal simplicity of PSL₃(3).
-/

namespace Matrix.PSL3Three

/-- Every proper subgroup of PSL₃(3) is solvable. -/
public theorem isSolvable_of_ne_top (H : Subgroup PSL) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  obtain ⟨M, hM, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  let := maximal_isSolvable M hM
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHM)

/-- Strict-inclusion form of solvability of proper subgroups of PSL₃(3). -/
public theorem isSolvable_of_lt (H : Subgroup PSL) (hH : H < ⊤) :
    Group.IsSolvable H :=
  isSolvable_of_ne_top H (ne_of_lt hH)

end Matrix.PSL3Three
