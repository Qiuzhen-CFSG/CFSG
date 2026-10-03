module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates
public import Theory.GroupTheory.PGroup.FrattiniProfileAutomorphisms

/-!
# Data and properness for the two-automorphism small even cases

This narrow layer records the finite index set and the parity argument showing
that every selected root-generated subgroup is proper in the Sylow model.  The
automorphism certificates live above this layer.
-/

namespace ReeTwo.SylowModel

/-- Indices of the 34 representatives with diagnostic two-group automorphism
groups. -/
@[expose] public def smallEvenTwoAutIndices : Finset (Fin 59) :=
  {0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
   18, 19, 20, 21, 22, 23, 24, 25, 26, 29, 35, 37, 38, 40, 43, 46, 51}

/-- All listed candidates lie in the parity kernel. -/
public theorem smallEvenCandidate_le_character_ker (i : Fin 59) :
    smallEvenCandidate i ≤ character.ker := by
  have hs : character rootOne ^ 2 = 1 := by decide +kernel
  fin_cases i <;>
    simp only [smallEvenCandidate, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff,
      SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_pow, character_root,
      hs, mul_one, and_self]

/-- Parity separates every listed representative from the whole Sylow model. -/
public theorem smallEvenCandidate_ne_top (i : Fin 59) : smallEvenCandidate i ≠ ⊤ := by
  intro h
  have hr : rootOne ∈ character.ker :=
    smallEvenCandidate_le_character_ker i (h.symm ▸ Subgroup.mem_top rootOne)
  exact character_rootOne_ne_one (MonoidHom.mem_ker.mp hr)

end ReeTwo.SylowModel
