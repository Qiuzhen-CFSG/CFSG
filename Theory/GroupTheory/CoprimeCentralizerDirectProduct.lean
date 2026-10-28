module

public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Disjoint fixed and displacement subgroups for coprime conjugation

For a finite abelian subgroup V normalized by a subgroup of coprime order,
the fixed subgroup and the displacement subgroup are disjoint. Transport the
coprime-action complement theorem through the inclusion V → G, preserving
the actual ambient commutator and centralizer. Together with
`eq_commutator_sup_centralizer_of_solvable_coprime`, this gives their internal
direct product decomposition of V.

This is the coprime splitting used in Aschbacher–Smith, E.6.8(1), printed p.247.
-/

public section

namespace Subgroup
open scoped IsMulCommutative

/-- Coprime conjugation on an abelian subgroup has disjoint displacement
and fixed subgroups, as subgroups of the original ambient group. -/
theorem commutator_disjoint_centralizer_of_coprime
    {G : Type*} [Group G] [Finite G] (V A : Subgroup G)
    [IsMulCommutative V] (hn : A ≤ normalizer (V : Set G))
    (hc : Nat.Coprime (Nat.card A) (Nat.card V)) :
    Disjoint ⁅V, A⁆ (V ⊓ centralizer (A : Set G)) := by
  let _ : Normalizes A V := ⟨hn⟩
  have hs : Group.IsSolvable V := Group.isSolvable_of_comm fun x y => mul_comm x y
  have hd := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := A) hs hc inferInstance
  have hm := Subgroup.disjoint_map V.subtype_injective hd.symm.disjoint
  rw [commutatorAction_subgroup_conj_map_eq_commutator V A hn,
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn V A hn,
    map_subgroupOf_eq_of_le (show subgroupCentralizerIn V A ≤ V from inf_le_left)] at hm
  exact hm

end Subgroup
