module

public import Theory.GroupTheory.PGroup.NormalFour

/-!
# Cyclic normal subgroups when normal four-groups are absent

Every normal abelian subgroup of a finite two-group without a normal
elementary four-group is cyclic. Choosing a maximal normal abelian subgroup
therefore gives a cyclic normal self-centralizing subgroup.

This is the initial reduction for the dihedral/semidihedral alternative in
GLS, Number 2, Chapter C, Lemma 10.11. The normal-four theorem supplies the
contrapositive, without assuming a classification of two-groups.
-/

namespace IsPGroup

/-- Absence of a normal four-group forces every normal abelian subgroup
to be cyclic. -/
public theorem isCyclic_normal_abelian_of_no_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] : IsCyclic D := by
  by_contra hD
  obtain ⟨E, hEn, -, hEe, hE⟩ :=
    hP.exists_normal_four_of_normal_abelian_not_cyclic D hD
  exact hno ⟨E, hEn, hEe, hE⟩

/-- A finite two-group without a normal four-group has a cyclic normal
self-centralizing subgroup. -/
public theorem exists_cyclic_normal_selfCentralizing_of_no_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4) :
    ∃ D : Subgroup P, D.Normal ∧ IsCyclic D ∧ Subgroup.centralizer (D : Set P) = D := by
  obtain ⟨D, hDn, hDa, hDC⟩ := exists_normal_abelian_selfCentralizing hP
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  exact ⟨D, hDn, hP.isCyclic_normal_abelian_of_no_normal_four hno D,
    le_antisymm hDC D.le_centralizer⟩

end IsPGroup

namespace Subgroup

/-- The ambient formulation of absence of normal four-groups also excludes
normal four-groups in the subgroup considered as a group. -/
public theorem no_normal_four_of_no_normalized_four
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G)
    (hno : ¬ ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Q ∧ Q ≤ normalizer (F : Set G)) :
    ¬ ∃ E : Subgroup Q, E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  rintro ⟨E, hEn, hEe, hE⟩
  let : E.Normal := hEn
  let : IsElementaryAbelian 2 E := hEe
  apply hno
  refine ⟨E.map Q.subtype, IsElementaryAbelian.map_subtype,
    ?_, map_subtype_le _, ?_⟩
  · simpa only [card_map_of_injective Q.subtype_injective] using hE
  · simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using E.le_normalizer_map Q.subtype

end Subgroup
