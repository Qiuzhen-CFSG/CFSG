module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases

/-!
# Centralizers of large subgroups in the dihedral group of order eight

Every subgroup of `DihedralGroup 4` with at least four elements contains its
centralizer, and that centralizer has at most four elements. The whole group
is allowed; no abelianness hypothesis is imposed on the given subgroup.

The actual dihedral normal forms give a center of at most two elements by
finite computation. Thus a subgroup of order at least four has a proper
centralizer. Lagrange's theorem bounds every proper subgroup by four. If the
given subgroup is proper, it has order four and is abelian by the prime-square
order theorem; containment in its centralizer and the cardinal bound then give
equality. For the whole group, only the centralizer cardinal bound is needed.

This intrinsic calculation supplies the dihedral Sylow centralizer bound used
in Stellmacher (9.1), relation (9), journal p. 47, via the separate concrete
wreath-product Sylow model and transport. The proof uses Mathlib's dihedral
group and finite-group APIs, independently of the campaign's hypotheses.
-/

namespace DihedralGroup

private theorem center_card_le_two :
    Nat.card (Subgroup.center (DihedralGroup 4)) ≤ 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem card_le_four_of_ne_top (subgroup : Subgroup (DihedralGroup 4))
    (hne : subgroup ≠ ⊤) : Nat.card subgroup ≤ 4 := by
  have hdiv := subgroup.card_subgroup_dvd_card
  rw [nat_card] at hdiv
  have hlt : Nat.card subgroup < 8 := by
    have hle := subgroup.card_le_card_group
    rw [nat_card] at hle
    have hneq : Nat.card subgroup ≠ 8 := by
      intro heq
      apply hne
      apply subgroup.eq_top_of_card_eq
      simpa only [nat_card] using heq
    omega
  interval_cases hcard : Nat.card subgroup <;> norm_num [hcard] at *

/-- A subgroup of order at least four in the dihedral group of order eight
contains its centralizer, whose order is at most four. -/
public theorem centralizer_le_of_card_ge_four
    (W : Subgroup (DihedralGroup 4)) (hW : 4 ≤ Nat.card W) :
    Subgroup.centralizer (W : Set (DihedralGroup 4)) ≤ W ∧
      Nat.card (Subgroup.centralizer (W : Set (DihedralGroup 4))) ≤ 4 := by
  have hproper : Subgroup.centralizer (W : Set (DihedralGroup 4)) ≠ ⊤ := by
    intro heq
    have hle : W ≤ Subgroup.center (DihedralGroup 4) :=
      Subgroup.centralizer_eq_top_iff_subset.mp heq
    have hsmall := (Subgroup.card_le_of_le hle).trans center_card_le_two
    omega
  have hbound := card_le_four_of_ne_top _ hproper
  refine ⟨?_, hbound⟩
  by_cases htop : W = ⊤
  · rw [htop]
    exact le_top
  have hcard : Nat.card W = 4 := Nat.le_antisymm (card_le_four_of_ne_top W htop) hW
  have hcomm : IsMulCommutative W :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard
  have hle : W ≤ Subgroup.centralizer (W : Set (DihedralGroup 4)) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm
  exact (Subgroup.eq_of_le_of_card_ge hle (hbound.trans hW)).ge

end DihedralGroup
