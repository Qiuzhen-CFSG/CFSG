module
public import GorensteinWalter.DihedralAut
public import Theory.GroupTheory.CyclicTwoAut
public import Theory.GroupTheory.SpecificGroups.DihedralSubgroupModels
/-!
# Dihedral subgroups with exceptional automorphisms

A subgroup of `DihedralGroup (2^n)` whose automorphism group is not a
two-group is Klein four. This elementary reduction supplies the central
quotient step of ABG Chapter II §1 Lemma 3(i), article p.10.

The generic dihedral subgroup theorem gives a cyclic group or an actual
dihedral model of two-power order. Cyclic two-groups have two-group
automorphism groups. The same holds for dihedral groups of order at least
eight, by `GorensteinWalter.dihedral_mulAut_is_twoGroup`. The dihedral model
of order two is cyclic, leaving exactly the Klein four model. Automorphism
groups are transported along the proved subgroup equivalences.
-/

namespace ABG.Wreathed
public theorem dihedral_subgroup_automorphisms {n : ℕ} (D : Subgroup (DihedralGroup (2 ^ n)))
    (hAut : ¬ IsPGroup 2 (MulAut D)) : IsKleinFour D := by
  let : NeZero (2 ^ n) := ⟨by positivity⟩
  have hp : IsPGroup 2 (DihedralGroup (2 ^ n)) :=
    IsPGroup.of_card (n := n + 1) (by rw [DihedralGroup.nat_card, pow_succ]; omega)
  have hDp := hp.to_subgroup D
  rcases DihedralGroup.subgroup_cyclic_or_dihedral_two_power D with hc | ⟨k, ⟨e⟩⟩
  · let : IsCyclic D := hc
    exact (hAut hDp.mulAut_of_isCyclic_two).elim
  · by_cases hk0 : k = 0
    · subst k
      let : IsCyclic D := isCyclic_of_prime_card (p := 2) (by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
        norm_num)
      exact (hAut hDp.mulAut_of_isCyclic_two).elim
    · by_cases hk1 : k = 1
      · subst k
        exact {
          card_four := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]; norm_num
          exponent_two := by
            rw [Monoid.exponent_eq_of_mulEquiv e]
            exact (inferInstance : IsKleinFour (DihedralGroup 2)).exponent_two }
      · have hA := GorensteinWalter.dihedral_mulAut_is_twoGroup (m := k) (by omega)
        exact (hAut (hA.of_equiv (MulAut.congr e).symm)).elim
end ABG.Wreathed
