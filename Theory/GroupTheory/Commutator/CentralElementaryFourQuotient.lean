module
public import Theory.GroupTheory.Commutator.CentralDihedral
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Derived order in a central elementary-four extension

A finite group with a central normal subgroup and elementary quotient of
order four has derived subgroup of order at most two. No prescribed
commutator structure or two-group hypothesis is needed.

Recognize the quotient as the Klein four-group, hence as the dihedral group
of order four. The existing central-dihedral extension theorem bounds the
intersection of the center and derived subgroup by two. The abelian quotient
places the entire derived subgroup in the central kernel, giving the result.

This source-neutral counting step supplies the class-two reduction for
Stellmacher (10.1)(a), Journal of Algebra 190 (1997), printed p.60; its
geometric consumer constructs the actual central quotient.
-/

public theorem card_commutator_le_two_of_central_elementary_four_quotient
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : N ≤ Subgroup.center G)
    [IsElementaryAbelian 2 (G ⧸ N)] (hcard : Nat.card (G ⧸ N) = 4) :
    Nat.card (commutator G) ≤ 2 := by
  let W := G ⧸ N
  let _ : Nontrivial W := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hcard]; decide)
  let _ : IsKleinFour W := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  let equiv : W ≃* DihedralGroup 2 := IsKleinFour.nonempty_mulEquiv.some
  let projection := QuotientGroup.mk' N
  let f := equiv.toMonoidHom.comp projection
  have hsurj : Function.Surjective f := equiv.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : f.ker ≤ Subgroup.center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ equiv.injective, QuotientGroup.ker_mk']
    exact hN
  have hderived : commutator G ≤ Subgroup.center G :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative W)).trans hN
  have hbound := CentralExtension.card_center_inf_commutator_le_two_of_dihedral f hsurj hker
  rwa [inf_eq_right.mpr hderived] at hbound

