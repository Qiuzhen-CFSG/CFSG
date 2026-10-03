module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Elementary two-subgroups in C5 semidirect C4

For every action of C4 on C5, each two-subgroup is cyclic of order
dividing four. Consequently each elementary abelian two-subgroup of the
semidirect product has order at most two. The action need not be faithful;
in particular the theorem applies to the Frobenius action without using
its injectivity as an additional premise.

The right projection has a five-group kernel, the image of C5. That kernel
meets the elementary two-subgroup trivially, so projection embeds the
subgroup in C4. It is therefore cyclic; its exponent, and hence its order,
divides two.

This source-neutral projection argument supplies the elementary image
bound for the order-twenty local quotient in Stellmacher (10.1). The
concrete cyclic groups use native Multiplicative/ZMod types, avoiding
campaign definitions in the Theory layer.
-/

namespace SemidirectProduct

/-- Every two-subgroup of C5 semidirect C4 embeds in the cyclic right
factor, and therefore is cyclic of order dividing four. -/
public theorem two_subgroup_isCyclic_card_dvd_four
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (A : Subgroup (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ))
    (hA : IsPGroup 2 A) : IsCyclic A ∧ Nat.card A ∣ 4 := by
  let projection : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      Multiplicative (ZMod 4) := rightHom
  have hnormal : IsPGroup 5 (Multiplicative (ZMod 5)) := by
    apply IsPGroup.of_card (n := 1)
    norm_num
  have hkernel : IsPGroup 5 projection.ker := by
    rw [show projection.ker = (inl : Multiplicative (ZMod 5) →*
      SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ).range from
        range_inl_eq_ker_rightHom.symm]
    exact hnormal.of_surjective _ (MonoidHom.rangeRestrict_surjective inl)
  have hdisjoint : Disjoint A projection.ker :=
    hA.disjoint_of_coprime hkernel (by decide)
  have hinjective : Function.Injective (projection.comp A.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro actor hactor
    exact Subtype.ext (hdisjoint.le_bot ⟨actor.property,hactor⟩)
  refine ⟨isCyclic_of_injective (projection.comp A.subtype) hinjective, ?_⟩
  simpa using Subgroup.card_dvd_of_injective (projection.comp A.subtype) hinjective

public theorem elementary_two_subgroup_card_le_two
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (A : Subgroup (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ))
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 2 := by
  let _ := hA
  let _ : IsCyclic A :=
    (two_subgroup_isCyclic_card_dvd_four φ A (IsElementaryAbelian.isPGroup 2 A)).1
  have hcard : Nat.card A ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 A
  exact Nat.le_of_dvd (by decide) hcard

end SemidirectProduct
