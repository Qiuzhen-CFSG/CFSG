module
public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Perm

/-!
# Full outer index gives every automorphism

Let `H` be a subgroup of a finite group `G`. If the index of `H C_G(H)` in
`N_G(H)` equals the index of the inner automorphisms in `Aut(H)`, then every
automorphism of `H` is induced by an element of `N_G(H)`.

The normalizer action image contains the inner automorphism group. The
preimage identity from `NormalizerInnerAutomorphisms` rewrites the ambient
outer index as the relative index of the inner automorphisms in this image.
Multiplication of subgroup indices then forces the image to have index one
in `Aut(H)`. Finiteness makes the index cancelled in this step positive.

This general finite-group observation supplies full normalizer fusion when
the quaternion outer automizer index is six in Alperin–Brauer–Gorenstein,
Chapter II, Section 1, Proposition 1. It makes no quaternion or quasi-dihedral
assumption and retains the full denominator `H ⊔ C_G(H)`.
-/

namespace Subgroup

/-- Equality with the full outer automorphism index forces the normalizer action
to realize every automorphism of the subgroup. -/
public theorem normalizerMonoidHom_surjective_of_outer_index
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hindex : (H ⊔ centralizer (H : Set G)).relIndex (normalizer (H : Set G)) =
      (MulAut.conj : H →* MulAut H).range.index) :
    Function.Surjective H.normalizerMonoidHom := by
  let I := (MulAut.conj : H →* MulAut H).range
  let R := H.normalizerMonoidHom.range
  have hIR : I ≤ R := by
    rintro f ⟨x, rfl⟩
    refine ⟨⟨x.val, H.le_normalizer x.property⟩, ?_⟩
    ext y
    rfl
  have hi : I.relIndex R = I.index := by
    rwa [relIndex, ← normalizerMonoidHom_comap_conj_range, index_comap] at hindex
  have hmul := relIndex_mul_index hIR
  rw [hi] at hmul
  have hne : I.index ≠ 0 := index_ne_zero_of_finite
  have hR : R.index = 1 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
    (by simpa using hmul)
  exact MonoidHom.range_eq_top.mp (index_eq_one.mp hR)

end Subgroup

