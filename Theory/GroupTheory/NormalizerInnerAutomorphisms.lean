module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Conj

/-!
# Inner automorphisms in a subgroup normalizer action

For any subgroup `H` of a group `G`, the elements of its normalizer inducing
inner automorphisms of `H` are exactly `H ⊔ C_G(H)`, viewed as a subgroup of
`N_G(H)`. No finiteness or normality assumption on `H` in `G` is required.

The normalizer action maps the copy of `H` inside its normalizer onto the
inner automorphism group. The preimage of that image is the copy of `H`
joined with the action kernel, and the kernel is the centralizer. Taking
subgroups inside the normalizer respects this join because both subgroups
lie in the normalizer.

This standard normalizer–centralizer identity supplies the outer automorphism
comparison in Alperin–Brauer–Gorenstein, Chapter II, Section 1, Proposition 1.
The statement is independent of the quasi-dihedral and quaternion hypotheses
of that application.
-/

namespace Subgroup

/-- The normalizer elements inducing inner automorphisms are the subgroup joined
with its centralizer, restricted to the normalizer. -/
public theorem normalizerMonoidHom_comap_conj_range {G : Type*} [Group G]
    (H : Subgroup G) :
    (MulAut.conj : H →* MulAut H).range.comap H.normalizerMonoidHom =
      (H ⊔ centralizer (H : Set G)).subgroupOf (normalizer (H : Set G)) := by
  have hmap : (H.subgroupOf (normalizer (H : Set G))).map H.normalizerMonoidHom =
      (MulAut.conj : H →* MulAut H).range := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x.val, hx⟩, ?_⟩
      ext t
      rfl
    · rintro ⟨x, rfl⟩
      refine ⟨⟨x.val, H.le_normalizer x.property⟩, x.property, ?_⟩
      ext t
      rfl
  rw [← hmap, comap_map_eq, normalizerMonoidHom_ker,
    subgroupOf_sup H.le_normalizer (centralizer_le_normalizer (H : Set G))]

end Subgroup

