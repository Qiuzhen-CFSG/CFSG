module

public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Theory.PGroupCore

/-!
# Automorphism obstructions for centric radical candidates

In a group satisfying the normalizer condition, a self-centralizing subgroup
whose normalizer acts by inner automorphisms is the whole group. Consequently,
if the intersection of the normalizer action with the automorphism p-core is
inner, a proper self-centralizing subgroup cannot have a p-group automorphism
group.

The proof uses the identity between the preimage of the inner automorphisms
and the product of the subgroup with its centralizer, followed by the
normalizer condition. This is the elementary normalizer obstruction used in
centric radical subgroup classification; no fusion system is required.
-/

namespace Subgroup

/-- A centric subgroup on which the normalizer acts by inner automorphisms is
self-normalizing, hence is the whole group under the normalizer condition. -/
public theorem eq_top_of_centric_of_normalizer_range_le_inner
    {G : Type*} [Group G] (hnc : NormalizerCondition G)
    (U : Subgroup G) (hc : centralizer (U : Set G) ≤ U)
    (hi : U.normalizerMonoidHom.range ≤ (MulAut.conj : U →* MulAut U).range) :
    U = ⊤ := by
  apply normalizerCondition_iff_only_full_group_self_normalizing.mp hnc U
  apply le_antisymm ?_ U.le_normalizer
  intro x hx
  have h : (⟨x, hx⟩ : normalizer (U : Set G)) ∈
      (MulAut.conj : U →* MulAut U).range.comap U.normalizerMonoidHom :=
    hi ⟨⟨x, hx⟩, rfl⟩
  rw [normalizerMonoidHom_comap_conj_range, sup_of_le_left hc] at h
  exact h

/-- A proper centric radical candidate cannot have its entire normalizer action
inside the automorphism p-core. -/
public theorem eq_top_of_centric_radical_of_range_le_pCore
    {G : Type*} [Group G] (hnc : NormalizerCondition G)
    (U : Subgroup G) (hc : centralizer (U : Set G) ≤ U) (p : ℕ)
    (hr : U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (ha : U.normalizerMonoidHom.range ≤ pCore p (MulAut U)) : U = ⊤ :=
  eq_top_of_centric_of_normalizer_range_le_inner hnc U hc
    (fun _ hx => hr ⟨hx, ha hx⟩)

/-- In particular, a proper centric radical candidate has automorphisms outside
the class of p-groups. -/
public theorem eq_top_of_centric_radical_of_isPGroup_mulAut
    {G : Type*} [Group G] (hnc : NormalizerCondition G)
    (U : Subgroup G) (hc : centralizer (U : Set G) ≤ U) (p : ℕ)
    (hr : U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (ha : IsPGroup p (MulAut U)) : U = ⊤ := by
  have htop : (⊤ : Subgroup (MulAut U)) ≤ pCore p (MulAut U) :=
    le_sSup ⟨inferInstance, ha.to_subgroup ⊤⟩
  exact eq_top_of_centric_radical_of_range_le_pCore hnc U hc p hr
    (le_top.trans htop)

/-- Intrinsic radicality pulls back along any ambient group isomorphism.
The induced subgroup and automorphism isomorphisms preserve the normalizer
image, the automorphism p-core, and the inner automorphisms. -/
public theorem intrinsic_radical_of_map_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (U : Subgroup G) (p : ℕ)
    (hrad : (U.map e.toMonoidHom).normalizerMonoidHom.range ⊓
      pCore p (MulAut (U.map e.toMonoidHom)) ≤
      (MulAut.conj : U.map e.toMonoidHom →* MulAut (U.map e.toMonoidHom)).range) :
    U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range := by
  let V := U.map e.toMonoidHom
  let u := U.equivMapOfInjective e.toMonoidHom e.injective
  let a := MulAut.congr u
  rintro f ⟨⟨g, rfl⟩, hp⟩
  have hnorm : e g ∈ normalizer (V : Set H) :=
    le_normalizer_map e.toMonoidHom (mem_map_of_mem e.toMonoidHom g.property)
  let g' : normalizer (V : Set H) := ⟨e g, hnorm⟩
  have hact : a (U.normalizerMonoidHom g) = V.normalizerMonoidHom g' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := u.surjective x
    apply Subtype.ext
    change e (g * (u.symm (u x) : U) * (g : G)⁻¹) = e g * e x * (e g)⁻¹
    rw [u.symm_apply_apply, map_mul, map_mul, map_inv]
  have haP : a (U.normalizerMonoidHom g) ∈ pCore p (MulAut V) := by
    rw [← pCore_map_iso p a]
    exact mem_map_of_mem a.toMonoidHom hp
  obtain ⟨v, hv⟩ := hrad ⟨⟨g', hact.symm⟩, haP⟩
  refine ⟨u.symm v, a.injective ?_⟩
  rw [← hv]
  apply MulEquiv.ext
  intro x
  change u (u.symm v * u.symm x * (u.symm v)⁻¹) = v * x * v⁻¹
  simp only [map_mul, map_inv, u.apply_symm_apply]

end Subgroup
