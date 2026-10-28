module

public import Theory.GroupTheory.CoprimeQuotientNormalizer

/-!
# Lifting full normalizer actions

A surjection with kernel of order prime to `p` maps the normalizer of a
`p`-subgroup onto the normalizer of its image. If the map is injective on
that subgroup, every automorphism realized downstairs is realized upstairs.
The first assertion is the coprime quotient normalizer theorem (the Frattini
argument); the second transports conjugation through the subgroup isomorphism.
-/

namespace Subgroup

/-- The coprime quotient normalizer theorem for an arbitrary surjection. -/
public theorem normalizer_map_eq_of_coprime_kernel
    {G H : Type*} [Group G] [Finite G] [Group H]
    (p : ℕ) [Fact p.Prime] (A : Subgroup G) [Fact (IsPGroup p A)]
    (f : G →* H) (hf : Function.Surjective f)
    (hcop : Nat.Coprime p (Nat.card f.ker)) :
    normalizer (A.map f : Set H) = (normalizer (A : Set G)).map f := by
  let q := QuotientGroup.mk' f.ker
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have he : e.toMonoidHom.comp q = f := by ext; rfl
  have h := normalizer_map_quotient_eq_map_normalizer p A f.ker inferInstance hcop
  have hm := congrArg (fun B : Subgroup (G ⧸ f.ker) => B.map e.toMonoidHom) h
  rw [map_equiv_normalizer_eq, map_map, map_map, he] at hm
  exact hm

/-- Transport a full normalizer action across an isomorphic subgroup, provided
normalizing elements lift. -/
public theorem normalizerMonoidHom_surjective_of_lift
    {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) (f : G →* H) (e : A ≃* B)
    (he : ∀ a : A, (e a : H) = f a)
    (hN : normalizer (B : Set H) ≤ (normalizer (A : Set G)).map f)
    (hB : Function.Surjective B.normalizerMonoidHom) :
    Function.Surjective A.normalizerMonoidHom := by
  intro α
  obtain ⟨b, hb⟩ := hB (e.symm.trans (α.trans e))
  obtain ⟨g, hg, hfg⟩ := hN b.property
  refine ⟨⟨g, hg⟩, ?_⟩
  apply MulEquiv.ext
  intro a
  apply e.injective
  apply Subtype.ext
  rw [he, he]
  change f (g * (a : G) * g⁻¹) = f (α a)
  rw [map_mul, map_mul, map_inv, hfg, ← he a, ← he (α a)]
  have h := congrArg (fun β : MulAut B => (β (e a) : H)) hb
  simpa using h

/-- Full normalizer action in an intermediate subgroup gives the corresponding
restricted ambient action. -/
public theorem normalizerMonoidHom_restrict_surjective
    {G : Type*} [Group G] (A M : Subgroup G) (hAM : A ≤ M)
    (h : Function.Surjective (A.subgroupOf M).normalizerMonoidHom) :
    Function.Surjective (A.normalizerMonoidHom.comp
      (M.subgroupOf (normalizer (A : Set G))).subtype) := by
  let e := subgroupOfEquivOfLe hAM
  intro α
  obtain ⟨x, hx⟩ := h (e.trans (α.trans e.symm))
  have hn : (x.val : G) ∈ normalizer (A : Set G) := by
    have hxN := x.property
    exact (show (x.val : M) ∈ (normalizer (A : Set G)).subgroupOf M from
      (subgroupOf_normalizer_eq hAM).symm ▸ hxN)
  refine ⟨⟨⟨x.val, hn⟩, x.val.property⟩, ?_⟩
  apply MulEquiv.ext
  intro a
  have hv := congrArg (fun β : MulAut (A.subgroupOf M) =>
    (((β (e.symm a)) : M) : G)) hx
  apply Subtype.ext
  simpa [e, subgroupOfEquivOfLe] using hv

end Subgroup
