module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.Transport

/-!
# An automorphism from the finite graph of a generator assignment

Generate a subgroup by pairs of original and image generators. The collection
equations give the same 6144 normal forms in this graph. Uniqueness in its first
coordinate makes first projection injective. Generation makes both projections
surjective, so their composite is the required automorphism.

This proves the assignment is multiplicative on the actual group, without
assuming an unproved presentation or an ambient permutation normalizer.
Source conventions: Parrott (1972), §5, p.683; see `Words`.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.SecondExtension

/-- The collection certificates construct an actual automorphism. -/
theorem exists_aut {G : Type*} [Group G] [Finite G] (g h : Fin 9 → G)
    (gs : SylowRelations g) (hs : SylowRelations h)
    (gc : CosetRelations g) (hc : CosetRelations h)
    (gg : Subgroup.closure (Set.range g) = ⊤)
    (hg : Subgroup.closure (Set.range h) = ⊤)
    (unique : Function.Injective
      (fun p : Fin 2048 × Fin 3 => word g p.1 * rep g p.2)) :
    ∃ a : MulAut G, ∀ i, a (g i) = h i := by
  let k : Fin 9 → G × G := fun i => (g i, h i)
  let K := Subgroup.closure (Set.range k)
  let q₁ : K →* G := (MonoidHom.fst G G).comp K.subtype
  let q₂ : K →* G := (MonoidHom.snd G G).comp K.subtype
  have hq₁ : Function.Surjective q₁ := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← gg]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨k i, Subgroup.subset_closure ⟨i, rfl⟩⟩, rfl⟩
  have hq₂ : Function.Surjective q₂ := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hg]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨k i, Subgroup.subset_closure ⟨i, rfl⟩⟩, rfl⟩
  have hk₁ : Function.Injective q₁ := by
    intro x y hxy
    obtain ⟨p, hp⟩ := normalForm_surjective k (gs.prod hs) (gc.prod hc) x.property
    obtain ⟨q, hq⟩ := normalForm_surjective k (gs.prod hs) (gc.prod hc) y.property
    have he : p = q := unique (by
      change x.val.1 = y.val.1 at hxy
      rw [← hp, ← hq] at hxy
      exact hxy)
    exact Subtype.ext (hp.symm.trans (he ▸ hq))
  let e : K ≃* G := MulEquiv.ofBijective q₁ ⟨hk₁, hq₁⟩
  let f : G →* G := q₂.comp e.symm.toMonoidHom
  have hf : Function.Surjective f := hq₂.comp e.symm.surjective
  let a : MulAut G := MulEquiv.ofBijective f hf.bijective_of_finite
  refine ⟨a, fun i => ?_⟩
  have hi : e ⟨k i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = g i := rfl
  change q₂ (e.symm (g i)) = h i
  rw [← hi, e.symm_apply_apply]
  rfl

end Tits.AmalgamRigidity.SecondExtension
