module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.Collection

/-!
# An endpoint automorphism from a bounded graph subgroup

The graph of two assignments satisfying the Weyl relations has at most
12288 elements by the coordinate collection theorem. Its first projection
surjects onto the literal endpoint of that order, so it is an isomorphism.
Generation by the proposed images makes the second projection surjective as
well. Their composite is an actual automorphism, with the full Sylow square
and the reflection image both specified.

Source: the graph construction in Tits/AmalgamRigidity/LocalRestrictions/
SecondExtension/Graph.lean; source application is Aschbacher–Smith F.1.11–12,
pp.262–263, with Parrott's marking on p.683.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.SecondExtension
open ReeTwo

/-- Word equations hold componentwise in the graph construction. -/
theorem WeylRelations.prod {G H : Type*} [Group G] [Group H]
    {f : SylowModel →* G} {g : SylowModel →* H} {r : G} {s : H}
    (hf : WeylRelations f r) (hg : WeylRelations g s) :
    WeylRelations (f.prod g) (r, s) where
  square := Prod.ext hf.square hg.square
  cube := Prod.ext hf.cube hg.cube
  conjugate i := Prod.ext (hf.conjugate i) (hg.conjugate i)

private theorem normalForm_mem {G : Type*} [Group G] (f : SylowModel →* G)
    (r : G) (p : radical × Fin 3 × Fin 2) :
    normalForm f r p ∈ Subgroup.closure (insert r (Set.range f)) := by
  let H := Subgroup.closure (insert r (Set.range f))
  have hf (x : SylowModel) : f x ∈ H := Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)
  have hr : r ∈ H := Subgroup.subset_closure (Or.inl rfl)
  exact H.mul_mem (H.mul_mem (hf _) (H.pow_mem (H.mul_mem (hf _) hr) _)) (H.pow_mem hr _)

/-- The generated finite image has at most 12288 elements. -/
theorem generated_card_le {G : Type*} [Group G] [Finite G]
    (f : SylowModel →* G) (r : G) (h : WeylRelations f r) :
    Nat.card (Subgroup.closure (insert r (Set.range f))) ≤ 12288 := by
  let H := Subgroup.closure (insert r (Set.range f))
  let F : radical × Fin 3 × Fin 2 → H := fun p => ⟨normalForm f r p, normalForm_mem f r p⟩
  have hs : Function.Surjective F := by
    intro x
    obtain ⟨p, hp⟩ := normalForm_surjective f r h x.property
    exact ⟨p, Subtype.ext hp⟩
  have hb := Nat.card_le_card_of_surjective F hs
  simpa only [Nat.card_prod, radical_card, Nat.card_fin] using hb

/-- The graph of two assignments is a group of the same order as the literal
endpoint. Both projections are therefore isomorphisms when both assignments
generate, yielding an actual automorphism with the required values. -/
theorem exists_aut_of_relations {G : Type*} [Group G] [Finite G]
    (f g : SylowModel →* G) (r s : G)
    (hf : WeylRelations f r) (hg : WeylRelations g s)
    (gf : Subgroup.closure (insert r (Set.range f)) = ⊤)
    (gg : Subgroup.closure (insert s (Set.range g)) = ⊤)
    (card : Nat.card G = 12288) :
    ∃ a : MulAut G, (∀ x, a (f x) = g x) ∧ a r = s := by
  let k := f.prod g
  let K := Subgroup.closure (insert (r, s) (Set.range k))
  let q₁ : K →* G := (MonoidHom.fst G G).comp K.subtype
  let q₂ : K →* G := (MonoidHom.snd G G).comp K.subtype
  have hq₁ : Function.Surjective q₁ := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← gf]
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases hz with hz | ⟨x, hx⟩
    · subst z
      exact ⟨⟨(r, s), Subgroup.subset_closure (Or.inl rfl)⟩, rfl⟩
    · subst z
      exact ⟨⟨k x, Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)⟩, rfl⟩
  have hq₂ : Function.Surjective q₂ := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← gg]
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases hz with hz | ⟨x, hx⟩
    · subst z
      exact ⟨⟨(r, s), Subgroup.subset_closure (Or.inl rfl)⟩, rfl⟩
    · subst z
      exact ⟨⟨k x, Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)⟩, rfl⟩
  have hcard : Nat.card K ≤ Nat.card G := by
    rw [card]
    exact generated_card_le k (r, s) (hf.prod hg)
  let e : K ≃* G := MulEquiv.ofBijective q₁ (hq₁.bijective_of_nat_card_le hcard)
  let F : G →* G := q₂.comp e.symm.toMonoidHom
  have hF : Function.Surjective F := hq₂.comp e.symm.surjective
  let a : MulAut G := MulEquiv.ofBijective F hF.bijective_of_finite
  refine ⟨a, ?_, ?_⟩
  · intro x
    have he : e ⟨k x, Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)⟩ = f x := rfl
    change q₂ (e.symm (f x)) = g x
    rw [← he, e.symm_apply_apply]
    rfl
  · have he : e ⟨(r, s), Subgroup.subset_closure (Or.inl rfl)⟩ = r := rfl
    change q₂ (e.symm r) = s
    rw [← he, e.symm_apply_apply]
    rfl

end Tits.AmalgamRigidity.FullRee.SecondExtension
