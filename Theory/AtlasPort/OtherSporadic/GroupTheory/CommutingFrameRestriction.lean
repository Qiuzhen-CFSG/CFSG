/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/CommutingFrameRestriction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.ThreeTranspositionFrames

/-!
# Commuting frames inside subgroups

Maximal commuting frames restrict to subgroups containing them. Applying
three-transposition frame conjugacy inside the subgroup gives internal
conjugators, preserving the distinction from ambient conjugacy.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/CommutingFrameRestriction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream calculations.
-/

@[expose] public section

namespace Atlas.GroupTheory

/-- A full commuting frame contained in a subgroup remains maximal among the
distinguished elements of that subgroup. -/
theorem IsCommutingFrame.subgroup_preimage {G : Type*} [Group G]
    {D F : Set G} (hF : IsCommutingFrame D F) (L : Subgroup G)
    (hFL : F ⊆ L) :
    IsCommutingFrame (L.subtype ⁻¹' D) (L.subtype ⁻¹' F) := by
  refine ⟨fun _ hx => hF.1 hx, ?_, ?_⟩
  · intro x hx y hy
    apply Subtype.ext
    exact (hF.2.1 x.val hx y.val hy).eq
  · intro E hE hc hsub
    have heq : L.subtype '' E = F := hF.2.2 _ (by
      rintro x ⟨y,hy,rfl⟩
      exact hE hy) (by
      rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
      exact (hc a ha b hb).map L.subtype) (by
      intro x hx
      exact ⟨⟨x,hFL hx⟩,hsub hx,rfl⟩)
    apply Set.Subset.antisymm ?_ hsub
    intro x hx
    change x.val ∈ F
    rw [← heq]
    exact ⟨x,hx,rfl⟩

/-- Sylow conjugacy can be applied inside any subgroup containing both frames.
In particular, this does not replace internal conjugacy by ambient conjugacy. -/
theorem commutingFrames_conjugate_in_subgroup {G : Type*} [Group G] [Finite G]
    (D F K : Set G) (L : Subgroup G)
    (hsq : ∀ x ∈ D, x ^ 2 = 1)
    (hprod : ∀ x ∈ D, ∀ y ∈ D, (x*y)^2=1 ∨ orderOf (x*y)=3)
    (hD : ∀ g : G, (MulAut.conj g) '' D = D)
    (hF : IsCommutingFrame D F) (hK : IsCommutingFrame D K)
    (hFL : F ⊆ L) (hKL : K ⊆ L) :
    ∃ g : L, (MulAut.conj g.val) '' F = K := by
  have hconj : ∀ g : L,
      (MulAut.conj g) '' (L.subtype ⁻¹' D) = L.subtype ⁻¹' D := by
    intro g
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change g.val*y.val*g.val⁻¹ ∈ D
      rw [← hD g.val]
      exact ⟨y.val,hy,rfl⟩
    · intro hx
      refine ⟨(MulAut.conj g).symm x,?_,(MulAut.conj g).apply_symm_apply x⟩
      change g.val⁻¹*x.val*g.val ∈ D
      rw [← hD g.val⁻¹]
      exact ⟨x.val,hx,by simp⟩
  obtain ⟨g,hg⟩ := commutingFrames_conjugate
    (L.subtype ⁻¹' D) (L.subtype ⁻¹' F) (L.subtype ⁻¹' K)
    (fun x hx => Subtype.ext (hsq x.val hx)) (by
      intro x hx y hy
      rcases hprod x.val hx y.val hy with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr ((orderOf_injective L.subtype L.subtype_injective (x*y)).symm.trans h))
    hconj (hF.subgroup_preimage L hFL) (hK.subgroup_preimage L hKL)
  refine ⟨g,?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    have hm : MulAut.conj g (⟨y,hFL hy⟩ : L) ∈ L.subtype ⁻¹' K := by
      rw [← hg]
      exact ⟨⟨y,hFL hy⟩,hy,rfl⟩
    exact hm
  · intro x hx
    have hm : (⟨x,hKL hx⟩ : L) ∈ L.subtype ⁻¹' K := hx
    rw [← hg] at hm
    obtain ⟨y,hy,he⟩ := hm
    exact ⟨y.val,hy,congrArg Subtype.val he⟩

end Atlas.GroupTheory
