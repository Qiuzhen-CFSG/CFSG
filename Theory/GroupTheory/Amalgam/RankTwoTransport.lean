module

public import Theory.GroupTheory.Amalgam.RankTwo

/-!
# Transport of subgroup amalgams

An injective ambient homomorphism induces compatible isomorphisms on both
parabolics and their whole overlap. Injectivity also preserves the intersection,
so a subgroup amalgam remains a subgroup amalgam after transport.

This is the passage from matrix flag stabilizers to projective flag stabilizers
used in Aschbacher--Smith, Definitions F.1.4--5, printed p. 260.
-/

@[expose] public section

namespace Theory.GroupTheory.RankTwoAmalgam

variable {G H : Type*} [Group G] [Group H]

/-- Transport all three groups by the same injective map. In particular the
two isomorphisms on the parabolics agree on the entire overlap. -/
noncomputable def ofSubgroupsMapIso (f : G →* H) (hf : Function.Injective f)
    (P₁ B P₂ : Subgroup G) (h₁ : B ≤ P₁) (h₂ : B ≤ P₂) :
    Iso (ofSubgroups P₁ B P₂ h₁ h₂)
      (ofSubgroups (P₁.map f) (B.map f) (P₂.map f)
        (Subgroup.map_mono h₁) (Subgroup.map_mono h₂)) where
  left := P₁.equivMapOfInjective f hf
  middle := B.equivMapOfInjective f hf
  right := P₂.equivMapOfInjective f hf
  left_commutes b := by apply Subtype.ext; rfl
  right_commutes b := by apply Subtype.ext; rfl

/-- The whole overlap, rather than just a chosen Sylow subgroup, is preserved. -/
theorem map_overlap (f : G →* H) (hf : Function.Injective f)
    (P₁ B P₂ : Subgroup G) (h : P₁ ⊓ P₂ = B) :
    P₁.map f ⊓ P₂.map f = B.map f := by
  rw [← Subgroup.map_inf P₁ P₂ f hf, h]

end Theory.GroupTheory.RankTwoAmalgam
