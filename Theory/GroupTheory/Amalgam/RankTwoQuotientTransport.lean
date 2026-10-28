module
public import Theory.GroupTheory.Amalgam.RankTwo
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quotient transport of subgroup amalgams

For a homomorphism f, quotient each subgroup by its intersection with ker(f).
The first isomorphism theorem identifies these three quotients with their
images under f, and the identifications commute with both inclusion maps.
If the whole overlap contains the kernel, its image is still the whole overlap.

This supports passage from matrix to projective flag stabilizers even when
SL₃(F) → PSL₃(F) has nontrivial scalar kernel. It complements the injective
transport in `RankTwoTransport`.

Source: the first isomorphism theorem, applied to the amalgams of
Aschbacher–Smith, Definitions F.1.4–5, printed p.260.
-/

@[expose] public section
namespace Theory.GroupTheory.RankTwoAmalgam
variable {G H : Type*} [Group G] [Group H]

/-- The actual restricted map induces the isomorphism with its image. -/
noncomputable def subgroupQuotientMapEquiv (f : G →* H) (P : Subgroup G) :
    P ⧸ f.ker.subgroupOf P ≃* P.map f :=
  (QuotientGroup.quotientMulEquivOfEq
    (show f.ker.subgroupOf P = (f.subgroupMap P).ker by
      ext x
      change f x.val = 1 ↔ (f.subgroupMap P) x = 1
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap P)
      (f.subgroupMap_surjective P))

@[simp] theorem subgroupQuotientMapEquiv_mk (f : G →* H) (P : Subgroup G) (p : P) :
    subgroupQuotientMapEquiv f P (QuotientGroup.mk' _ p) = f.subgroupMap P p := rfl

/-- Quotient the three groups by the same ambient kernel. -/
def ofSubgroupQuotients (f : G →* H) (P₁ B P₂ : Subgroup G)
    (h₁ : B ≤ P₁) (h₂ : B ≤ P₂) :
    RankTwoAmalgam (P₁ ⧸ f.ker.subgroupOf P₁) (B ⧸ f.ker.subgroupOf B)
      (P₂ ⧸ f.ker.subgroupOf P₂) :=
  ⟨QuotientGroup.quotientMapSubgroupOfOfLe le_rfl h₁,
    QuotientGroup.quotientMapSubgroupOfOfLe le_rfl h₂⟩

/-- Both squares use the original homomorphism, with no independent choices. -/
noncomputable def ofSubgroupQuotientsMapIso (f : G →* H) (P₁ B P₂ : Subgroup G)
    (h₁ : B ≤ P₁) (h₂ : B ≤ P₂) :
    Iso (ofSubgroupQuotients f P₁ B P₂ h₁ h₂)
      (ofSubgroups (P₁.map f) (B.map f) (P₂.map f)
        (Subgroup.map_mono h₁) (Subgroup.map_mono h₂)) where
  left := subgroupQuotientMapEquiv f P₁
  middle := subgroupQuotientMapEquiv f B
  right := subgroupQuotientMapEquiv f P₂
  left_commutes b := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (f.ker.subgroupOf B) b
    rfl
  right_commutes b := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (f.ker.subgroupOf B) b
    rfl

/-- Containment of the kernel in the second subgroup suffices for preserving
the entire intersection. -/
theorem map_overlap_of_ker_le (f : G →* H) (P₁ P₂ : Subgroup G)
    (h₂ : f.ker ≤ P₂) :
    (P₁ ⊓ P₂).map f = P₁.map f ⊓ P₂.map f := by
  apply le_antisymm (Subgroup.map_inf_le _ _ _)
  rintro y ⟨⟨x, hx, rfl⟩, hx₂⟩
  have hx' : x ∈ (P₂.map f).comap f := hx₂
  rw [Subgroup.comap_map_eq_self h₂] at hx'
  exact Subgroup.mem_map_of_mem f ⟨hx, hx'⟩
end Theory.GroupTheory.RankTwoAmalgam
