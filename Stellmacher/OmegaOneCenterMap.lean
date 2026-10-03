module

public import Stellmacher.SectionsOneToFourDefs

/-!
# Omega-center subgroups under injective maps

The ambient subgroup `Ω₁(Z(Q))` is elementary abelian at two and commutes
with injective group homomorphisms. This identifies an intrinsic Sylow-center subgroup inside
a local subgroup with its image in the common ambient group, as needed
for the application of (2.3) in Stellmacher (4.6).

Membership in `Ω₁(Z(Q))` is characterized by lying in `Q`, squaring to
one, and commuting with all of `Q`. The forward direction uses the
elementary-abelian omega subgroup of the center; the reverse inserts a
central involution among the defining closure generators. Injectivity
then transports all three conditions. The elementary-abelian assertion itself
is the image of the omega subgroup of the abelian center under the two subtype maps.

Source: `refs/latex/stellmacher-n-group.tex`, the Section Two notation
and its use in the second paragraph of (4.6).
-/

namespace Stellmacher

/-- The ambient omega-center is elementary abelian at two. -/
public theorem omegaOneCenterAmbient_elementaryAbelian
    {G : Type*} [Group G] (Q : Subgroup G) : IsElementaryAbelian 2 (omegaOneCenterAmbient Q) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 (omega₁ (Subgroup.center Q) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative (Subgroup.center Q)
  exact (IsElementaryAbelian.map (p := 2) (Subgroup.center Q).subtype).map Q.subtype

/-- The ambient omega-center consists exactly of central elements of the
subgroup whose squares are one. -/
public theorem mem_omegaOneCenterAmbient_iff
    {G : Type*} [Group G] (Q : Subgroup G) (x : G) :
    x ∈ omegaOneCenterAmbient Q ↔
      x ∈ Q ∧ x ^ 2 = 1 ∧ ∀ q ∈ Q, q * x = x * q := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hx
    obtain ⟨xQ, ⟨xZ, hxZ, rfl⟩, rfl⟩ := hx
    refine ⟨xZ.val.property, ?_, ?_⟩
    · let _ : IsElementaryAbelian 2 (omega₁ (Subgroup.center Q) (p := 2)) :=
        IsElementaryAbelian.omega₁_of_isMulCommutative (Subgroup.center Q)
      have hp := elemPow_eq_one_of_isElementaryAbelian (p := 2) xZ hxZ
      exact congrArg (fun z : Subgroup.center Q ↦ (z : G)) hp
    · intro q hq
      exact congrArg (fun z : Q ↦ (z : G))
        ((Subgroup.mem_center_iff.mp xZ.property) ⟨q, hq⟩)
  · rintro ⟨hxQ, hxpow, hxcent⟩
    let xQ : Q := ⟨x, hxQ⟩
    have hxZ : xQ ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      exact Subtype.ext (hxcent q q.property)
    let xZ : Subgroup.center Q := ⟨xQ, hxZ⟩
    have hxpowZ : xZ ^ 2 = 1 := by
      apply (Subgroup.center Q).subtype_injective
      apply Q.subtype_injective
      exact hxpow
    have hxomega : xZ ∈ omega₁ (Subgroup.center Q) (p := 2) := by
      apply Subgroup.subset_closure
      simpa using hxpowZ
    exact ⟨xQ, ⟨xZ, hxomega, rfl⟩, rfl⟩

/-- The ambient first omega subgroup of a center commutes with injective maps. -/
public theorem omegaOneCenterAmbient_map_injective
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (Q : Subgroup G) :
    omegaOneCenterAmbient (Q.map f) = (omegaOneCenterAmbient Q).map f := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyQ, hypow, hycent⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hy
    obtain ⟨x, hxQ, rfl⟩ := hyQ
    refine ⟨x, (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hxQ, ?_, ?_⟩, rfl⟩
    · apply hf
      simpa using hypow
    · intro q hq
      apply hf
      simpa using hycent (f q) ⟨q, hq, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxQ, hxpow, hxcent⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hx
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨⟨x, hxQ, rfl⟩, ?_, ?_⟩
    · simpa using congrArg f hxpow
    · rintro q ⟨a, ha, rfl⟩
      simpa using congrArg f (hxcent a ha)

end Stellmacher
