module

public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Characteristic pairs and restriction to the ambient center

For a characteristic subgroup B of a finite p-group P, a nontrivial
characteristic subgroup D of B of exponent p gives the subgroup Z(P) ∩ D.
This module records its intrinsic image in B, the compatibility with another
central restriction, and the nontrivial convention needed for such pairs.
The nontriviality argument uses the center of a p-group and Cauchy's theorem.

These are the elementary subgroup transports in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
Remark C.1.19 and Notation C.1.20, pp.126–127.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- Restrict an intrinsic subgroup of B to the center of its ambient group. -/
@[expose] def centerRestriction (B : Subgroup G) (D : Subgroup B) : Subgroup G :=
  center G ⊓ D.map B.subtype

/-- The restricted group is contained in B, so it can be embedded wherever B is. -/
theorem centerRestriction_le (B : Subgroup G) (D : Subgroup B) :
    centerRestriction B D ≤ B :=
  inf_le_right.trans (map_subtype_le D)

/-- Recover the intrinsic subgroup from its ambient image. -/
theorem image_subgroupOf_subtype (B : Subgroup G) (D : Subgroup B) :
    (D.map B.subtype).subgroupOf B = D := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (B.subtype_injective heq) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Central restriction only shrinks the original intrinsic subgroup. -/
theorem centerRestriction_subgroupOf_le (B : Subgroup G) (D : Subgroup B) :
    (centerRestriction B D).subgroupOf B ≤ D := by
  intro x hx
  obtain ⟨y, hy, heq⟩ := hx.2
  exact (B.subtype_injective heq) ▸ hy

/-- An element central in the ambient group is already central in B.
Thus the inner central restriction does not change the final subgroup. -/
theorem centerRestriction_inf_center (B : Subgroup G) (D : Subgroup B) :
    centerRestriction B (center B ⊓ D) = centerRestriction B D := by
  apply le_antisymm
  · exact inf_le_inf_left _ (map_mono inf_le_right)
  · rintro x ⟨hz, y, hy, rfl⟩
    refine ⟨hz, y, ⟨?_, hy⟩, rfl⟩
    change y ∈ center B
    rw [mem_center_iff]
    intro b
    apply Subtype.ext
    exact (mem_center_iff.mp hz) b

/-- The full characteristic-center conclusion with an omega-center input. -/
theorem centerRestriction_spec [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (B : Subgroup G) [B.Characteristic]
    (D : Subgroup B) [D.Characteristic] (hne : D ≠ ⊥)
    (hD : D ≤ (omega₁ (center B) (p := p)).map (center B).subtype) :
    (centerRestriction B D).Characteristic ∧
      centerRestriction B D ≠ ⊥ ∧
      centerRestriction B D ≤ (omega₁ (center G) (p := p)).map (center G).subtype := by
  apply characteristic_center_reduction hp B D hne
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hD hx
  let : IsElementaryAbelian p (omega₁ (center B) (p := p)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative (center B)
  exact congrArg (center B).subtype
    (elemPow_eq_one_of_isElementaryAbelian (p := p) z hz)

/-- The omega center of a nontrivial finite p-group is nontrivial. -/
theorem omega_center_ne_bot [Finite G] [Nontrivial G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) :
    (omega₁ (center G) (p := p)).map (center G).subtype ≠ ⊥ := by
  let : Nontrivial (center G) := hp.center_nontrivial
  obtain ⟨n, hn, hcard⟩ :=
    (hp.to_subgroup (center G)).nontrivial_iff_card.mp inferInstance
  apply omega₁_map_subtype_ne_bot
  rw [hcard]
  exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn)

/-- Nontriviality of P is exactly the convention needed even for the first
structural clause of a characteristic pair; the trivial group has no witness. -/
theorem exists_characteristic_omega_center_iff [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) :
    (∃ D : Subgroup G, D.Characteristic ∧ D ≠ ⊥ ∧
      D ≤ (omega₁ (center G) (p := p)).map (center G).subtype) ↔ Nontrivial G := by
  constructor
  · rintro ⟨D, _, hne, _⟩
    let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hne
    exact D.subtype_injective.nontrivial
  · intro h
    let : Nontrivial G := h
    let : (omega₁ (center G) (p := p)).Characteristic := omega₁_characteristic _
    exact ⟨_, inferInstance, omega_center_ne_bot hp, le_rfl⟩

end Subgroup
