module
public import Stellmacher.SL2DerivedCard

/-!
# An SL₂(2) factor from its derived subgroup and one involution

The derived subgroup of an `SL₂(2)` factor has order three. Together with
any involution of order two in the factor, its ambient image generates the
whole order-six factor: their join contains subgroups of coprime orders three
and two, so Lagrange's theorem forces order six.

This group-theoretic identity supplies the selected factor-image equality
in Stellmacher (9.4). The factor and involution there come from the local
quotient action; this module only proves their generation property.
-/

namespace Stellmacher.SectionOne

universe u

/-- The derived three-subgroup and any involution generate an `SL₂(2)` factor. -/
public theorem sl2_derived_involution_generate
    {K : Type u} [Group K] [Finite K]
    (D : Subgroup K) (hD : IsSL2Two D)
    (u : K) (hu : u ∈ D) (hu2 : IsInvolution u) :
    D = ((commutator D).map D.subtype) ⊔ Subgroup.zpowers u := by
  let F := (commutator D).map D.subtype
  let Q := Subgroup.zpowers u
  have hFcard : Nat.card F = 3 := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact isSL2Two_commutator_card hD
  have hQcard : Nat.card Q = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu2.2 hu2.1]
  have hle : F ⊔ Q ≤ D :=
    sup_le (Subgroup.map_subtype_le _) ((Subgroup.zpowers_le).2 hu)
  have hthree : 3 ∣ Nat.card ↥(F ⊔ Q) :=
    hFcard ▸ Subgroup.card_dvd_of_le (le_sup_left : F ≤ F ⊔ Q)
  have htwo : 2 ∣ Nat.card ↥(F ⊔ Q) :=
    hQcard ▸ Subgroup.card_dvd_of_le (le_sup_right : Q ≤ F ⊔ Q)
  have hsix : 6 ∣ Nat.card ↥(F ⊔ Q) :=
    (show Nat.Coprime 3 2 by decide).mul_dvd_of_dvd_of_dvd hthree htwo
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [RankOneThreeGroupAssembly.isSL2Two_card hD]
    exact Nat.le_of_dvd Nat.card_pos hsix)).symm

end Stellmacher.SectionOne
