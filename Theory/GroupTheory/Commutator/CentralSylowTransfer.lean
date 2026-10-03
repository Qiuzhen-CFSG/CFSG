module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Central derived elements and Sylow transfer

In a finite group, a central element in both the ambient derived subgroup
and a Sylow subgroup belongs to the Sylow subgroup's derived subgroup.
Transfer to the Sylow abelianization kills the ambient derived subgroup,
and on a central element is the Sylow-index power. This index is coprime
to the image's order, forcing that image to be trivial.

This generic transfer calculation supplies the kernel-control step in the
two-primary central-cover argument used by Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 2. It uses no Schur-multiplier assumption.
-/

namespace Subgroup

private theorem mem_sylow_commutator_of_mem_center_of_mem_commutator
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (x : S)
    (hxcenter : (x : G) ∈ center G)
    (hxderived : (x : G) ∈ _root_.commutator G) :
    x ∈ _root_.commutator S := by
  let f : S →* Abelianization S := Abelianization.of
  let t : G →* Abelianization S := MonoidHom.transfer f
  have hkey : ∀ (k : ℕ) (g : G),
      g⁻¹ * (x : G) ^ k * g ∈ (S : Subgroup G) →
        g⁻¹ * (x : G) ^ k * g = (x : G) ^ k := by
    intro k g _
    have hcomm := mem_center_iff.mp ((center G).pow_mem hxcenter k) g
    calc
      g⁻¹ * (x : G) ^ k * g = g⁻¹ * (g * (x : G) ^ k) := by
        rw [mul_assoc, hcomm.symm]
      _ = (x : G) ^ k := inv_mul_cancel_left _ _
  have ht : t x = 1 := Abelianization.commutator_subset_ker t hxderived
  have hpow : f x ^ (S : Subgroup G).index = 1 := by
    have htransfer := MonoidHom.transfer_eq_pow f (x : G) hkey
    have hsame : t x = f (x ^ (S : Subgroup G).index) := htransfer
    rw [hsame, map_pow] at ht
    exact ht
  have hdvd : orderOf (f x) ∣ Nat.card S :=
    (orderOf_map_dvd f x).trans (_root_.orderOf_dvd_natCard x)
  have hcop : (orderOf (f x)).Coprime (S : Subgroup G).index :=
    S.card_coprime_index.coprime_dvd_left hdvd
  have horder : orderOf (f x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (orderOf_dvd_of_pow_eq_one hpow)
  have hfx : f x = 1 := orderOf_eq_one_iff.mp horder
  change x ∈ Abelianization.of.ker at hfx
  rwa [Abelianization.ker_of] at hfx

/-- Central elements of the ambient derived subgroup that lie in a Sylow
subgroup lie in its derived subgroup. -/
public theorem center_inf_commutator_inf_sylow_le_commutator
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) :
    (center G ⊓ _root_.commutator G) ⊓ (S : Subgroup G) ≤
      ⁅(S : Subgroup G), (S : Subgroup G)⁆ := by
  intro x hx
  have h := mem_sylow_commutator_of_mem_center_of_mem_commutator
    S ⟨x, hx.2⟩ hx.1.1 hx.1.2
  rw [← map_subtype_commutator]
  exact ⟨⟨x, hx.2⟩, h, rfl⟩

end Subgroup
