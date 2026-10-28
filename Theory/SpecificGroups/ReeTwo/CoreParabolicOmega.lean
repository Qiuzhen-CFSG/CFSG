module

public import Theory.SpecificGroups.ReeTwo.CoreParabolicStructure
public import Theory.SpecificGroups.ReeTwo.CoreCharacterKernel

/-!
# The extra characteristic subgroup in the full Ree core

The first omega subgroup has order 512 and lies strictly between the derived
subgroup and the full order-1024 core. It intersects the order-64 derived
centralizer in the derived subgroup and joins it to the full core.
Consequently it is a genuine extra invariant subgroup, not one of the two
cases in the unrepaired dichotomy from quasithin Lemma 14.2.21.

The proof uses the intrinsic omega/binary-character identification and the
explicit centralizer coordinates. It does not identify this subgroup with
an ambient Tits parabolic core; that requires a compatible embedding.
Source: Shinoda (1975), (2.3), pp.81–82, through `CoreCharacterKernel`.
-/

@[expose] public section
namespace ReeTwo.Core
open Subgroup

/-- The characteristic index-two core has order 512. -/
theorem omega_card : Nat.card (omega₁ Core (p := 2)) = 512 := by
  have hs : Function.Surjective binaryCharacter := by
    intro t
    refine ⟨⟨0,0,t.toAdd,0,0,0,0,0,0,0⟩, ?_⟩
    simp [binaryCharacter]
  have hc : Nat.card (Core ⧸ binaryCharacter.ker) = 2 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective binaryCharacter hs).toEquiv]
    change Nat.card (ZMod 2) = 2
    simp
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup binaryCharacter.ker
  rw [card, hc, binaryCharacter_ker_eq_omega] at h
  omega

/-- Its intersection with the derived centralizer is exactly the derived subgroup. -/
theorem omega_inf_centralizer_derived :
    omega₁ Core (p := 2) ⊓ centralizer (commutator Core : Set Core) =
      commutator Core := by
  ext x
  rw [← binaryCharacter_ker_eq_omega, mem_inf, mem_centralizer_derived_iff, mem_derived_iff]
  change (x.b1 + x.b2 + x.b3 = 0 ∧ _) ↔ _
  constructor
  · rintro ⟨hb,h0,h1,h3,h4⟩
    simp only [h1,h3,zero_add,add_zero] at hb
    exact ⟨h0,h1,hb,h3,h4⟩
  · rintro ⟨h0,h1,h2,h3,h4⟩
    exact ⟨by simp [h1,h2,h3],h0,h1,h3,h4⟩

/-- Together with the derived centralizer it generates the full core. -/
theorem omega_sup_centralizer_derived :
    omega₁ Core (p := 2) ⊔ centralizer (commutator Core : Set Core) = ⊤ := by
  apply top_unique
  intro x _
  let z := root 2 ^ (binaryCharacter x).toAdd.val
  have hz : binaryCharacter z = binaryCharacter x :=
    (by decide +kernel : ∀ t : FiveFour.Cyclic 2,
      binaryCharacter (root 2 ^ t.toAdd.val) = t) _
  have hy : z⁻¹ * x ∈ omega₁ Core (p := 2) := by
    rw [← binaryCharacter_ker_eq_omega]
    change binaryCharacter (z⁻¹ * x) = 1
    rw [map_mul, map_inv, hz, _root_.inv_mul_cancel]
  have hzF : z ∈ centralizer (commutator Core : Set Core) :=
    pow_mem root_two_mem_centralizer_derived _
  have h1 : z ∈ omega₁ Core (p := 2) ⊔ centralizer (commutator Core : Set Core) :=
    (show centralizer (commutator Core : Set Core) ≤ _ from le_sup_right) hzF
  have h2 : z⁻¹ * x ∈ omega₁ Core (p := 2) ⊔ centralizer (commutator Core : Set Core) :=
    (show omega₁ Core (p := 2) ≤ _ from le_sup_left) hy
  simpa only [mul_inv_cancel_left] using mul_mem h1 h2

/-- The omega subgroup strictly contains the derived subgroup. -/
theorem derived_lt_omega : commutator Core < omega₁ Core (p := 2) := by
  apply lt_of_le_of_ne
  · rw [← omega_inf_centralizer_derived]
    exact inf_le_left
  · intro he
    have hm : root 0 ∈ omega₁ Core (p := 2) := by
      rw [← binaryCharacter_ker_eq_omega]
      change binaryCharacter (root 0) = 1
      decide +kernel
    rw [← he, mem_derived_iff] at hm
    exact (by decide : (1 : ZMod 2) ≠ 0) hm.1

/-- The omega subgroup is proper in the full core. -/
theorem omega_lt_top : omega₁ Core (p := 2) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  have hm : root 2 ∈ omega₁ Core (p := 2) := he ▸ mem_top _
  rw [← binaryCharacter_ker_eq_omega] at hm
  exact (by decide +kernel : binaryCharacter (root 2) ≠ 1) hm

/-- The extra characteristic subgroup is distinct from the derived centralizer. -/
theorem omega_ne_centralizer_derived : omega₁ Core (p := 2) ≠
    centralizer (commutator Core : Set Core) := by
  intro he
  have hc := omega_card
  rw [he, centralizer_derived_card] at hc
  omega

end ReeTwo.Core
