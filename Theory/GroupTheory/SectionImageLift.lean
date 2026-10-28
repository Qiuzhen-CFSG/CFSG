module
public import Mathlib.GroupTheory.Index

/-!
# Lifting subgroup images through a marked section

A section map with kernel Z detects containment after adjoining Z. Restricting
that map to a subgroup containing Z gives its order as the product of the
image order and the kernel order. These statements use the literal subgroup
inclusions, so they also apply to commutator subgroups inside a module support.
-/

public section

open Subgroup
namespace Subgroup
variable {G A : Type*} [Group G] [Group A]

theorem le_of_section_image_le {B Z W K : Subgroup G}
    (q : B →* A) (hk : q.ker = Z.subgroupOf B)
    (hWB : W ≤ B) (hZK : Z ≤ K)
    (hi : (W.subgroupOf B).map q ≤ (K.subgroupOf B).map q) : W ≤ K := by
  have h : W.subgroupOf B ≤ K.subgroupOf B := by
    have hker : q.ker ≤ K.subgroupOf B := by
      rw [hk]
      exact subgroupOf_mono B hZK
    simpa only [sup_of_le_left hker] using (map_le_map_iff.mp hi)
  intro w hw
  exact h (show (⟨w,hWB hw⟩ : B) ∈ W.subgroupOf B from hw)

theorem mem_of_section_image_mem {B Z W : Subgroup G}
    (q : B →* A) (hk : q.ker = Z.subgroupOf B) (hZW : Z ≤ W)
    (b : B) (hb : q b ∈ (W.subgroupOf B).map q) : (b : G) ∈ W := by
  obtain ⟨w,hw,he⟩ := hb
  have hz : (b * w⁻¹ : B) ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hzw : (b : G) * (w : G)⁻¹ ∈ Z := by
    simpa only [hk, mem_subgroupOf, coe_mul, coe_inv] using hz
  simpa using W.mul_mem (hZW hzw) hw

theorem card_eq_section_image_mul_kernel [Finite G]
    {B Z W : Subgroup G} (q : B →* A) (hk : q.ker = Z.subgroupOf B)
    (hWB : W ≤ B) (hZW : Z ≤ W) :
    Nat.card W = Nat.card ((W.subgroupOf B).map q) * Nat.card Z := by
  let f : W →* A := q.comp (inclusion hWB)
  have hfk : f.ker = Z.subgroupOf W := by
    ext w
    change inclusion hWB w ∈ q.ker ↔ (w : G) ∈ Z
    rw [hk]
    rfl
  have hfr : f.range = (W.subgroupOf B).map q := by
    ext a
    constructor
    · rintro ⟨w,rfl⟩
      exact ⟨inclusion hWB w,w.property,rfl⟩
    · rintro ⟨w,hw,rfl⟩
      exact ⟨⟨w,hw⟩,rfl⟩
  rw [card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hfr, hfk,
    Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv]

end Subgroup
