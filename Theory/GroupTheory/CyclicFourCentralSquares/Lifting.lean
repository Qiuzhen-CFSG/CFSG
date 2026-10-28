module

public import Theory.GroupTheory.CyclicFourCentralSquares

/-!
# Lifting containment of a cyclic quartic center through its square quotient

If the image of the center in the quotient by its squares lies in the image
of a subgroup, the whole center already lies in that subgroup. Indeed, its
intersection with the center supplements the squares, which lie in the
Frattini subgroup of the center. Frattini nongeneration finishes the proof.

This is the lifting step from the binary residual calculation to the quartic
case of Aschbacher–Smith I.2.2(6a), printed pp.410 and 412. The subgroup need
not be normal. In fact its use here only requires the center to have order four.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Containment of the center lifts through its square quotient. -/
theorem center_le_of_centralSquares_image_le (hZ : Nat.card (center G) = 4)
    (A : Subgroup G)
    (h : (center G).map (QuotientGroup.mk' (centralSquares G)) ≤
      A.map (QuotientGroup.mk' (centralSquares G))) : center G ≤ A := by
  let q := QuotientGroup.mk' (centralSquares G)
  let : Fact (IsPGroup 2 (center G)) :=
    ⟨IsPGroup.of_card (n := 2) (by simpa using hZ)⟩
  have htop : A.subgroupOf (center G) ⊔ frattini (center G) = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨a, ha, he⟩ := h (mem_map.mpr ⟨z, z.property, rfl⟩)
    have hs : (z : G) * a⁻¹ ∈ centralSquares G := by
      apply (QuotientGroup.eq_one_iff (N := centralSquares G) _).mp
      change q ((z : G) * a⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have haZ : a ∈ center G := by
      have := (center G).mul_mem_cancel_left z.property |>.mp (centralSquares_le_center hs)
      simpa using (center G).inv_mem this
    obtain ⟨w, hw⟩ := mem_centralSquares.mp hs
    let aZ : center G := ⟨a, haZ⟩
    have hz : z = w ^ 2 * aZ := by
      apply Subtype.ext
      change (z : G) = (w : G) ^ 2 * a
      rw [hw, inv_mul_cancel_right]
    rw [hz]
    exact (A.subgroupOf (center G) ⊔ frattini (center G)).mul_mem
      (mem_sup_right (pth_power_mem_frattini_of_isPGroup (p := 2) w))
      (mem_sup_left ha)
  have ht := frattini_nongenerating htop
  intro z hz
  exact (show (⟨z, hz⟩ : center G) ∈ A.subgroupOf (center G) from ht ▸ mem_top _)

end Subgroup
