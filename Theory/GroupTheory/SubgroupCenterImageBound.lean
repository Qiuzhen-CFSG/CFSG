module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Recovering a subgroup from a full-size image

If W lies in A, meets the kernel of f trivially, and has at least as many
elements as f(A), then A is contained in ker(f)W. Applied to a subgroup
center, this recovers the center from an embedded subgroup whose image fills
the center downstairs. Surjectivity of f on the whole ambient group is not
needed.

This is the elementary finite-group argument used for central covers in
Aschbacher–Smith, E.6.11(3b), printed pp.249–250.
-/

public section

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite H]

theorem le_ker_sup_of_disjoint_of_card (f : G →* H) {W A : Subgroup G}
    (hWA : W ≤ A) (hker : W ⊓ f.ker = ⊥)
    (hcard : Nat.card (A.map f) ≤ Nat.card W) : A ≤ f.ker ⊔ W := by
  have hinj : Function.Injective (f.subgroupMap W) := by
    intro x y hxy
    apply inv_mul_eq_one.mp
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hker]
    refine ⟨W.mul_mem (W.inv_mem x.property) y.property, ?_⟩
    change f ((x : G)⁻¹ * (y : G)) = 1
    rw [map_mul, map_inv, show f (x : G) = f (y : G) from congrArg Subtype.val hxy]
    exact inv_mul_cancel _
  have he : Nat.card (W.map f) = Nat.card W :=
    (Nat.card_congr (MulEquiv.ofBijective (f.subgroupMap W)
      ⟨hinj, f.subgroupMap_surjective W⟩).toEquiv).symm
  have himage : W.map f = A.map f :=
    eq_of_le_of_card_ge (map_mono hWA) (he ▸ hcard)
  intro a ha
  obtain ⟨w, hw, hfw⟩ := himage.symm ▸ mem_map_of_mem f ha
  have hk : a * w⁻¹ ∈ f.ker := by
    change f (a * w⁻¹) = 1
    rw [map_mul, map_inv, hfw, mul_inv_cancel]
  have hm := (f.ker ⊔ W).mul_mem (mem_sup_left hk) (mem_sup_right hw)
  simpa only [inv_mul_cancel_right] using hm

omit [Finite H] in
/-- A homomorphism maps the relative center into the relative image center. -/
theorem map_subgroup_center_le (f : G →* H) (S : Subgroup G) :
    ((center S).map S.subtype).map f ≤ (center (S.map f)).map (S.map f).subtype := by
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨⟨f z, mem_map_of_mem f z.property⟩, mem_center_iff.mpr ?_, rfl⟩
  rintro ⟨_, y, hy, rfl⟩
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, map_mul] using
    congrArg f (congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩))

omit [Finite H] in
/-- An injective homomorphism preserves relative centers exactly. -/
theorem map_subgroup_center_eq (f : G →* H) (hf : Function.Injective f)
    (S : Subgroup G) :
    ((center S).map S.subtype).map f = (center (S.map f)).map (S.map f).subtype := by
  apply le_antisymm (map_subgroup_center_le f S)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨s, hs, he⟩ := z.property
  refine ⟨s, ⟨⟨s, hs⟩, mem_center_iff.mpr ?_, rfl⟩, he⟩
  intro t
  apply Subtype.ext
  apply hf
  have hh := congrArg Subtype.val
    (mem_center_iff.mp hz ⟨f t, mem_map_of_mem f t.property⟩)
  simpa only [Subgroup.coe_mul, map_mul, he] using hh

/-- A subgroup of the relative center filling the center downstairs accounts
for the whole relative center modulo the kernel. -/
theorem center_le_ker_sup_of_disjoint_of_card (f : G →* H)
    (S W : Subgroup G) (hW : W ≤ (center S).map S.subtype)
    (hker : W ⊓ f.ker = ⊥) (hcard : Nat.card (center (S.map f)) ≤ Nat.card W) :
    (center S).map S.subtype ≤ f.ker ⊔ W := by
  apply le_ker_sup_of_disjoint_of_card f hW hker
  exact (card_le_of_le (map_subgroup_center_le f S)).trans
    ((card_map_of_injective (S.map f).subtype_injective).le.trans hcard)

end Subgroup
