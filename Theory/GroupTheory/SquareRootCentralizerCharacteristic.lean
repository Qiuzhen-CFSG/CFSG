module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Recognizing a characteristic element by its square roots

Automorphisms preserve centralizer cardinalities. A nonidentity central element
is therefore fixed if its square roots all have one centralizer size, while
every other nonidentity central element has a square root with a different
size. This packages the intrinsic argument used for the Ree first cores.

Source: the elementary invariance of commutation and powers under group
isomorphisms; the motivating coordinate certificate is `RootTwistedFirstCore`.
-/

namespace Group

/-- The cardinality of the set of elements commuting with `x`. -/
public noncomputable def commutingCard {G : Type*} [Group G] (x : G) : ℕ :=
  Nat.card {y : G // y * x = x * y}

/-- Isomorphisms preserve the centralizer cardinality. -/
public theorem commutingCard_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) : commutingCard (e x) = commutingCard x := by
  symm
  apply Nat.card_congr
  refine e.toEquiv.subtypeEquiv ?_
  intro y
  change y * x = x * y ↔ e y * e x = e x * e y
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

/-- Square-root centralizer sizes distinguish a central mark intrinsically. -/
public theorem fixed_of_square_root_commutingCard {G : Type*} [Group G]
    (z : G) (n : ℕ) (hz : z ∈ Subgroup.center G) (hz1 : z ≠ 1)
    (hroots : ∀ y : G, y ^ 2 = z → commutingCard y = n)
    (hother : ∀ x : G, x ∈ Subgroup.center G → x ≠ 1 → x ≠ z →
      ∃ y : G, y ^ 2 = x ∧ commutingCard y ≠ n)
    (a : MulAut G) : a z = z := by
  have hc : a z ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := a.surjective y
    simpa only [map_mul] using congrArg a (Subgroup.mem_center_iff.mp hz x)
  have hn : a z ≠ 1 := by
    intro h
    apply hz1
    apply a.injective
    simpa only [map_one] using h
  by_contra he
  obtain ⟨y, hy, hncard⟩ := hother (a z) hc hn he
  have hs : (a.symm y) ^ 2 = z := by
    rw [← map_pow, hy, a.symm_apply_apply]
  have hh := hroots (a.symm y) hs
  rw [commutingCard_equiv] at hh
  exact hncard hh

end Group
