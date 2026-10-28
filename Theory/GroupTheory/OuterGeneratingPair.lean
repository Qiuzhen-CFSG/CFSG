module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.PGroup

/-!
# Outer automorphisms from a generating pair

Suppose that, after an inner adjustment, every automorphism fixes one member
of a generating pair and fixes or inverts the other. The adjusted automorphism
squares to the identity on both generators, hence on the whole group. Inner
adjustments disappear in the outer quotient, so that quotient is a two-group.

This elementary reduction is useful for proving full automorphism bounds from
simultaneous conjugacy calculations. Its Hall--Janko application concerns the
outer-group entry in GLS, Volume 3, Table 5.3g. No finiteness, simplicity, or
existence of an automorphism inverting the second generator is required.
-/

public section
namespace MulAut
variable {G : Type*} [Group G]

/-- Fixing the first generator and fixing or inverting the second forces the
square of an automorphism to be the identity. -/
theorem square_eq_one_of_generating_pair (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (f : MulAut G) (ha : f a = a) (hb : f b = b ∨ f b = b⁻¹) :
    f ^ 2 = 1 := by
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense hgen
  intro x hx
  rcases Set.mem_insert_iff.mp hx with hx | hx
  · subst x
    change f (f a) = a
    rw [ha, ha]
  · rw [Set.mem_singleton_iff] at hx
    subst x
    change f (f b) = b
    rcases hb with hb | hb
    · rw [hb, hb]
    · rw [hb, map_inv, hb, inv_inv]

/-- A simultaneous conjugacy calculation for the images of two generators
controls the quotient of the full automorphism group by inner automorphisms. -/
theorem outer_isPGroup_two_of_generating_pair (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (h : ∀ f : MulAut G, ∃ g : G, f a = MulAut.conj g a ∧
      (f b = MulAut.conj g b ∨ f b = MulAut.conj g b⁻¹)) :
    IsPGroup 2 (MulAut.Outer G) := by
  intro z
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup G) z
  obtain ⟨g, ha, hb⟩ := h f
  let k : MulAut G := (MulAut.conj g)⁻¹ * f
  have hka : k a = a := by simp [k, MulAut.mul_apply, ha, mul_assoc]
  have hkb : k b = b ∨ k b = b⁻¹ := by
    rcases hb with hb | hb
    · exact Or.inl (by simp [k, MulAut.mul_apply, hb, mul_assoc])
    · exact Or.inr (by simp [k, MulAut.mul_apply, hb, mul_assoc])
  have hk := square_eq_one_of_generating_pair a b hgen k hka hkb
  let q := QuotientGroup.mk' (innerSubgroup G)
  have hqg : q (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff (MulAut.conj g)).mpr ⟨g, rfl⟩
  have hqk : q k = q f := by simp [k, map_mul, map_inv, hqg]
  refine ⟨1, ?_⟩
  change q f ^ 2 = 1
  rw [← hqk, ← map_pow, hk, map_one]

end MulAut
