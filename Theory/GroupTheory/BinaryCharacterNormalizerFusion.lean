module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Binary character values under a normalizer

Suppose a binary character on a subgroup `S` detects membership in `R`
on elements of another subgroup `Q`. A conjugation preserving both `Q`
and `R` preserves the character values of elements of `S` lying in `Q`.
Indeed, the conjugation preserves whether the character is one, and the
target group has only one other element. The same two-element argument shows
that every automorphism fixes a binary character with characteristic kernel.

This is the local normalizer step in the transfer analysis following
Stellmacher (10.1)(b). It supplies no ambient fusion control: the
conjugating element must normalize the two specified subgroups.
-/

namespace Subgroup

/-- An automorphism fixes a binary character whose kernel is characteristic. -/
public theorem binary_character_apply_eq_of_characteristic_kernel
    {H : Type*} [Group H] (χ : H →* Multiplicative (ZMod 2))
    [χ.ker.Characteristic] (f : MulAut H) (x : H) : χ (f x) = χ x := by
  have hone : χ (f x) = 1 ↔ χ x = 1 := by
    change x ∈ χ.ker.comap f.toMonoidHom ↔ x ∈ χ.ker
    rw [characteristic_iff_comap_eq.mp inferInstance f]
  by_cases hx : χ x = 1
  · exact (hone.mpr hx).trans hx.symm
  · have hfx : χ (f x) ≠ 1 := fun h => hx (hone.mp h)
    obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : Multiplicative (ZMod 2))).mp
      (by simp : Nat.card (Multiplicative (ZMod 2)) = 2)
    exact (ha (χ (f x)) hfx).trans (ha (χ x) hx).symm

/-- A binary character detecting `R` on `Q` respects conjugations that
normalize both subgroups, when both endpoints belong to its domain. -/
public theorem binary_character_eq_of_normalizer_conjugation
    {G : Type*} [Group G] (S Q R : Subgroup G)
    (χ : S →* Multiplicative (ZMod 2))
    (hχ : ∀ s : S, (s : G) ∈ Q → (χ s = 1 ↔ (s : G) ∈ R))
    (x y : S) (hx : (x : G) ∈ Q) (g : G)
    (hgQ : g ∈ normalizer (Q : Set G))
    (hgR : g ∈ normalizer (R : Set G))
    (hxy : g * (x : G) * g⁻¹ = (y : G)) : χ y = χ x := by
  have hy : (y : G) ∈ Q := by
    rw [← hxy]
    exact (mem_normalizer_iff.mp hgQ (x : G)).mp hx
  have hmem : (x : G) ∈ R ↔ (y : G) ∈ R := by
    rw [← hxy]
    exact mem_normalizer_iff.mp hgR (x : G)
  have hone : χ x = 1 ↔ χ y = 1 := (hχ x hx).trans (hmem.trans (hχ y hy).symm)
  by_cases hxone : χ x = 1
  · exact (hone.mp hxone).trans hxone.symm
  · have hyone : χ y ≠ 1 := fun h => hxone (hone.mpr h)
    obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : Multiplicative (ZMod 2))).mp
      (by simp : Nat.card (Multiplicative (ZMod 2)) = 2)
    exact (ha (χ y) hyone).trans (ha (χ x) hxone).symm

end Subgroup
