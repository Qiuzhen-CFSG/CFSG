module
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Scalar action of a nonnormal cubic normalizer

A nonnormal cubic in S₃×S₃ has nontrivial projections onto both factors.
Its normalizer either fixes or inverts a generator, forcing the same sign
on both coordinates of the entire cubic residual. The finite checks are
only identities between individual permutations of three letters.

Source application: Aschbacher--Smith15.2.21(3), printed p.1114,
refs/quasithin.pdf, through SmallActionsSource.ExtraspecialAction.
-/

public section
open Subgroup
namespace SymmetricThreeProductResidual
local notation "A" => Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)
private theorem coordinate_cubic_conjugate : ∀ r y : Equiv.Perm (Fin 3),
    y ^ 3 = 1 → r * y * r⁻¹ = y ∨ r * y * r⁻¹ = y⁻¹ := by decide +kernel
private theorem coordinate_cubic_fixed : ∀ r y : Equiv.Perm (Fin 3),
    y ^ 3 = 1 → y ≠ 1 → r * y * r⁻¹ = y →
      ∀ z : Equiv.Perm (Fin 3), z ^ 3 = 1 → r * z * r⁻¹ = z := by decide +kernel
private theorem coordinate_cubic_inverted : ∀ r y : Equiv.Perm (Fin 3),
    y ^ 3 = 1 → y ≠ 1 → r * y * r⁻¹ = y⁻¹ →
      ∀ z : Equiv.Perm (Fin 3), z ^ 3 = 1 → r * z * r⁻¹ = z⁻¹ := by decide +kernel
private theorem normal_cubic_axis (y : A) (h3 : y ^ 3 = 1)
    (haxis : y.1 = 1 ∨ y.2 = 1) : (zpowers y).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  apply le_normalizer_iff.mpr
  intro r _ x hx
  obtain ⟨k,rfl⟩ := mem_zpowers_iff.mp hx
  have hh : r * y * r⁻¹ ∈ zpowers y := by
    rcases haxis with h | h
    · rcases coordinate_cubic_conjugate r.2 y.2 (congrArg Prod.snd h3) with hc | hc
      · have he : r * y * r⁻¹ = y := Prod.ext (by simp [h]) hc
        rw [he]; exact mem_zpowers y
      · have he : r * y * r⁻¹ = y⁻¹ := Prod.ext (by simp [h]) hc
        rw [he]; exact inv_mem (mem_zpowers y)
    · rcases coordinate_cubic_conjugate r.1 y.1 (congrArg Prod.fst h3) with hc | hc
      · have he : r * y * r⁻¹ = y := Prod.ext hc (by simp [h])
        rw [he]; exact mem_zpowers y
      · have he : r * y * r⁻¹ = y⁻¹ := Prod.ext hc (by simp [h])
        rw [he]; exact inv_mem (mem_zpowers y)
  change (MulAut.conj r) (y ^ k) ∈ zpowers y
  rw [map_zpow]
  exact (zpowers y).zpow_mem hh k

private theorem cubic_member {D : Type*} [Group D] [Finite D]
    (hc : Nat.card D = 3) (y : D) (hy : y ≠ 1) (z : D) :
    z = 1 ∨ z = y ∨ z = y⁻¹ := by
  classical
  have ho : orderOf y = 3 := orderOf_eq_prime (hc ▸ pow_card_eq_one' (x := y)) hy
  have hm := mem_zpowers_iff_mem_range_orderOf.mp (mem_zpowers_of_prime_card hc hy (g' := z))
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
  have hn := Finset.mem_range.mp hn
  rw [ho] at hn
  interval_cases n
  · exact Or.inl (he ▸ pow_zero y)
  · exact Or.inr (Or.inl (he ▸ pow_one y))
  · right; right
    rw [← he]
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [←pow_succ] using (show y ^ 3 = 1 from hc ▸ pow_card_eq_one' (x := y))

/-- The normalizer of a nonnormal cubic in S₃×S₃ acts by a scalar sign
on the full cubic residual. The identity action is allowed for kernel elements. -/
theorem normalizer_cubic_scalar (B : Subgroup A) (hc : Nat.card B = 3)
    (hn : ¬ B.Normal) (r : A) (hr : r ∈ normalizer (B : Set A)) :
    (∀ z : A, z ^ 3 = 1 → r * z * r⁻¹ = z) ∨
      (∀ z : A, z ^ 3 = 1 → r * z * r⁻¹ = z⁻¹) := by
  classical
  have hne : B ≠ ⊥ := by intro he; simp [he] at hc
  obtain ⟨y,hy,hy1⟩ := B.bot_or_exists_ne_one.resolve_left hne
  have hy3 : y ^ 3 = 1 := congrArg Subtype.val (hc ▸ pow_card_eq_one' (x := (⟨y,hy⟩ : B)))
  have hygen : zpowers y = B := by
    have hh := congrArg (map B.subtype) (zpowers_eq_top_of_prime_card hc
      (g := (⟨y,hy⟩ : B)) (fun h => hy1 (congrArg Subtype.val h)))
    simpa only [MonoidHom.map_zpowers, coe_subtype, ← MonoidHom.range_eq_map, range_subtype] using hh
  have ha : y.1 ≠ 1 := fun h => hn (hygen ▸ normal_cubic_axis y hy3 (Or.inl h))
  have hb : y.2 ≠ 1 := fun h => hn (hygen ▸ normal_cubic_axis y hy3 (Or.inr h))
  have hmem : r * y * r⁻¹ ∈ B := (mem_normalizer_iff.mp hr y).mp hy
  rcases cubic_member hc (⟨y,hy⟩ : B) (fun h => hy1 (congrArg Subtype.val h))
    ⟨r*y*r⁻¹,hmem⟩ with he | he | he
  · have hh : r*y*r⁻¹ = 1 := congrArg Subtype.val he
    exact (hy1 ((MulAut.conj r).injective (hh.trans (map_one _).symm))).elim
  · left
    intro z hz
    have he' := congrArg Subtype.val he
    exact Prod.ext
      (coordinate_cubic_fixed r.1 y.1 (congrArg Prod.fst hy3) ha (congrArg Prod.fst he') z.1 (congrArg Prod.fst hz))
      (coordinate_cubic_fixed r.2 y.2 (congrArg Prod.snd hy3) hb (congrArg Prod.snd he') z.2 (congrArg Prod.snd hz))
  · right
    intro z hz
    have he' := congrArg Subtype.val he
    exact Prod.ext
      (coordinate_cubic_inverted r.1 y.1 (congrArg Prod.fst hy3) ha (congrArg Prod.fst he') z.1 (congrArg Prod.fst hz))
      (coordinate_cubic_inverted r.2 y.2 (congrArg Prod.snd hy3) hb (congrArg Prod.snd he') z.2 (congrArg Prod.snd hz))
end SymmetricThreeProductResidual
