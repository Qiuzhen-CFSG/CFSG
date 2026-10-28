module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.IntervalCases

/-!
# Centralizing one endpoint of a cubic pair in SL₂(3)

For nonidentity cubic elements x and y in SL₂(3), exactly one of xy and
xy⁻¹ has fourth power one. The finite matrix calculation therefore excludes
an automorphism that fixes x and inverts y. Since the two nonidentity elements
of an order-three subgroup are mutual inverses, an automorphism fixing one
cubic subgroup pointwise and preserving the other fixes the latter pointwise.

We apply this to the conjugation action on the literal ambient join. This is
the small-group calculation used in Aschbacher, *Sporadic Groups* (1994),
47.6, printed p.264, to identify C_L(U) with the pair normalizer inside L.
No assertion about the ambient Sylow two-subgroup being semidihedral is used.
-/

public section
namespace Theory.SpecificGroups.SL2.CubicPairCentralizer

abbrev SL23 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)
private theorem cubic_fourth_power : ∀ x y : SL23, x ≠ 1 → x ^ 3 = 1 → y ≠ 1 → y ^ 3 = 1 →
    ((x * y) ^ 4 = 1 ↔ (x * y⁻¹) ^ 4 ≠ 1) := by
  decide +kernel

open Subgroup
private lemma three_elements {H : Type*} [Group H] [Finite H] (hc : Nat.card H = 3)
    {x y : H} (hx : x ≠ 1) (hy : y ≠ 1) : y = x ∨ y = x⁻¹ := by
  classical
  have hz := zpowers_eq_top_of_prime_card hc hx
  have ho : orderOf x = 3 := (orderOf_eq_card_of_zpowers_eq_top hz).trans hc
  have hm := (mem_zpowers_iff_mem_range_orderOf (x := x) (y := y)).mp
    (hz ▸ (mem_top y))
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  rw [Finset.mem_range, ho] at hn
  interval_cases n
  · exact (hy (pow_zero x)).elim
  · exact Or.inl (pow_one x)
  · right
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [← pow_succ, ho] using pow_orderOf_eq_one x

private lemma not_fix_and_invert {H : Type*} [Group H] (e : H ≃* SL23)
    (f : MulAut H) (x y : H) (hx : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hy : y ≠ 1) (hy3 : y ^ 3 = 1) (hfx : f x = x) : f y ≠ y⁻¹ := by
  intro hfy
  have hmodel := cubic_fourth_power (e x) (e y)
    (fun h => hx (e.injective (h.trans e.map_one.symm)))
    (by rw [← map_pow, hx3, map_one])
    (fun h => hy (e.injective (h.trans e.map_one.symm)))
    (by rw [← map_pow, hy3, map_one])
  have hsep : (x * y) ^ 4 = 1 ↔ (x * y⁻¹) ^ 4 ≠ 1 := by
    simpa only [← map_inv, ← map_mul, ← map_pow, e.map_eq_one_iff, not_congr e.map_eq_one_iff] using hmodel
  have he : (x * y) ^ 4 = 1 ↔ (x * y⁻¹) ^ 4 = 1 := by
    have hh := f.map_eq_one_iff (x := (x * y) ^ 4)
    rw [map_pow, map_mul, hfx, hfy] at hh
    exact hh.symm
  exact (iff_not_self ((he.symm).trans hsep)).elim

/-- Centralizing one cubic subgroup while normalizing the other centralizes both
when their literal join is SL₂(3). -/
theorem pair_centralizes {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (e : (A ⊔ B : Subgroup G) ≃* SL23) :
    centralizer (A : Set G) ⊓ normalizer (B : Set G) ≤ centralizer (B : Set G) := by
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : A)
  intro g hg
  have hgJ : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    A.normalizer_inf_normalizer_le_normalizer_sup B
      ⟨centralizer_le_normalizer _ hg.1, hg.2⟩
  let f : MulAut (A ⊔ B : Subgroup G) := (A ⊔ B).normalizerMonoidHom ⟨g, hgJ⟩
  let xJ : (A ⊔ B : Subgroup G) := ⟨x, mem_sup_left x.property⟩
  have hfx : f xJ = xJ := by
    apply Subtype.ext
    change g * (x : G) * g⁻¹ = x
    rw [← mem_centralizer_iff.mp hg.1 x x.property, mul_inv_cancel_right]
  apply mem_centralizer_iff.mpr
  intro y hy
  by_cases hy1 : y = 1
  · simp [hy1]
  let yB : B := ⟨y, hy⟩
  let fB : MulAut B := B.normalizerMonoidHom ⟨g, hg.2⟩
  have hyB : yB ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hfyB : fB yB ≠ 1 := fun h => hyB (fB.injective (h.trans fB.map_one.symm))
  rcases three_elements hB hyB hfyB with hfix | hinv
  · have hh := congrArg Subtype.val hfix
    change g * y * g⁻¹ = y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · let yJ : (A ⊔ B : Subgroup G) := ⟨y, mem_sup_right hy⟩
    apply False.elim
    apply not_fix_and_invert e f xJ yJ
      (fun h => hx (Subtype.ext (congrArg (fun z : (A ⊔ B : Subgroup G) => (z : G)) h)))
      (Subtype.ext (by
        have hh := congrArg Subtype.val (pow_card_eq_one' (x := x))
        simpa only [hA, Subgroup.coe_pow, Subgroup.coe_one] using hh))
      (fun h => hy1 (congrArg Subtype.val h))
      (Subtype.ext (by
        have hh := congrArg Subtype.val (pow_card_eq_one' (x := yB))
        simpa only [hB, Subgroup.coe_pow, Subgroup.coe_one] using hh)) hfx
    exact Subtype.ext (congrArg (fun z : B => (z : G)) hinv)

end Theory.SpecificGroups.SL2.CubicPairCentralizer
