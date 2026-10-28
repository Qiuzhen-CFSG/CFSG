module

public import BenderSuzuki.SE.PermutationRegular
public import BenderSuzuki.SE.PermutationQuotient
public import Theory.GroupAction.NormalComplement

/-!
# Primitive-action obstructions for source 16.7

In an even primitive action, an odd normal subgroup fixes every point. Hence
an odd-normal-subgroup times involution-centralizer factorization is impossible
in degree at least three when that involution has no fixed point. The argument
uses the original action and does not require faithfulness.

Source: GLS IV, Chapter 2, Lemma 16.7, final paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section16.NativeSource
open Subgroup PFAppendixIII PFchapter1section1 MulAction
variable {H Ω : Type*} [Group H] [Finite H] [MulAction H Ω] [Finite Ω]

omit [Finite H] [Finite Ω] in
/-- The orbit index in a finite transitive action divides the group order. -/
public theorem transitive_card_dvd [IsPretransitive H Ω] (a : Ω) : Nat.card Ω ∣ Nat.card H := by
  rw [← index_stabilizer_of_transitive H a]
  exact (stabilizer H a).index_dvd_card

omit [Finite H] in
/-- An involution acting without fixed points makes the degree even. -/
public theorem even_card_of_free_involution {s : H} (hs : IsInvolution s)
    (hfree : ∀ a : Ω, s • a ≠ a) : Even (Nat.card Ω) := by
  have hP : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1) (by
    simp only [Nat.card_zpowers, orderOf_eq_prime hs.sq_eq_one hs.ne_one, pow_one])
  have hzero : Nat.card (fixedPoints (zpowers s) Ω) = 0 := by
    rw [Finite.card_eq_zero_iff]
    exact ⟨fun a => hfree a (mem_fixedPoints.mp a.property ⟨s, mem_zpowers s⟩)⟩
  have he := hP.card_modEq_card_fixedPoints Ω
  rw [hzero] at he
  exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp he)

omit [Finite H] [Finite Ω] in
/-- Odd normal subgroups act trivially at even primitive degree. -/
public theorem odd_normal_fixes_of_even [Nonempty Ω]
    (htwo : IsMultiplyPretransitive H Ω 2) (heven : Even (Nat.card Ω))
    (K : Subgroup H) [K.Normal] (hodd : Odd (Nat.card K)) :
    ∀ k : K, ∀ a : Ω, (k : H) • a = a := by
  let : IsPreprimitive H Ω := isPreprimitive_of_is_two_pretransitive htwo
  let : IsQuasiPreprimitive H Ω := IsPreprimitive.isQuasiPreprimitive
  have hfix : fixedPoints K Ω = Set.univ := by
    by_contra hn
    let : IsPretransitive K Ω := IsQuasiPreprimitive.isPretransitive_of_normal hn
    have ho : Odd (Nat.card Ω) := hodd.of_dvd_nat (transitive_card_dvd (Classical.choice ‹Nonempty Ω›))
    exact (Nat.not_even_iff_odd.mpr ho) heven
  intro k a
  exact mem_fixedPoints.mp (hfix ▸ Set.mem_univ a) k

omit [Finite H] in
/-- The odd-core factorization from Z-star contradicts a free involution in
a doubly transitive action of degree at least three. -/
public theorem no_free_involution_of_odd_factor
    (htwo : IsMultiplyPretransitive H Ω 2) (hthree : 3 ≤ Nat.card Ω)
    {s : H} (hs : IsInvolution s) (hfree : ∀ a : Ω, s • a ≠ a)
    (K : Subgroup H) [K.Normal] (hodd : Odd (Nat.card K))
    (hfactor : K ⊔ centralizer ({s} : Set H) = ⊤) : False := by
  let : Nonempty Ω := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card Ω)).1
  have hkfix := odd_normal_fixes_of_even htwo (even_card_of_free_involution hs hfree) K hodd
  have hcomm (g : H) (a : Ω) : s • (g • a) = g • (s • a) := by
    obtain ⟨k, hk, c, hc, rfl⟩ := mem_sup_of_normal_left.mp
      (show g ∈ K ⊔ centralizer ({s} : Set H) by rw [hfactor]; trivial)
    have hcs := mem_centralizer_singleton_iff.mp hc
    simp only [mul_smul, hkfix ⟨k, hk⟩]
    rw [← mul_smul, ← mul_smul, hcs]
  let a : Ω := Classical.choice inferInstance
  have hcard : (3 : Cardinal) ≤ Cardinal.mk Ω := by
    rw [← Nat.cast_card]
    exact_mod_cast hthree
  obtain ⟨b, hba, hbs⟩ := Cardinal.exists_ne_ne_of_three_le hcard a (s • a)
  obtain ⟨g, hga, hgs⟩ := is_two_pretransitive_iff.mp htwo
    (hfree a).symm hba.symm
  have hh := hcomm g a
  rw [hga, hgs] at hh
  exact hbs hh.symm

end BenderSuzuki.ZD.Section16.NativeSource
