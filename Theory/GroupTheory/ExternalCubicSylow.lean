module

public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupTheory.SubgroupConjugation

/-!
# External cubics permuting with a two-subgroup

Let K be normal, x an element of order three outside K, and T a two-subgroup.
If ⟨x⟩T is a subgroup, its intersection with K is exactly T ∩ K, and x
normalizes that intersection. This follows by passing to the quotient by K:
the images of ⟨x⟩ and T have coprime orders.

An order-three element with odd centralizer cannot normalize a two-subgroup
whose order is not one modulo three. Conjugation orbit counting proves this
without confusing normalization of the two-subgroup with normalization of
⟨x⟩. These are the elementary steps in the unitary case of
Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.20, p.955.
-/

public section
namespace Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- An external cubic permuting with T normalizes the intersection T ∩ K.
The product equality asserts that the setwise product is the generated subgroup. -/
theorem external_cubic_normalizes_intersection
    (K T : Subgroup G) [K.Normal] (hT : IsPGroup 2 T)
    (x : G) (hx : orderOf x = 3) (hxK : x ∉ K)
    (hprod : ((zpowers x ⊔ T : Subgroup G) : Set G) = (zpowers x : Set G) * T) :
    x ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  let q := QuotientGroup.mk' K
  have hA : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hx)
  have hd : Disjoint ((zpowers x).map q) (T.map q) :=
    (hA.map q).disjoint_of_coprime (hT.map q) (by decide)
  have hAK : Disjoint (zpowers x) K := by
    apply disjoint_def.mpr
    intro a ha hKa
    by_contra ha1
    have ha1' : (⟨a, ha⟩ : zpowers x) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    have hgen : (⟨x, mem_zpowers x⟩ : zpowers x) ∈ zpowers (⟨a, ha⟩ : zpowers x) :=
      mem_zpowers_of_prime_card
        (show Nat.card (zpowers x) = 3 from (Nat.card_zpowers x).trans hx) ha1'
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hgen
    have hn' : a ^ n = x := congrArg Subtype.val hn
    exact hxK (hn' ▸ K.zpow_mem hKa n)
  let D := zpowers x ⊔ T
  have hi : D ⊓ K = T ⊓ K := by
    apply le_antisymm
    · intro z hz
      have hzprod : z ∈ (zpowers x : Set G) * (T : Set G) := hprod ▸ hz.1
      obtain ⟨a, ha, t, ht, rfl⟩ := hzprod
      have he : q a = (q t)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul]
        exact (QuotientGroup.eq_one_iff _).mpr hz.2
      have ha0 : q a = 1 := disjoint_def.mp hd
        (mem_map_of_mem q ha) (he ▸ (T.map q).inv_mem (mem_map_of_mem q ht))
      have ha1 : a = 1 := disjoint_def.mp hAK ha ((QuotientGroup.eq_one_iff _).mp ha0)
      refine ⟨?_, hz.2⟩
      change a * t ∈ T
      rw [ha1, one_mul]
      exact ht
    · exact inf_le_inf le_sup_right le_rfl
  have hn : D ≤ normalizer ((D ⊓ K : Subgroup G) : Set G) := by
    apply subgroup_le_normalizer_of_conj_mem
    intro d z hz
    exact ⟨D.mul_mem (D.mul_mem d.property hz.1) (D.inv_mem d.property),
      (inferInstance : K.Normal).conj_mem z hz.2 d⟩
  rw [hi] at hn
  exact hn ((show zpowers x ≤ D from le_sup_left) (mem_zpowers x))

/-- Odd centralizer and conjugation orbit counting obstruct normalization.
This concerns x normalizing R, not R normalizing ⟨x⟩. -/
theorem not_normalizes_two_subgroup_of_odd_centralizer
    (R : Subgroup G) (hR : IsPGroup 2 R) (x : G) (hx : orderOf x = 3)
    (hodd : Odd (Nat.card (centralizer ({x} : Set G))))
    (hcard : ¬ Nat.card R ≡ 1 [MOD 3]) :
    x ∉ normalizer (R : Set G) := by
  intro hn
  let A := zpowers x
  have hA : IsPGroup 3 A :=
    IsPGroup.of_card (n := 1) (by simpa only [A, Nat.card_zpowers, pow_one] using hx)
  have hcop : Nat.Coprime (Nat.card R) (Nat.card (centralizer ({x} : Set G))) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
    rw [hn]
    exact (Nat.coprime_two_left.mpr hodd).pow_left n
  have hd := (disjoint_of_coprime_natCard hcop).eq_bot
  have hc : R ⊓ centralizer (A : Set G) = ⊥ := by
    apply eq_bot_iff.mpr
    apply le_trans (inf_le_inf_left R (centralizer_le (Set.singleton_subset_iff.mpr
      (mem_zpowers x))))
    exact hd.le
  have hmod := card_modEq_card_inf_centralizer A R hA (zpowers_le.mpr hn)
  rw [hc, Subgroup.card_bot] at hmod
  exact hcard hmod

end Subgroup
