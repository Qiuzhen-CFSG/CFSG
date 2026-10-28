module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.ActorData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.TwoComponents
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Basic

/-!
# The actual rank-two quotient and invariant component factors

The order-nine quotient by O₂(Y₊) gives |Y₊S| = 2ⁿ · 9. The supplied
isomorphism modulo O₂,Φ to S₃ × S₃ then makes O₂,Φ a two-group, by comparing
orders. This argument retains the Frattini denominator throughout.
Relative normality of L in I and the actual S-orbit equality give normality
and S-invariance of both residual factors.

Source: Aschbacher--Smith, 15.3.37--40, printed pp.1135--1138.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

private theorem card_eq_two_pow_mul_nine {Y : Subgroup G}
    (hquot : Nat.card (Y ⧸ pCore 2 Y) = 9) :
    ∃ n : ℕ, Nat.card Y = 2 ^ n * 9 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := Y))
  exact ⟨n, by rw [← (pCore 2 Y).card_mul_index, index_eq_card, hquot, hn]⟩

/-- Only the order of the actual two-core quotient is needed for its three-part. -/
theorem threePart_of_twoCore_quotient_nine {Y : Subgroup G}
    (hquot : Nat.card (Y ⧸ pCore 2 Y) = 9) :
    3 ^ (Nat.card Y).factorization 3 = 9 := by
  obtain ⟨n, hn⟩ := card_eq_two_pow_mul_nine hquot
  rw [hn, Nat.factorization_mul (pow_ne_zero n (by decide)) (by decide)]
  simp only [Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2), smul_zero, zero_add]
  change 3 ^ (Nat.factorization (3 ^ 2)) 3 = 9
  rw [Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_three]
  norm_num

private theorem card_join_eq_two_pow_mul_nine {Y S : Subgroup G}
    (hquot : Nat.card (Y ⧸ pCore 2 Y) = 9)
    (hS : IsPGroup 2 S) (hSY : S ≤ normalizer (Y : Set G)) :
    ∃ n : ℕ, Nat.card (Y ⊔ S : Subgroup G) = 2 ^ n * 9 := by
  let H := Y ⊔ S
  have hYH : Y ≤ H := le_sup_left
  have hSH : S ≤ H := le_sup_right
  let : (Y.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hSY)
  have hgen : Y.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup hYH hSH]
    exact subgroupOf_self _
  have hp : IsPGroup 2 (H ⧸ Y.subgroupOf H) :=
    isPGroup_quotient_of_sup_eq_top _ _ hS.comap_subtype hgen
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hp
  obtain ⟨a, ha⟩ := card_eq_two_pow_mul_nine hquot
  refine ⟨a + b, ?_⟩
  change Nat.card H = _
  rw [← (Y.subgroupOf H).card_mul_index, index_eq_card, hb,
    Nat.card_congr (subgroupOfEquivOfLe hYH).toEquiv, ha, pow_add]
  ac_rfl

/-- The genuine O₂,Φ denominator is a two-group in the order-nine branch. -/
theorem rankTwoShadow_kernel_isTwoGroup {Y S : Subgroup G}
    (hquot : Nat.card (Y ⧸ pCore 2 Y) = 9)
    (hS : IsPGroup 2 S) (hSY : S ≤ normalizer (Y : Set G))
    (e : ((Y ⊔ S : Subgroup G) ⧸ twoFrattiniCore (Y ⊔ S : Subgroup G)) ≃*
      SymmetricThreeProduct.G) :
    IsPGroup 2 (twoFrattiniCore (Y ⊔ S : Subgroup G)) := by
  obtain ⟨n, hn⟩ := card_join_eq_two_pow_mul_nine hquot hS hSY
  have hcard : Nat.card ((Y ⊔ S : Subgroup G) ⧸ twoFrattiniCore (Y ⊔ S : Subgroup G)) = 36 :=
    (Nat.card_congr e.toEquiv).trans SymmetricThreeProduct.card_group
  have he := (twoFrattiniCore (Y ⊔ S : Subgroup G)).card_mul_index
  rw [index_eq_card, hcard, hn] at he
  have hmul : Nat.card (twoFrattiniCore (Y ⊔ S : Subgroup G)) * 4 = 2 ^ n := by omega
  have hd : Nat.card (twoFrattiniCore (Y ⊔ S : Subgroup G)) ∣ 2 ^ n := ⟨4, hmul.symm⟩
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card hk

/-- Relative component normality and orbit equality give the four invariance
facts needed to use the rank-two quotient. -/
theorem component_factors_normal_invariant {Y L I S : Subgroup G}
    (hLI : L ≤ I) [(L.subgroupOf I).Normal] (hYI : Y ≤ I)
    (hSY : S ≤ normalizer (Y : Set G)) (he : L = componentOrbit L S) :
    ((componentFactor Y L).subgroupOf Y).Normal ∧
    ((centralizingFactor Y L).subgroupOf Y).Normal ∧
    S ≤ normalizer (componentFactor Y L : Set G) ∧
    S ≤ normalizer (centralizingFactor Y L : Set G) := by
  have hYL : Y ≤ normalizer (L : Set G) :=
    hYI.trans (le_normalizer_of_normal_subgroupOf hLI)
  have hSL : S ≤ normalizer (L : Set G) := by
    conv_rhs => rw [he]
    exact le_normalizer_componentOrbit L S
  exact ⟨componentFactor_normal hYL, centralizingFactor_normal hYL,
    normalizes_componentFactor hSY hSL, normalizes_centralizingFactor hSY hSL⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo
