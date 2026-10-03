module

public import Stellmacher.Recognition.LyonsU3Four.AutomizerPrimeExclusions
public import Stellmacher.Recognition.LyonsU3Four.AutomizerNineExclusion
public import Stellmacher.Recognition.LyonsU3Four.OrderFifteenAction
public import Stellmacher.Recognition.LyonsU3Four.OrderFifteenNormalizer

/-!
# The automizer calculation and conditional order-fifteen normalizer

The bound 315, divisibility by three, and exclusion of seven and nine show
that the actual Sylow automizer has order three or fifteen. In the latter
case, the splitting of the actual normalizer modulo its odd core supplies
an order-fifteen automorphism. Its powers are transitive on the nonidentity
central cosets and on the nonidentity center elements, and the automorphism
itself fixes only the identity. The center action has order three; in
particular, fixed-point-freeness is not asserted for every nonidentity power.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
printed pp. 372–373.
-/

namespace Stellmacher.Recognition.LyonsU3Four

/-- The elementary bounds finish the calculation once the order-nine obstruction
has been established. -/
public theorem automizerIndex_eq_three_or_fifteen_of_not_nine_dvd
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (h9 : ¬ 9 ∣ automizerIndex S) :
    automizerIndex S = 3 ∨ automizerIndex S = 15 := by
  have h315 := automizerIndex_dvd_315 S h
  have h3 := three_dvd_automizerIndex S h
  have h7 := not_seven_dvd_automizerIndex S h
  let m := automizerIndex S
  change m = 3 ∨ m = 15
  change 3 ∣ m at h3
  change ¬ 7 ∣ m at h7
  change ¬ 9 ∣ m at h9
  change m ∣ 315 at h315
  have h45 : m ∣ 45 :=
    ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr h7).symm.dvd_of_dvd_mul_left h315
  have hc : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 9 ∨ m = 15 ∨ m = 45 := by
    have hm := Nat.mem_divisors.mpr ⟨h45, by decide⟩
    have hds : Nat.divisors 45 = {1, 3, 5, 9, 15, 45} := by decide
    rw [hds] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hc with h | h | h | h | h | h
  · norm_num [h] at h3
  · exact Or.inl h
  · norm_num [h] at h3
  · exact (h9 (by rw [h])).elim
  · exact Or.inr h
  · exact (h9 (by rw [h]; decide)).elim

/-- Lyons's numerical automizer calculation under exactly the intrinsic Sylow
hypothesis in a finite simple group. -/
public theorem automizerIndex_eq_three_or_fifteen
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) :
    automizerIndex S = 3 ∨ automizerIndex S = 15 :=
  automizerIndex_eq_three_or_fifteen_of_not_nine_dvd S h
    (not_nine_dvd_automizerIndex S h)

/-- The conditional order-fifteen normalizer structure, with all action
properties for the same actual automorphism of the supplied Sylow subgroup.
The equivalence preserves the canonical Sylow embedding into the quotient
of its actual normalizer by its odd core. -/
public theorem exists_orderFifteen_normalizer_structure
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (h15 : automizerIndex S = 15) :
    ∃ (β : MulAut S) (α : Multiplicative (ZMod 15) →* MulAut S),
      orderOf β = 15 ∧
      α (Multiplicative.ofAdd (1 : ZMod 15)) = β ∧
      (∀ s : S, β s = s → s = 1) ∧
      (∀ x y : S ⧸ Subgroup.center S, x ≠ 1 → y ≠ 1 →
        ∃ n : ℤ, (Subgroup.quotientAut (Subgroup.center S) β ^ n) x = y) ∧
      orderOf (MulAut.characteristic (Subgroup.center S) β) = 3 ∧
      (∀ x y : Subgroup.center S, x ≠ 1 → y ≠ 1 →
        ∃ n : ℤ, (MulAut.characteristic (Subgroup.center S) β ^ n) x = y) ∧
      ∃ e : (Subgroup.normalizer (S : Set G) ⧸
          pPrimeCore 2 (Subgroup.normalizer (S : Set G))) ≃*
          S ⋊[α] Multiplicative (ZMod 15),
        ∀ s : S, e (sylowNormalizerQuotientMap S s) = SemidirectProduct.inl s := by
  obtain ⟨β, α, hβ, hα, e, he⟩ := exists_orderFifteen_normalizer_equiv S h h15
  exact ⟨β, α, hβ, hα, order_fifteen_fixed_eq_one S h β hβ,
    order_fifteen_quotient_transitive S h β hβ, order_fifteen_center_order S h β hβ,
    order_fifteen_center_transitive S h β hβ, e, he⟩

end Stellmacher.Recognition.LyonsU3Four
