module

public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith

/-!
# An index-two product with a quaternion subgroup

In a group of order 64, let A be a normal C₄ × C₄ subgroup and R a normal
quaternion subgroup. If some element inverts A, then AR has index two.
Indeed an inverter in AR would put every square of A in R. The two distinct
nonidentity squares of A contradict the unique involution of R. Also R
cannot lie in the abelian subgroup A, so the product has order strictly
between 16 and 64. The product formula then gives an intersection of order
four. Quaternion uniqueness of the involution makes this intersection cyclic,
and we obtain an ambient generator of order four.

This elementary calculation is used for the local configuration in
Stellmacher, (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup

private abbrev C4 := Multiplicative (ZMod 4)

/-- A C₄ × C₄ subgroup has two distinct nonidentity squares. -/
public theorem exists_distinct_squares_of_c4_square
    {G : Type*} [Group G] (A : Subgroup G)
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    ∃ x ∈ A, ∃ y ∈ A,
      x ^ 4 = 1 ∧ y ^ 4 = 1 ∧ x ^ 2 ≠ 1 ∧ y ^ 2 ≠ 1 ∧ x ^ 2 ≠ y ^ 2 := by
  obtain ⟨e⟩ := hA
  let f : C4 × C4 →* G := A.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := A.subtype_injective.comp e.symm.injective
  let x : C4 × C4 := (Multiplicative.ofAdd 1, 1)
  let y : C4 × C4 := (1, Multiplicative.ofAdd 1)
  refine ⟨f x, (e.symm x).property, f y, (e.symm y).property, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, show x ^ 4 = 1 by decide, map_one]
  · rw [← map_pow, show y ^ 4 = 1 by decide, map_one]
  · intro h
    exact (by decide : x ^ 2 ≠ 1) (hf (by simpa only [map_pow, map_one] using h))
  · intro h
    exact (by decide : y ^ 2 ≠ 1) (hf (by simpa only [map_pow, map_one] using h))
  · intro h
    exact (by decide : x ^ 2 ≠ y ^ 2) (hf (by simpa only [map_pow] using h))

/-- A quaternion subgroup cannot contain every square of a C₄ × C₄ subgroup. -/
public theorem not_all_squares_mem_quaternion_of_c4_square
    {G : Type*} [Group G] (A R : Subgroup G)
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) (hR : Nonempty (R ≃* QuaternionGroup 2)) :
    ¬ (∀ x ∈ A, x ^ 2 ∈ R) := by
  intro hall
  obtain ⟨x, hx, y, hy, hx4, hy4, hx2, hy2, hxy⟩ :=
    exists_distinct_squares_of_c4_square A hA
  obtain ⟨e⟩ := hR
  let xx : R := ⟨x ^ 2, hall x hx⟩
  let yy : R := ⟨y ^ 2, hall y hy⟩
  have hxx : xx ^ 2 = 1 := Subtype.ext (by change (x ^ 2) ^ 2 = 1; simpa only [← pow_mul] using hx4)
  have hyy : yy ^ 2 = 1 := Subtype.ext (by change (y ^ 2) ^ 2 = 1; simpa only [← pow_mul] using hy4)
  have hunique : ∀ a b : QuaternionGroup 2,
      a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b := by decide
  have heq := hunique (e xx) (e yy)
    (by simpa only [map_pow, map_one] using congrArg e hxx)
    (by simpa only [map_pow, map_one] using congrArg e hyy)
    (fun h => hx2 (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))))
    (fun h => hy2 (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))))
  exact hxy (congrArg Subtype.val (e.injective heq))

/-- An inverter of a C₄ × C₄ subgroup lies outside its product with a normal
quaternion subgroup. -/
public theorem inverter_not_mem_c4_square_sup_quaternion
    {G : Type*} [Group G] (A R : Subgroup G) [R.Normal]
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) (hR : Nonempty (R ≃* QuaternionGroup 2))
    (t : G) (ht : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹) : t ∉ A ⊔ R := by
  intro htAR
  obtain ⟨a, ha, r, hr, rfl⟩ := mem_sup_of_normal_right.mp htAR
  apply not_all_squares_mem_quaternion_of_c4_square A R hA hR
  obtain ⟨e⟩ := hA
  have hcomm (x : G) (hx : x ∈ A) : a * x = x * a := by
    have h : (⟨a, ha⟩ : A) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨a, ha⟩ := e.injective (by
      simp only [map_mul]
      exact mul_comm _ _)
    exact congrArg Subtype.val h
  intro x hx
  let q := QuotientGroup.mk' R
  have hq : q (a * r * x * (a * r)⁻¹) = q x := by
    have hrq : q r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    simp only [map_mul, map_inv, hrq, mul_one]
    rw [← map_mul, hcomm x hx, map_mul]
    group
  have hxi : q x = q x⁻¹ := hq.symm.trans (congrArg q (ht x hx))
  apply (QuotientGroup.eq_one_iff (x ^ 2)).mp
  change q (x ^ 2) = 1
  rw [map_pow, pow_two]
  calc
    q x * q x = q x⁻¹ * q x := congrArg (fun z => z * q x) hxi
    _ = 1 := by rw [map_inv, inv_mul_cancel]

/-- The product of a C₄ × C₄ subgroup and a normal quaternion subgroup has
index two in an order-64 group admitting an inverter of the abelian subgroup. -/
public theorem c4_square_sup_quaternion_index_two
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 64)
    (A R : Subgroup G) [R.Normal]
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hR : Nonempty (R ≃* QuaternionGroup 2))
    (t : G) (ht : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹) : (A ⊔ R).index = 2 := by
  have hout := inverter_not_mem_c4_square_sup_quaternion A R hA hR t ht
  obtain ⟨eA⟩ := hA
  obtain ⟨eR⟩ := hR
  have hcardA : Nat.card A = 16 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card]
  have hAi : A.index = 4 := by
    have h := A.card_mul_index
    rw [hG, hcardA] at h
    omega
  have hnle : ¬ R ≤ A := by
    intro hle
    let f : QuaternionGroup 2 →* A := (inclusion hle).comp eR.symm.toMonoidHom
    have hf : Function.Injective f := (inclusion_injective hle).comp eR.symm.injective
    have hcomm (x y : A) : x * y = y * x := eA.injective (by
      simp only [map_mul]
      exact mul_comm _ _)
    have hh := hcomm (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0))
    have heq : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 :=
      hf (by simpa only [map_mul] using hh)
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1) heq
  have hrel : A.relIndex (A ⊔ R) ≠ 1 := by
    intro h
    exact hnle (le_sup_right.trans (relIndex_eq_one.mp h))
  have hidx : (A ⊔ R).index ≠ 1 := by
    intro h
    exact hout (index_eq_one.mp h ▸ mem_top t)
  have hmul := relIndex_mul_index (show A ≤ A ⊔ R from le_sup_left)
  rw [hAi] at hmul
  have hrpos : 0 < A.relIndex (A ⊔ R) := Nat.pos_of_ne_zero (by
    intro h
    rw [h] at hmul
    norm_num at hmul)
  have hipos : 0 < (A ⊔ R).index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hr : 2 ≤ A.relIndex (A ⊔ R) := by omega
  have hi : 2 ≤ (A ⊔ R).index := by omega
  nlinarith


/-- The intersection of the base and normal quaternion subgroup has order
four in the order-64 configuration. -/
public theorem c4_square_inf_quaternion_card
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 64)
    (A R : Subgroup G) [R.Normal]
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hR : Nonempty (R ≃* QuaternionGroup 2))
    (t : G) (ht : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹) :
    Nat.card (A ⊓ R : Subgroup G) = 4 := by
  have hindex := c4_square_sup_quaternion_index_two hG A R hA hR t ht
  have hAR : Nat.card (A ⊔ R : Subgroup G) = 32 := by
    have hh := (A ⊔ R).card_mul_index
    rw [hindex, hG] at hh
    omega
  obtain ⟨eA⟩ := hA
  obtain ⟨eR⟩ := hR
  have hcA : Nat.card A = 16 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card]
  have hcR : Nat.card R = 8 := by
    rw [Nat.card_congr eR.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes R A le_normalizer_of_normal
  rw [sup_comm R A, inf_comm R A, hcA, hcR, hAR] at hh
  omega

/-- The intersection is cyclic of order four, with a generator in the
ambient group. Quaternion uniqueness of the involution rules out exponent
two for a subgroup of order four. -/
public theorem exists_generator_c4_square_inf_quaternion
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 64)
    (A R : Subgroup G) [R.Normal]
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hR : Nonempty (R ≃* QuaternionGroup 2))
    (t : G) (ht : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹) :
    ∃ c : G, orderOf c = 4 ∧ zpowers c = A ⊓ R := by
  have hcard := c4_square_inf_quaternion_card hG A R hA hR t ht
  obtain ⟨e⟩ := hR
  have hn : ¬ ∀ c : (A ⊓ R : Subgroup G), c ^ 2 = 1 := by
    intro hall
    let f : (A ⊓ R : Subgroup G) → {q : QuaternionGroup 2 // q ^ 2 = 1} := fun c =>
      ⟨e ⟨c, c.property.2⟩, by
        have hh : (⟨c, c.property.2⟩ : R) ^ 2 = 1 :=
          Subtype.ext (congrArg (fun x : (A ⊓ R : Subgroup G) => (x : G)) (hall c))
        rw [← map_pow, hh, map_one]⟩
    have hf : Function.Injective f := by
      intro x y hh
      exact Subtype.ext (congrArg (fun x : R => (x : G)) (e.injective (congrArg Subtype.val hh)))
    have hh := Nat.card_le_card_of_injective f hf
    have htwo : Nat.card {q : QuaternionGroup 2 // q ^ 2 = 1} = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [hcard, htwo] at hh
    omega
  push Not at hn
  obtain ⟨c, hc⟩ := hn
  have hc4 : (c : G) ^ 4 = 1 := by
    have hq : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
    have hh : (⟨c, c.property.2⟩ : R) ^ 4 = 1 := e.injective (by
      rw [map_pow, map_one]; exact hq _)
    exact congrArg Subtype.val hh
  have hc2 : (c : G) ^ 2 ≠ 1 := fun hh => hc (Subtype.ext hh)
  have hord : orderOf (c : G) = 4 := orderOf_eq_prime_pow (p := 2) (n := 1) hc2 hc4
  refine ⟨c, hord, eq_of_le_of_card_ge (zpowers_le.mpr c.property) ?_⟩
  rw [hcard, Nat.card_zpowers, hord]

end Subgroup
