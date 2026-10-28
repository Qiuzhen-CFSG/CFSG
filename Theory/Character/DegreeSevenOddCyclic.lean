module

public import Theory.Character.SchurDegreeSeven
public import Theory.Character.IntegralRestriction
public import Theory.Character.RationalPower
public import Theory.Character.Integrality
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Odd cyclic restrictions in degree seven

A rational-valued irreducible character of degree seven of a finite simple
group takes value `-1` at elements of order fifteen, and the group has no
elements of order forty-five. No rational realization is assumed.

For an element of order fifteen, let `a` be its fifth-power value and `b`
its own value. The principal multiplicity on its cyclic subgroup gives
`15 + 2a + 8b = 15m`, where `m` is a natural number. Rational character
values are integers, `b ≤ 7`, and prime-order trace spacing gives
`a ∈ {4, 1, -2}`. These conditions force `a = 4` and `b = -1`.
An element of order nine whose cube has value four would instead give
`15 + 6c = 9m`, with `c ∈ {4, 1, -2}`, which is impossible. The third and
fifth powers of an element of order forty-five connect these two results.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed pp. 74–75. The proof uses ordinary
cyclic restriction multiplicities and Schur's prime-power trace spacing.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

private def cyclicHom {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (g : G) (hg : g ^ n = 1) : Multiplicative (ZMod n) →* G where
  toFun i := g ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change g ^ (i.toAdd + j.toAdd).val = g ^ i.toAdd.val * g ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hg).symm

private theorem cyclic_sum_nat {G : Type*} [Group G] {χ : ClassFunction G}
    (hχ : IsCharacter χ) {n : ℕ} [NeZero n] (g : G) (hg : g ^ n = 1) :
    ∃ m : ℕ, (∑ i : Multiplicative (ZMod n), χ (g ^ i.toAdd.val)) =
      (n : ℂ) * m := by
  let e := cyclicHom g hg
  obtain ⟨m, hm⟩ := (isCharacter_comp_hom e hχ).scalarProduct_nat isCharacter_one
  refine ⟨m, ?_⟩
  have hc : (Nat.card (Multiplicative (ZMod n)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have he : (∑ i : Multiplicative (ZMod n), χ (e i)) =
      (Nat.card (Multiplicative (ZMod n)) : ℂ) * (m : ℂ) := by
    simp only [scalarProduct, Pi.one_apply, star_one, mul_one] at hm
    rw [← hm, mul_inv_cancel_left₀ hc]
    congr 2
    exact Subsingleton.elim _ _
  simpa only [e, cyclicHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] using he

private theorem integer_value {G : Type*} [Group G] [Finite G]
    {χ : ClassFunction G} (hχ : IsCharacter χ) (g : G)
    (hrat : ∃ q : ℚ, χ g = (q : ℂ)) : ∃ z : ℤ, χ g = (z : ℂ) := by
  obtain ⟨d, ρ, rfl⟩ := hχ
  have hint := character_value_isIntegral ρ g
  obtain ⟨q, hq⟩ := hrat
  rw [hq] at hint
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  exact ⟨z, by rw [hq, ← hz]; simp⟩

private theorem fifteen_values
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    {g : G} (hg : orderOf g = 15) : χ g = -1 ∧ χ (g ^ 5) = 4 := by
  have hchar : IsCharacter χ := by obtain ⟨d, ρ, _, hρ⟩ := hχ; exact ⟨d, ρ, hρ⟩
  have hpow : g ^ 15 = 1 := hg ▸ pow_orderOf_eq_one g
  have ho3 : orderOf (g ^ 5) = 3 := by rw [orderOf_pow, hg]; norm_num
  have ho5 : orderOf (g ^ 3) = 5 := by rw [orderOf_pow, hg]; norm_num
  have hfive := hχ.degree_seven_value_of_order_five hdegree ho5 (hrat _)
  have hthree := hχ.degree_seven_value_of_order_three hdegree ho3 (hrat _)
  obtain ⟨b, hb⟩ := integer_value hchar g (hrat g)
  have hb_le : b ≤ 7 := by
    obtain ⟨ρ, hρ, _⟩ := hχ.exists_faithful_degree_seven hdegree
    have hρpow : (ρ g) ^ 15 = 1 := by rw [← map_pow, hpow, map_one]
    have hn := finite_order_end_norm_trace_le_finrank (ρ g) (by decide) hρpow
    have he : LinearMap.trace ℂ (Fin 7 → ℂ) (ρ g) = (b : ℂ) := by
      simpa only [hρ, Representation.character] using hb
    rw [he] at hn
    have hre := (Complex.re_le_norm (b : ℂ)).trans hn
    norm_num at hre
    have hre' : (b : ℝ) ≤ 7 := by simpa using hre
    exact_mod_cast hre'
  have hunit (k : ℕ) (hk : k.Coprime 15) : χ (g ^ k) = χ g :=
    hchar.pow_eq_of_rational_value g (by decide) hpow hk (hrat g)
  have hten : χ (g ^ 10) = χ (g ^ 5) := by
    have hp : (g ^ 5) ^ 3 = 1 := by simpa only [← pow_mul] using hpow
    simpa only [← pow_mul] using
      hchar.pow_eq_of_rational_value (g ^ 5) (by decide) hp
        (show Nat.Coprime 2 3 by decide) (hrat _)
  have hf (k : ℕ) (hk : k.Coprime 5) : χ (g ^ (3*k)) = 2 := by
    have hp : (g ^ 3) ^ 5 = 1 := by simpa only [← pow_mul] using hpow
    simpa only [← pow_mul, hfive] using
      hchar.pow_eq_of_rational_value (g ^ 3) (by decide) hp hk (hrat _)
  obtain ⟨m, hm⟩ := cyclic_sum_nat hchar g hpow
  rw [(Multiplicative.toAdd : Multiplicative (ZMod 15) ≃ ZMod 15).sum_comp
    (fun i => χ (g ^ i.val))] at hm
  change (∑ i : Fin 15, χ (g ^ i.val)) = (15 : ℂ) * m at hm
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ] at hm
  norm_num only [pow_zero, pow_one, hdegree,
    hunit 2 (by decide), hunit 4 (by decide), hunit 7 (by decide),
    hunit 8 (by decide), hunit 11 (by decide), hunit 13 (by decide),
    hunit 14 (by decide), hfive, hten,
    hf 2 (by decide), hf 3 (by decide), hf 4 (by decide), hb] at hm
  have hs : (15 : ℂ) + 2 * χ (g ^ 5) + 8 * (b : ℂ) = 15 * m := by
    linear_combination hm
  rcases hthree with ha | ha | ha
  · rw [ha] at hs
    have hi : (23 : ℤ) + 8 * b = 15 * m := by exact_mod_cast hs
    have : b = -1 := by omega
    exact ⟨by simpa [this] using hb, ha⟩
  · rw [ha] at hs
    have hi : (17 : ℤ) + 8 * b = 15 * m := by exact_mod_cast hs
    omega
  · rw [ha] at hs
    have hi : (11 : ℤ) + 8 * b = 15 * m := by exact_mod_cast hs
    omega

private theorem nine_cube_ne_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    {g : G} (hg : orderOf g = 9) : χ (g ^ 3) ≠ 4 := by
  intro hfour
  have hchar : IsCharacter χ := by obtain ⟨d, ρ, _, hρ⟩ := hχ; exact ⟨d, ρ, hρ⟩
  have hpow : g ^ 9 = 1 := hg ▸ pow_orderOf_eq_one g
  have hvalues : χ g = 4 ∨ χ g = 1 ∨ χ g = -2 := by
    obtain ⟨ρ, rfl, hfaithful⟩ := hχ.exists_faithful_degree_seven hdegree
    have hp : (ρ g) ^ (3 ^ 2) = 1 := by rw [← map_pow, show 3^2 = 9 by decide, hpow, map_one]
    have hne : ρ g ≠ 1 := by
      intro he
      have hg1 : g = 1 := hfaithful (he.trans (map_one ρ).symm)
      simp [hg1] at hg
    obtain ⟨j, hj, he⟩ := prime_power_trace_spacing_of_rational (ρ g)
      (show Nat.Prime 3 by decide) hp hne (hrat g)
    change ρ.character g = _ at he
    norm_num at hj he
    interval_cases j <;> norm_num at he ⊢ <;> simp [he]
  have hunit (k : ℕ) (hk : k.Coprime 9) : χ (g ^ k) = χ g :=
    hchar.pow_eq_of_rational_value g (by decide) hpow hk (hrat g)
  have hsix : χ (g ^ 6) = 4 := by
    have hp : (g ^ 3) ^ 3 = 1 := by simpa only [← pow_mul] using hpow
    simpa only [← pow_mul, hfour] using
      hchar.pow_eq_of_rational_value (g ^ 3) (by decide) hp
        (show Nat.Coprime 2 3 by decide) (hrat _)
  obtain ⟨m, hm⟩ := cyclic_sum_nat hchar g hpow
  rw [(Multiplicative.toAdd : Multiplicative (ZMod 9) ≃ ZMod 9).sum_comp
    (fun i => χ (g ^ i.val))] at hm
  change (∑ i : Fin 9, χ (g ^ i.val)) = (9 : ℂ) * m at hm
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ] at hm
  norm_num only [pow_zero, pow_one, hdegree, hfour, hsix,
    hunit 2 (by decide), hunit 4 (by decide), hunit 5 (by decide),
    hunit 7 (by decide), hunit 8 (by decide)] at hm
  have hs : (15 : ℂ) + 6 * χ g = 9 * m := by linear_combination hm
  rcases hvalues with hv | hv | hv <;> rw [hv] at hs <;> norm_num at hs
  · have he : 39 = 9 * m := by exact_mod_cast hs
    omega
  · have he : 21 = 9 * m := by exact_mod_cast hs
    omega
  · have he : 3 = 9 * m := by exact_mod_cast hs
    omega

/-- At order fifteen, a rational-valued degree-seven irreducible character
of a finite simple group has value minus one. -/
public theorem IsIrreducibleCharacter.degree_seven_value_of_order_fifteen
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    {g : G} (hg : orderOf g = 15) : χ g = -1 :=
  (fifteen_values hχ hdegree hrat hg).1

/-- Such a character also takes value four at the fifth power of an
order-fifteen element. -/
public theorem IsIrreducibleCharacter.degree_seven_fifth_power_value_of_order_fifteen
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    {g : G} (hg : orderOf g = 15) : χ (g ^ 5) = 4 :=
  (fifteen_values hχ hdegree hrat hg).2

/-- A finite simple group with a rational-valued irreducible character of
degree seven has no elements of order forty-five. -/
public theorem IsIrreducibleCharacter.degree_seven_order_ne_fortyFive
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ)) (g : G) : orderOf g ≠ 45 := by
  intro hg
  have h15 : orderOf (g ^ 3) = 15 := by rw [orderOf_pow, hg]; norm_num
  have h9 : orderOf (g ^ 5) = 9 := by rw [orderOf_pow, hg]; norm_num
  apply nine_cube_ne_four hχ hdegree hrat h9
  simpa only [← pow_mul] using
    hχ.degree_seven_fifth_power_value_of_order_fifteen hdegree hrat h15
