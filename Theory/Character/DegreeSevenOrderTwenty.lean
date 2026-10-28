module

public import Theory.Character.SchurDegreeSeven
public import Theory.Character.ScalarProductMultiplicity
public import Theory.Character.Transport
public import Theory.Character.RationalPower
public import Theory.Character.AbelianLinearCharacters

/-!
# Excluding order twenty in degree seven

A rational-valued irreducible character of degree seven of a finite simple
group, taking value minus one on involutions, excludes elements of order
twenty. For an element `g` of order twenty, Schur's trace spacing gives
`χ (g ^ 4) = 2`. Rational power invariance evaluates the pairing with a
faithful linear character of its cyclic subgroup as `6 + χ (g ^ 2)`.
This is twenty times a natural multiplicity; the trace bound makes that
multiplicity zero. Thus `χ (g ^ 2) = -6`, and the principal pairing on the
subgroup of order ten would have multiplicity minus one.

This uses complex characters and their rational values, without requiring
a rational realization.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed pp. 74–75; cyclic restriction and
ordinary character multiplicities.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

private def cyclicHom {M : Type*} [Monoid M] (n : ℕ) [NeZero n]
    (x : M) (hx : x ^ n = 1) : Multiplicative (ZMod n) →* M where
  toFun i := x ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change x ^ (i.toAdd + j.toAdd).val = x ^ i.toAdd.val * x ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hx).symm

private theorem pairing_nat {H : Type*} [Group H] [Finite H]
    {χ : ClassFunction H} (hχ : IsCharacter χ) (η : H →* ℂ) :
    ∃ m : ℕ, (∑ x : H, χ x * star (η x)) = (Nat.card H : ℂ) * m := by
  have hη : IsCharacter (η : H → ℂ) := by
    obtain ⟨n, ρ, _, hρ⟩ := η.isLinearCharacter.1
    exact ⟨n, ρ, hρ⟩
  obtain ⟨m, hm⟩ := hχ.scalarProduct_nat hη
  refine ⟨m, ?_⟩
  have hc : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [← hm, scalarProduct, mul_inv_cancel_left₀ hc]

/-- A rational-valued degree-seven irreducible character of a finite simple
group, with value minus one at every involution, excludes order twenty. -/
public theorem IsIrreducibleCharacter.degree_seven_orderOf_ne_twenty
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ x : G, ∃ q : ℚ, χ x = (q : ℂ))
    (hinv : ∀ u : G, orderOf u = 2 → χ u = -1) :
    ∀ g : G, orderOf g ≠ 20 := by
  classical
  intro g hg
  have hg20 : g ^ 20 = 1 := hg ▸ pow_orderOf_eq_one g
  have hc : IsCharacter χ := by
    obtain ⟨n, ρ, _, hρ⟩ := hχ
    exact ⟨n, ρ, hρ⟩
  have h10 : χ (g ^ 10) = -1 := hinv _ (by rw [orderOf_pow, hg]; norm_num)
  have h4 : χ (g ^ 4) = 2 :=
    hχ.degree_seven_value_of_order_five hdegree (by rw [orderOf_pow, hg]; norm_num) (hrat _)
  have hp (d n k : ℕ) (hn : n ≠ 0) (hd : d * n = 20) (hk : k.Coprime n) :
      χ (g ^ (d * k)) = χ (g ^ d) := by
    have hdn : (g ^ d) ^ n = 1 := by rw [← pow_mul, hd, hg20]
    simpa only [← pow_mul] using hc.pow_eq_of_rational_value (g ^ d) hn hdn hk (hrat _)
  have h3 := hp 1 20 3 (by decide) (by decide) (by decide)
  have h7 := hp 1 20 7 (by decide) (by decide) (by decide)
  have h9 := hp 1 20 9 (by decide) (by decide) (by decide)
  have h11 := hp 1 20 11 (by decide) (by decide) (by decide)
  have h13 := hp 1 20 13 (by decide) (by decide) (by decide)
  have h17 := hp 1 20 17 (by decide) (by decide) (by decide)
  have h19 := hp 1 20 19 (by decide) (by decide) (by decide)
  have h6 := hp 2 10 3 (by decide) (by decide) (by decide)
  have h14 := hp 2 10 7 (by decide) (by decide) (by decide)
  have h18 := hp 2 10 9 (by decide) (by decide) (by decide)
  have h8 := hp 4 5 2 (by decide) (by decide) (by decide)
  have h12 := hp 4 5 3 (by decide) (by decide) (by decide)
  have h16 := hp 4 5 4 (by decide) (by decide) (by decide)
  have h15 := hp 5 4 3 (by decide) (by decide) (by decide)
  norm_num only [Nat.reduceMul, pow_one] at h3 h7 h9 h11 h13 h17 h19 h6 h14 h18 h8 h12 h16 h15
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)
  have hζ : IsPrimitiveRoot ζ 20 := Complex.isPrimitiveRoot_exp 20 (by decide)
  have hζ10 : ζ ^ 10 = -1 :=
    (IsPrimitiveRoot.pow (by decide) hζ (show 20 = 10 * 2 by decide)).eq_neg_one_of_two_right
  have hζ2 : ζ ^ 2 + 1 ≠ 0 := by
    intro h
    have hz4 : ζ ^ 4 = 1 := by
      have hz2 : ζ ^ 2 = -1 := by linear_combination h
      calc ζ ^ 4 = (ζ ^ 2) ^ 2 := by ring
           _ = 1 := by rw [hz2]; norm_num
    have hd := hζ.dvd_of_pow_eq_one 4 hz4
    norm_num at hd
  have hpoly : ζ ^ 8 - ζ ^ 6 + ζ ^ 4 - ζ ^ 2 + 1 = 0 := by
    apply (mul_eq_zero.mp (show (ζ ^ 2 + 1) *
      (ζ ^ 8 - ζ ^ 6 + ζ ^ 4 - ζ ^ 2 + 1) = 0 by linear_combination hζ10)).resolve_left hζ2
  let e := cyclicHom 20 g hg20
  let η := cyclicHom 20 ζ hζ.pow_eq_one
  have hs : (∑ i : Multiplicative (ZMod 20), χ (e i) * star (η i)) = 6 + χ (g ^ 2) := by
    change (∑ i : Multiplicative (ZMod 20), χ (g ^ i.toAdd.val) * star (ζ ^ i.toAdd.val)) = _
    rw [(Multiplicative.toAdd : Multiplicative (ZMod 20) ≃ ZMod 20).sum_comp
      (fun i => χ (g ^ i.val) * star (ζ ^ i.val))]
    change (∑ i : Fin 20, χ (g ^ i.val) * star (ζ ^ i.val)) = _
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    norm_num only [pow_zero, pow_one, h3, h7, h9, h11, h13, h17, h19,
      h6, h14, h18, h8, h12, h16, h15, h4, h10, hdegree, star_one, mul_one]
    have hs10 : star ζ ^ 10 = -1 := by rw [← star_pow, hζ10, star_neg, star_one]
    have hsP : star ζ ^ 8 - star ζ ^ 6 + star ζ ^ 4 - star ζ ^ 2 + 1 = 0 := by
      simpa only [star_add, star_sub, star_pow, star_one, star_zero] using congrArg star hpoly
    simp only [star_pow]
    linear_combination
      (χ g * (star ζ ^ 9 + star ζ ^ 7 + star ζ ^ 3 + star ζ) +
        χ (g ^ 2) * (star ζ ^ 8 + star ζ ^ 4) +
        χ (g ^ 5) * star ζ ^ 5 + 2 * (star ζ ^ 6 + star ζ ^ 2) - 1) * hs10 +
      (2 - χ (g ^ 2)) * hsP
  obtain ⟨m, hm⟩ := pairing_nat (isCharacter_comp_hom e hc) η
  have hm' : 6 + χ (g ^ 2) = 20 * (m : ℂ) := by
    apply hs.symm.trans
    show (∑ i : Multiplicative (ZMod 20), χ (e i) * star (η i)) = 20 * (m : ℂ)
    convert hm using 1
    · congr 2
      exact Subsingleton.elim _ _
    · simp [Nat.card_eq_fintype_card]
  obtain ⟨ρ, heq, _⟩ := hχ.exists_faithful_degree_seven hdegree
  have hbound : (χ (g ^ 2)).re ≤ 7 := by
    have hb := finite_order_end_norm_trace_le_finrank (ρ (g ^ 2)) (n := 10) (by decide)
      (by rw [← map_pow, ← pow_mul, show 2 * 10 = 20 by decide, hg20, map_one])
    have he : χ (g ^ 2) = LinearMap.trace ℂ (Fin 7 → ℂ) (ρ (g ^ 2)) := by rw [heq]; rfl
    rw [he]
    exact (Complex.re_le_norm _).trans (by simpa using hb)
  have hm0 : m = 0 := by
    have hr := congrArg Complex.re hm'
    norm_num at hr
    have : (m : ℝ) < 1 := by linarith
    have : m < 1 := by exact_mod_cast this
    omega
  have hv : χ (g ^ 2) = -6 := by rw [hm0] at hm'; norm_num at hm'; linear_combination hm'
  let e10 := cyclicHom 10 (g ^ 2) (by rw [← pow_mul]; exact hg20)
  obtain ⟨l, hl⟩ := pairing_nat (isCharacter_comp_hom e10 hc) (1 : Multiplicative (ZMod 10) →* ℂ)
  have hs10 : (∑ i : Multiplicative (ZMod 10), χ (e10 i) * star ((1 : Multiplicative (ZMod 10) →* ℂ) i)) = -10 := by
    change (∑ i : Multiplicative (ZMod 10), χ ((g ^ 2) ^ i.toAdd.val) * star (1 : ℂ)) = _
    rw [(Multiplicative.toAdd : Multiplicative (ZMod 10) ≃ ZMod 10).sum_comp
      (fun i => χ ((g ^ 2) ^ i.val) * star (1 : ℂ))]
    change (∑ i : Fin 10, χ ((g ^ 2) ^ i.val) * star (1 : ℂ)) = _
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, ← pow_mul]
    norm_num [hdegree, h4, h6, h8, h10, h12, h14, h16, h18, hv]
  have hl' : (-10 : ℂ) = 10 * (l : ℂ) := by
    apply hs10.symm.trans
    convert hl using 1
    · congr 2
      exact Subsingleton.elim _ _
    · simp [Nat.card_eq_fintype_card]
  have hr := congrArg Complex.re hl'
  simp at hr
  have hn : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  linarith
