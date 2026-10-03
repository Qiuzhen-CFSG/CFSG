module

public import Theory.Character.SchurDegreeSeven
public import Theory.Character.VanishingCentralizer
public import Theory.Character.DegreeSevenOddCyclic
public import Theory.Character.DegreeSevenOrderTwenty

/-!
# Mixed orders for rational characters of degree seven

The commuting-element congruence compares integer values modulo the order of
an element of prime order. In a five-centralizer, absence of order 45 reduces
nontrivial elements of three-power order to order three. The value at order 15
then selects four from the full order-three list four, one, minus two.

The imported cyclic restriction results exclude order 45 and give value minus
one at order 15, discharging the inputs to the final five-centralizer theorem.
They also exclude order 20 when the character has value minus one on every
involution. All results use rational character values without assuming a
rational realization.
Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed pp. 74–75.
-/

/-- Integer character values at commuting prime-order multiples agree modulo
that prime. -/
public theorem Representation.prime_dvd_integer_character_sub_of_commute
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {p : ℕ} (hp : p.Prime)
    {x y : G} (hx : orderOf x = p) (hcomm : Commute x y)
    (a b : ℤ) (hy : ρ.character y = (a : ℂ))
    (hxy : ρ.character (x * y) = (b : ℂ)) : (p : ℤ) ∣ b - a := by
  let η : ℂ := Complex.exp (2 * Real.pi * Complex.I / Nat.card G)
  let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hη : IsPrimitiveRoot η (Nat.card G) :=
    Complex.isPrimitiveRoot_exp _ (Nat.card_pos (α := G)).ne'
  have hξ : IsPrimitiveRoot ξ p := Complex.isPrimitiveRoot_exp _ hp.ne_zero
  have hξη : ξ ∈ cyclotomicOrder η :=
    primitive_root_mem_cyclotomicOrder_of_dvd hη (Nat.card_pos (α := G)).ne' hξ
      (hx ▸ orderOf_dvd_natCard x)
  have hηint : IsIntegral ℤ η := by
    refine ⟨Polynomial.X ^ Nat.card G - 1,
      Polynomial.monic_X_pow_sub_C (1 : ℤ) (Nat.card_pos (α := G)).ne', ?_⟩
    simp [hη.pow_eq_one]
  obtain ⟨_, _, hcong⟩ := representation_character_congruent_at_mul
    hξ hp.ne_zero hη hξη ρ hx hcomm.eq
  apply prime_dvd_int_of_congruent_zero_mod_one_sub hp hξ hηint hξη (b - a)
  change _ ∈ Ideal.span _ at hcong ⊢
  convert hcong using 1
  ext
  simp [hy, hxy]

/-- Without elements of order 45, a nontrivial three-element centralizing an
order-five element has order three. -/
public theorem orderOf_eq_three_of_centralizes_five_of_no_order_fortyFive
    {G : Type*} [Group G] [Finite G]
    (hno : ∀ x : G, orderOf x ≠ 45)
    {s g : G} (hs : orderOf s = 5) (hc : Commute s g) (hg : g ≠ 1)
    (hpower : ∃ e : ℕ, orderOf g = 3 ^ e) : orderOf g = 3 := by
  obtain ⟨e, he⟩ := hpower
  have he0 : e ≠ 0 := by
    intro hz
    have : orderOf g = 1 := by simpa [hz] using he
    exact hg (orderOf_eq_one_iff.mp this)
  have he2 : ¬ 2 ≤ e := by
    intro he2
    have hd : 9 ∣ orderOf g := by
      rw [he]
      exact Nat.pow_dvd_pow 3 he2
    have hk : orderOf (g ^ (orderOf g / 9)) = 9 :=
      orderOf_pow_orderOf_div (by rw [he]; positivity) hd
    have hc' := hc.pow_right (orderOf g / 9)
    have ho : orderOf (s * g ^ (orderOf g / 9)) = 45 := by
      rw [hc'.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hs, hk]; decide), hs, hk]
    exact hno _ ho
  have he1 : e = 1 := by omega
  simpa [he1] using he

/-- Assemble the five-centralizer value from the cyclic order-45 exclusion and
order-15 value. Every order-three trace possibility is retained until the
commuting-element congruence modulo five excludes it. -/
public theorem IsIrreducibleCharacter.degree_seven_three_element_value_of_mixed_order_inputs
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ x : G, ∃ q : ℚ, χ x = (q : ℂ))
    (hno : ∀ x : G, orderOf x ≠ 45)
    (hfifteen : ∀ x : G, orderOf x = 15 → χ x = -1)
    {s g : G} (hs : orderOf s = 5)
    (hc : g ∈ Subgroup.centralizer ({s} : Set G)) (hg : g ≠ 1)
    (hpower : ∃ e : ℕ, orderOf g = 3 ^ e) : χ g = 4 := by
  have hcomm : Commute s g := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have hg3 := orderOf_eq_three_of_centralizes_five_of_no_order_fortyFive
    hno hs hcomm hg hpower
  have hsg : orderOf (s * g) = 15 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hs, hg3]; decide), hs, hg3]
  have hval := hfifteen (s * g) hsg
  obtain ⟨ρ, hρχ, _⟩ := hχ.exists_faithful_degree_seven hdegree
  have hcong (a : ℤ) (ha : χ g = (a : ℂ)) : (5 : ℤ) ∣ -1 - a := by
    apply ρ.prime_dvd_integer_character_sub_of_commute (by decide) hs hcomm a (-1)
    · simpa [← hρχ] using ha
    · simpa [← hρχ] using hval
  rcases hχ.degree_seven_value_of_order_three hdegree hg3 (hrat g) with h | h | h
  · exact h
  · have hd := hcong 1 (by simpa using h)
    norm_num at hd
  · have hd := hcong (-2) (by simpa using h)
    norm_num at hd

/-- A nonidentity element of three-power order in a five-centralizer has
character value four for a rational-valued degree-seven irreducible character
of a finite simple group. The absence of order 45 reduces its order to three;
the order-15 value and the commuting-element congruence select its trace. -/
public theorem IsIrreducibleCharacter.degree_seven_three_element_value_of_centralizes_five
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ x : G, ∃ q : ℚ, χ x = (q : ℂ))
    {s g : G} (hs : orderOf s = 5)
    (hc : g ∈ Subgroup.centralizer ({s} : Set G)) (hg : g ≠ 1)
    (hpower : ∃ e : ℕ, orderOf g = 3 ^ e) : χ g = 4 :=
  hχ.degree_seven_three_element_value_of_mixed_order_inputs hdegree hrat
    (hχ.degree_seven_order_ne_fortyFive hdegree hrat)
    (fun _ hx => hχ.degree_seven_value_of_order_fifteen hdegree hrat hx)
    hs hc hg hpower
