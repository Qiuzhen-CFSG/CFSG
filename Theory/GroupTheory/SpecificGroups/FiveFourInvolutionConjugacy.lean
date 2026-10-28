module

public import Theory.GroupTheory.SpecificGroups.FiveFourInvolution

/-!
# Conjugacy of involutions in the faithful C₅ semidirect C₄ model

All involutions in this model are conjugate. Their right projections are the
unique involution of C₄. The inversion action on C₅ then lets conjugation by
a left-factor element adjust any left coordinate to any other: choose the
cube of the coordinate difference, whose square is that difference.

This is the quotient calculation used in D. Parrott, *A characterization of
the Tits' simple group* (1972), printed p.674, final paragraph.
-/

/-- All involutions in a faithful C₅ semidirect C₄ group are conjugate. -/
public theorem faithful_five_four_involutions_conjugate
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (y u : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4))
    (hy : orderOf y = 2) (hu : orderOf u = 2) :
    ∃ c, c * u * c⁻¹ = y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- An involution has nontrivial right projection, since the left factor is odd.
  have hr (v : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4))
      (hv : orderOf v = 2) : orderOf v.right = 2 := by
    apply orderOf_eq_prime
    · have hh := congrArg SemidirectProduct.right (hv ▸ pow_orderOf_eq_one v)
      simpa only [pow_two, SemidirectProduct.mul_right, SemidirectProduct.one_right] using hh
    · intro heq
      have hinl : v = SemidirectProduct.inl v.left := by ext <;> simp [heq]
      rw [hinl, orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective] at hv
      have hd := _root_.orderOf_dvd_natCard (x := v.left)
      norm_num [hv] at hd
  have hright : u.right = y.right := IsCyclic.eq_of_orderOf_eq_two (hr u hu) (hr y hy)
  have hact (x : Multiplicative (ZMod 5)) : φ u.right x = x⁻¹ := by
    have hh := congrArg SemidirectProduct.left
      (faithful_five_four_involution_inverts_left φ hφ u hu x)
    simpa [SemidirectProduct.mul_left, SemidirectProduct.inv_left, mul_comm, mul_left_comm, mul_assoc] using hh
  -- Squaring is invertible on C₅; its inverse is cubing.
  let a := (y.left * u.left⁻¹) ^ 3
  have hpow : (y.left * u.left⁻¹) ^ 5 = 1 := by
    simpa using (pow_card_eq_one' (x := y.left * u.left⁻¹))
  have ha : a * a = y.left * u.left⁻¹ := by
    change (y.left * u.left⁻¹) ^ 3 * (y.left * u.left⁻¹) ^ 3 = _
    rw [← pow_add, show 3 + 3 = 5 + 1 from rfl, pow_add, hpow, one_mul, pow_one]
  refine ⟨SemidirectProduct.inl a, ?_⟩
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, hact, mul_assoc,
      ha, mul_left_comm]
  · simpa using hright
