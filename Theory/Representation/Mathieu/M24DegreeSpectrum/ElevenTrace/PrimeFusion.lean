module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Representatives
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.CyclicFusion
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.SylowThree

/-!
# Square conjugacy for every odd-prime-order element of native M₂₄

For 5, 7, 11 and 23, the cyclic representatives supply a Sylow subgroup and
its square conjugator. For 3, a word certificate checks all 27 coordinates
of the existing Heisenberg Sylow subgroup. Sylow conjugacy then transports
the result to arbitrary native elements of odd prime order.

The native coordinate calculation is isolated in `SylowThree`, preserving
its shared public definitions. The only computational inputs are words
in the existing M₂₄ generators, checked pointwise by the Lean kernel.

This supplies the prime-order branches of the GM02 Proposition 5.1, p.17,
degree-eleven trace-field argument. Mixed orders 15 and 21 remain separate.
-/

public section
namespace Sporadic.Mathieu.M24OddCyclic

/-- Cubic fusion is transferred from the literal Sylow subgroup. -/
theorem square_conjugacy_of_order_three (g : M24) (hg : orderOf g = 3) :
    IsConj g (g ^ 2) := by
  obtain ⟨y, hy⟩ := m24Sylow3.exists_isConj_of_orderOf_eq_prime_pow
    (hg.trans (pow_one 3).symm)
  have hs := sylowThree_square_conjugacy y y.property
  exact hy.trans (hs.trans (IsConj.pow 2 hy).symm)

private theorem square_of_cyclic_sylow (i : Fin 4) (a p : ℕ) [Fact p.Prime]
    (hx : orderOf (representative i ^ a) = p) (hp : ¬ p * p ∣ 244823040)
    (g : M24) (hg : orderOf g = p) : IsConj g (g ^ 2) := by
  obtain ⟨n, hn⟩ := IsConj.of_order_eq_prime_power_generator hx hg (by rwa [m24_order])
  exact IsConj.square_of_conjugate_power (power_square_conjugacy i a) n hn

theorem square_conjugacy_of_order_five (g : M24) (hg : orderOf g = 5) :
    IsConj g (g ^ 2) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply square_of_cyclic_sylow 0 3 5 ?_ (by decide) g hg
  rw [orderOf_pow_of_dvd (by decide : 3 ≠ 0) (by rw [representative_order]; decide),
    representative_order]
  rfl

theorem square_conjugacy_of_order_seven (g : M24) (hg : orderOf g = 7) :
    IsConj g (g ^ 2) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply square_of_cyclic_sylow 1 3 7 ?_ (by decide) g hg
  rw [orderOf_pow_of_dvd (by decide : 3 ≠ 0) (by rw [representative_order]; decide),
    representative_order]
  rfl

theorem square_conjugacy_of_order_eleven (g : M24) (hg : orderOf g = 11) :
    IsConj g (g ^ 2) := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply square_of_cyclic_sylow 2 1 11 ?_ (by decide) g hg
  rw [pow_one, representative_order]
  rfl

theorem square_conjugacy_of_order_twentyThree (g : M24) (hg : orderOf g = 23) :
    IsConj g (g ^ 2) := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  apply square_of_cyclic_sylow 3 1 23 ?_ (by decide) g hg
  rw [pow_one, representative_order]
  rfl

/-- Uniform square fusion for all elements of odd prime order, without a class table. -/
theorem square_conjugacy_of_odd_prime_order (g : M24)
    (hp : (orderOf g).Prime) (hodd : ¬ 2 ∣ orderOf g) : IsConj g (g ^ 2) := by
  let : Fact (orderOf g).Prime := ⟨hp⟩
  rcases (m24_prime_dvd_order_iff (orderOf g)).mp (orderOf_dvd_natCard g) with
    h | h | h | h | h | h
  · exact (hodd (by rw [h])).elim
  · exact square_conjugacy_of_order_three g h
  · exact square_conjugacy_of_order_five g h
  · exact square_conjugacy_of_order_seven g h
  · exact square_conjugacy_of_order_eleven g h
  · exact square_conjugacy_of_order_twentyThree g h

end Sporadic.Mathieu.M24OddCyclic
