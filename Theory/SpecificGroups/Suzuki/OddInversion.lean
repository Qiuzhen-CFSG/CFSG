module

public import Theory.SpecificGroups.Suzuki.OddTorusContainment

/-!
# Inversion of odd-order Suzuki elements

Every odd-order element lies in a concrete maximal odd torus. That torus
has even-order normalizer, since its index is two or four. An involution
in the normalizer inverts the torus, and hence the original element.

This proves the actual matrix-group input from GLS, Volume 4, Chapter 4,
Lemma 3.8 used in Chapter 2, Lemma 12.14(a). No model inversion hypothesis
or additional torus construction is required.
-/

namespace BenderSuzuki.MatrixGroups

/-- Every odd-order element of the actual Suzuki matrix group is inverted by an involution. -/
public theorem suzuki_odd_element_inverted_by_involution {m : ℕ} (hm : 0 < m)
    (x : SuzukiMatrixGroup m) (hx : Odd (orderOf x)) :
    ∃ s : SuzukiMatrixGroup m, orderOf s = 2 ∧ s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨U, hxU, hU⟩ := suzukiOddSubgroup_exists_torus hm (Subgroup.zpowers x)
    (by simpa only [Nat.card_zpowers] using hx)
  have htwo : 2 ∣ Nat.card (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) := by
    have hd := U.relIndex_dvd_card (Subgroup.normalizer U)
    rcases hU.normalizer_index hm with hi | hi
    · rwa [hi] at hd
    · rw [hi] at hd
      exact (by decide : 2 ∣ 4).trans hd
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 htwo
  have hs' : orderOf (s : SuzukiMatrixGroup m) = 2 := by rwa [Subgroup.orderOf_coe]
  exact ⟨s, hs', hU.involution_inverts hm hs' s.property x (hxU (Subgroup.mem_zpowers x))⟩

end BenderSuzuki.MatrixGroups
