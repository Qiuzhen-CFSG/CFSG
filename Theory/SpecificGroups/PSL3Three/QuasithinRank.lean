module

public import Theory.GroupTheory.PrimeRankNonabelianCube
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.MatrixModel

/-!
# Odd-prime ranks of the actual PSL₃(3) matrix group

The embedded upper-unitriangular group has order 27 and index 208, hence is
Sylow at three. Its two adjacent root elements do not commute. Its abelian
subgroups therefore have order at most nine. Every other odd prime cube
fails to divide the ambient order 5616.

Only the characteristic-independent coordinate group and its faithful
projective matrix embedding are reused from `UnipotentGeometry.MatrixModel`.
The even-field Sylow and involution results play no role.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed pp.4 and 482.
-/

namespace Matrix.PSL3Three

open Matrix.PSL3Even.UnipotentGeometry

/-- The defining-prime rank is bounded using the nonabelian Sylow group of order 27. -/
public theorem primeRank_three_le_two : primeRank 3 PSL ≤ 2 := by
  let R : Subgroup PSL := (projective (ZMod 3)).range
  have hc : Nat.card R = 3 ^ 3 := by
    simpa [R] using projective_range_card (ZMod 3)
  have hp : IsPGroup 3 R := IsPGroup.of_card hc
  have hi : R.index = 208 := by
    have h := R.card_mul_index
    rw [hc, card_PSL] at h
    omega
  let S : Sylow 3 PSL := hp.toSylow (by rw [hi]; decide)
  rw [S.primeRank_eq]
  change primeRank 3 R ≤ 2
  rw [← Theory.GroupTheory.primeRank_equiv 3 (projectiveEquiv (ZMod 3))]
  apply primeRank_le_two_of_nonabelian_card_cube
  · simpa using card_U (ZMod 3)
  · intro h
    have he := (isMulCommutative_iff.mp h) (⟨1, 0, 0⟩ : U (ZMod 3)) ⟨0, 1, 0⟩
    have hf := (mul_comm_iff (ZMod 3) _ _).mp he
    norm_num at hf

/-- Every odd-prime rank of PSL₃(3) is at most two. -/
public theorem odd_primeRank_le_two {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p PSL ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases h3 : p = 3
  · subst p
    exact primeRank_three_le_two
  apply primeRank_le_two_of_cube_not_dvd
  rw [card_PSL]
  intro hd
  have hpd : p ∣ 2 ^ 4 * (3 ^ 3 * 13) := by
    norm_num
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hpv : p = 2 ∨ p = 3 ∨ p = 13 := by
    rcases hp.dvd_mul.mp hpd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h))
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
  rcases hpv with rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact h3 rfl
  · norm_num at hd

end Matrix.PSL3Three
