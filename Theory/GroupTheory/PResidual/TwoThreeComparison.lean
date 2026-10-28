module

public import Theory.GroupTheory.PResidual.ThreeFree
public import Theory.GroupTheory.PResidual.PrimeToMonotone

/-!
# Two-residuals of groups with prime divisors two and three

For a finite {2,3}-group, a quotient has order prime to three exactly
when it is a two-group. Thus O²(G) = O^{3′}(G). Functoriality of the
prime-to-three residual can then be applied to O²(G), including when
the overgroup has further prime divisors.

Source application: the inclusion O²(H) ≤ O^{3′}(C_G(z)) in the proof
of Aschbacher–Smith, Proposition 8.2.2(1), printed p.715 (combined
manuscript, 1 March 2004). These are residuals, not prime cores.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The two-residual and prime-to-three residual agree in a {2,3}-group. -/
theorem twoResidual_eq_primeToResidual_three
    (hG : IsPiGroup twoThreePrimes G) :
    pResidual 2 G = primeToResidual 3 G := by
  apply le_antisymm
  · apply le_sInf
    rintro N ⟨hN, hc⟩
    let := hN
    have hn : ¬ 3 ∣ Nat.card (G ⧸ N) := by
      apply (Nat.prime_three.coprime_iff_not_dvd).mp
      exact hc
    exact sInf_le ⟨hN, isPGroup_two_of_isPiGroup_twoThree (hG.quotient N) hn⟩
  · apply le_sInf
    rintro N ⟨hN, hp⟩
    let := hN
    apply primeToResidual_le
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    change Nat.Coprime 3 (Nat.card (G ⧸ N))
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n

end Subgroup
