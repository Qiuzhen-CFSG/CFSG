module

public import Theory.GroupTheory.PResidual.PrimeToSubnormal

/-!
# Lifting a prime-to-p residual across a coprime kernel

If a normal subgroup K lies in O^{p′}(G) and has the same image as that
residual modulo a normal p′-subgroup N, then K is O^{p′}(G). Indeed,
[G:KN] and [KN:K] are both prime to p, so [G:K] is prime to p.
The quotient map is retained explicitly; N need not lie in K.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.6.27, printed pp.934–935, with N = O₂(G) and p = 3.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Residual equality lifts across a normal kernel of order prime to p. -/
theorem eq_primeToResidual_of_coprime_quotient_image (p : ℕ) [Fact p.Prime] (N K : Subgroup G) [N.Normal] [K.Normal]
    (hN : Nat.Coprime p (Nat.card N)) (hK : K ≤ primeToResidual p G)
    (he : K.map (QuotientGroup.mk' N) = primeToResidual p (G ⧸ N)) :
    K = primeToResidual p G := by
  apply le_antisymm hK
  apply primeToResidual_le
  have hi := primeToResidual_index_coprime (G := G ⧸ N) p
  rw [← he, index_map, QuotientGroup.ker_mk',
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N), index_top, mul_one] at hi
  rw [← relIndex_mul_index (show K ≤ K ⊔ N from le_sup_left)]
  apply Nat.Coprime.mul_right _ hi
  rw [relIndex_sup_left]
  exact hN.coprime_dvd_right (relIndex_dvd_card _ _)

end Subgroup
