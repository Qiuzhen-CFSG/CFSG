module

public import Theory.GroupTheory.PResidual.PrimeSet

/-!
# The {2,3}-residual of a group of order prime to three

A {2,3}-group quotient of a three-free finite group is a two-group.
Consequently its {2,3}-residual is its two-residual. Functoriality then
places the two-residual of a three-free subgroup in the {2,3}-residual
of its overgroup.

Source: the residual comparison in Aschbacher–Smith, proof of 13.6.6,
printed p.927. This is a general finite-group argument.
-/

@[expose] public section
open Subgroup

variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem isPGroup_two_of_isPiGroup_twoThree
    (h : IsPiGroup twoThreePrimes G) (h3 : ¬ 3 ∣ Nat.card G) : IsPGroup 2 G := by
  apply isPGroup_iff_card_dvd_pow.mpr
  refine ⟨Nat.card G, Nat.dvd_pow_self_iff NeZero.out (by decide) |>.mpr ?_⟩
  intro q hq
  obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
  have hh := (IsPiGroup_iff twoThreePrimes G).mp h ⟨q, hqp⟩ hqd
  change q = 2 ∨ q = 3 at hh
  rcases hh with rfl | rfl
  · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩
  · exact (h3 hqd).elim

theorem piResidual_twoThree_eq_pResidual_two (h3 : ¬ 3 ∣ Nat.card G) :
    piResidual twoThreePrimes G = pResidual 2 G := by
  apply le_antisymm
  · apply le_sInf
    rintro N ⟨hN, hp⟩
    let := hN
    apply sInf_le
    refine ⟨hN, (IsPiGroup_iff twoThreePrimes (G ⧸ N)).mpr ?_⟩
    intro q hq
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hqd : q.val ∣ 2 := q.property.dvd_of_dvd_pow (hn ▸ hq)
    exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp hqd |>.resolve_left q.property.ne_one)
  · apply le_sInf
    rintro N ⟨hN, hp⟩
    let := hN
    exact sInf_le ⟨hN, isPGroup_two_of_isPiGroup_twoThree hp
      (fun hd => h3 (hd.trans (Subgroup.card_dvd_of_surjective
        (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N))))⟩

theorem Subgroup.map_twoResidual_le_piResidual (f : G →* H)
    (h3 : ¬ 3 ∣ Nat.card G) :
    (pResidual 2 G).map f ≤ piResidual twoThreePrimes H := by
  rw [← piResidual_twoThree_eq_pResidual_two h3]
  exact map_piResidual_le twoThreePrimes f

omit [Finite G] in
/-- The action kernel contains the prime-set residual when the actual
action image has the prescribed prime support. -/
theorem piResidual_le_ker_of_range (π : Set Nat.Primes) (f : G →* H)
    (h : IsPiGroup π f.range) : piResidual π G ≤ f.ker := by
  exact sInf_le ⟨inferInstance, h.of_equiv (QuotientGroup.quotientKerEquivRange f)⟩

end
