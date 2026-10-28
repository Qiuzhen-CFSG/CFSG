module

public import Theory.Alternating.proposition_5_2_9_10
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Alternating ranks in the generator-rank convention

GLS's elementary abelian rank agrees with the repository's `primeRank`.
The lower bound transports an elementary abelian witness; the upper bound
uses the elementary-subgroup characterization of prime rank. This converts
the alternating orbit calculation into the numerical invariant used by
quasithinness, without exposing the implementation of `HasPRank`.

Source: Gorenstein–Lyons–Solomon, volume 3, Proposition 5.2.10(a), as proved
in `Theory.Alternating.proposition_5_2_9_10`.
-/

public section

open scoped IsMulCommutative

namespace GLS3.Chapter5.PRank

/-- The order and exponent conventions for elementary abelian groups agree at a prime. -/
theorem elementaryAbelian_iff_exponent {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) :
    IsElementaryAbelian G p ↔ _root_.IsElementaryAbelian p G := by
  constructor
  · rintro ⟨hc, ho⟩
    refine { toIsMulCommutative := hc, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro g
    apply orderOf_dvd_iff_pow_eq_one.mp
    rcases ho g with h | h <;> simp [h]
  · intro h
    refine ⟨h.toIsMulCommutative, fun g => ?_⟩
    have hd : orderOf g ∣ p := (Monoid.order_dvd_exponent g).trans h.exponent_dvd_p
    exact (Nat.dvd_prime hp).mp hd

/-- An exact elementary abelian rank is the exact generator-based prime rank. -/
theorem HasPRank.primeRank_eq {G : Type*} [Group G] [Finite G]
    {p r : ℕ} (hp : p.Prime) (h : HasPRank G p r) : primeRank p G = r := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hw, hu⟩ := hasPRank_iff.mp h
  apply le_antisymm
  · exact (primeRank_le_iff_elementary_card_le G).mpr fun A hA =>
      hu A ((elementaryAbelian_iff_exponent hp).mpr hA)
  · obtain ⟨A, hA, hc⟩ := hw
    let : _root_.IsElementaryAbelian p A := (elementaryAbelian_iff_exponent hp).mp hA
    let : CommGroup A := IsMulCommutative.instCommGroup
    exact primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (_root_.IsElementaryAbelian.exponent_dvd_p p A)) hc A.subtype A.subtype_injective

/-- The odd-prime rank of Aₙ is the integer part of n/p. -/
theorem alternating_primeRank_of_odd_prime (n p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    primeRank p (alternatingGroup (Fin n)) = n / p :=
  (alternating_hasPRank_of_odd_prime n p hp hp2).primeRank_eq hp

end GLS3.Chapter5.PRank

