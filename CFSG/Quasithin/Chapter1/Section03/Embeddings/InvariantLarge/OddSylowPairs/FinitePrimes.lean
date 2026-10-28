module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddSylowPairs.Orders
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.Held.OddOrderBound
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation.GeneratorInvariance
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount

/-!
# The possible large primes in the exceptional finite rows

The intrinsic complement has order p² or p³, hence its inclusion forces p²
into the actual component order. Certified native orders and divisibility
bounds restrict J₂, HS, Ru and Tits to five, Held to five or seven, J₄ to
eleven, and binary triality to seven. Held uses its proved orbital action and
pair-stabilizer bound; triality uses its genuine fixed Bruhat cell count.
No table order or source subgroup classification is a hypothesis.

These are the numerical inputs to the actual Sylow-pair exclusions. No
action irreducibility is assumed. Source: Aschbacher–Smith A.3.15, pp.50–51, and the
invariant p > 3 case of Proposition 1.3.4, pp.510–511.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.HasOddSylowPair
variable {A : Type*} [Group A] {p : ℕ} [Fact p.Prime]

private theorem prime_five (hp : p.Prime) (hl : 3 < p)
    (hd : p^2 ∣ 2^14*3^3*5^3*7*11*13*29) : p=5 := by
  have hd' := (dvd_pow_self p (by decide : 2≠0)).trans hd
  simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 14 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 29)] at hd'
  have he : p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=29 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl <;> first | rfl | norm_num at hd

theorem prime_eq_five_of_jankoTwo
    (h : HasOddSylowPair p A) (hl : 3 < p)
    (e : A ≃* Sporadic.LeechRelated.J2.Carrier) : p=5 := by
  apply prime_five (Fact.out : p.Prime) hl
  have hd := h.prime_square_dvd
  rw [Nat.card_congr e.toEquiv,
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
  exact hd.trans (by norm_num)

theorem prime_eq_five_of_higmanSims
    (h : HasOddSylowPair p A) (hl : 3 < p)
    (e : A ≃* Sporadic.LeechRelated.HS.Carrier) : p=5 := by
  apply prime_five (Fact.out : p.Prime) hl
  have hd := h.prime_square_dvd
  rw [Nat.card_congr e.toEquiv] at hd
  exact (hd.trans Sporadic.LeechRelated.HS.card_carrier_dvd).trans (by norm_num)

theorem prime_eq_five_of_rudvalis
    (h : HasOddSylowPair p A) (hl : 3 < p)
    (e : A ≃* Rudvalis.Model) : p=5 := by
  apply prime_five (Fact.out : p.Prime) hl
  have hd := h.prime_square_dvd
  rw [Nat.card_congr e.toEquiv, Rudvalis.model_card] at hd
  exact hd.trans (by norm_num)

theorem prime_eq_five_of_tits
    (h : HasOddSylowPair p A) (hl : 3 < p)
    (e : A ≃* Tits.ParrottGroup) : p=5 := by
  apply prime_five (Fact.out : p.Prime) hl
  have hd := h.prime_square_dvd
  rw [Nat.card_congr (e.trans Tits.parrottFiniteImageEquiv).toEquiv,
    Tits.atlas1600Group_card] at hd
  exact hd.trans (by norm_num)

theorem prime_five_or_seven_of_held
    (h : HasOddSylowPair p A) (hl : 3 < p)
    (e : A ≃* Held.He) : p=5 ∨ p=7 := by
  have hd := h.prime_square_dvd
  rw [Nat.card_congr e.toEquiv] at hd
  have hgraph := Held.NormalizerGraph.Orbital.held_le_preservingGroup
  have hb := Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hgraph
    (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hgraph)
  replace hd := hd.trans hb
  have hp := (Fact.out : p.Prime)
  have hl := hl
  have hd' := (dvd_pow_self p (by decide : 2≠0)).trans hd
  simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 12 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0), hp.prime.dvd_pow_iff_dvd (by decide : 2 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17)] at hd'
  have he : p=5 ∨ p=7 ∨ p=17 := by omega
  rcases he with h | h | rfl
  · exact Or.inl h
  · exact Or.inr h
  · norm_num at hd

theorem prime_eq_eleven_of_jankoFour
    (h : HasOddSylowPair p A) (hl : 3 < p)
    (e : A ≃* Janko4.Model) : p=11 := by
  have hd := h.prime_square_dvd
  rw [Nat.card_congr e.toEquiv, Janko4.Cardinality.model_card] at hd
  have hf : 86775571046077562880 = 2^21*3^3*5*7*11^3*23*29*31*37*43 := by norm_num
  rw [hf] at hd
  have hp := (Fact.out : p.Prime)
  have hl := hl
  have hd' := (dvd_pow_self p (by decide : 2≠0)).trans hd
  simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 21 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 29),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 37),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 43)] at hd'
  have he : p=5 ∨ p=7 ∨ p=11 ∨ p=23 ∨ p=29 ∨ p=31 ∨ p=37 ∨ p=43 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | norm_num at hd

theorem prime_eq_seven_of_triality
    (h : HasOddSylowPair p A) (hl : 3 < p)
    (hm : Triality.Standard.IsTrialityGroupAt 2 A) : p=7 := by
  obtain ⟨P,hq,⟨e⟩⟩ := hm
  have hd := h.prime_square_dvd
  rw [Nat.card_congr e.toEquiv] at hd
  have hchar : P.prime = 2 := by
    have hh : P.prime ∣ 2 := hq ▸ dvd_pow_self P.prime (Nat.ne_of_gt P.exponent_pos)
    exact (Nat.prime_dvd_prime_iff_eq P.prime_prime (by decide)).mp hh
  obtain ⟨n,hn,rfl⟩ := (Triality.Standard.exists_binaryParameters_iff P).mpr hchar
  rw [Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier,
    Triality.Standard.ConcreteBruhat.FixedCellCount.card_borel, hq] at hd
  norm_num at hd
  have hf : 211341312 = 2^12*3^4*7^2*13 := by norm_num
  rw [hf] at hd
  have hp := (Fact.out : p.Prime)
  have hl := hl
  have hd' := (dvd_pow_self p (by decide : 2≠0)).trans hd
  simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 12 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 4 ≠ 0), hp.prime.dvd_pow_iff_dvd (by decide : 2 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)] at hd'
  have he : p=7 ∨ p=13 := by omega
  rcases he with rfl | rfl <;> first | rfl | norm_num at hd
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.HasOddSylowPair
