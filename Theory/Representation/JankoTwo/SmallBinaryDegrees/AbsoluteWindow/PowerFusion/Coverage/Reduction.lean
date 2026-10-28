module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Base

/-!
# Reduction of Hall--Janko class coverage to prime-order centralizers

A nonidentity element has a prime divisor of its order, and the certified
carrier order restricts that divisor to 2, 3, 5 or 7. Its appropriate power
has that prime order and commutes with the original element. Conjugating the
power into a chosen class therefore places the original element in the chosen
centralizer. All transports here use inner automorphisms of the literal carrier.

These reductions do not assert that the odd-prime centralizers are covered.
The separate finite certificates must discharge those premises in `Coverage`.
Source: Lagrange's theorem and the certified ATLAS `J2G1-p100B0` order.
-/

public section
namespace Sporadic.LeechRelated.J2.PowerFusionCertificate

/-- Moving a prime-order power moves its commuting parent into the same centralizer. -/
theorem covered_of_power_centralizers (p : ℕ)
    (h : ∀ x : Carrier, orderOf x = p → ∀ g : Carrier,
      Commute g x → ∃ i : Fin 21, IsConj (representative i) g)
    (g : Carrier) (hp : p ∣ orderOf g) :
    ∃ i : Fin 21, IsConj (representative i) g := by
  exact h (g ^ (orderOf g / p))
    (orderOf_pow_orderOf_div (orderOf_pos g).ne' hp) g
    (Commute.self_pow g _)

theorem covered_of_conjugate_centralizer {u x g : Carrier}
    (hcover : ∀ z ∈ Subgroup.centralizer ({x} : Set Carrier),
      ∃ i : Fin 21, IsConj (representative i) z)
    (hconj : IsConj u x) (hcomm : Commute g u) :
    ∃ i : Fin 21, IsConj (representative i) g := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hcx : MulAut.conj c u = x := hc
  have hcg : Commute (MulAut.conj c g) x := by
    rw [← hcx]
    exact hcomm.map (MulAut.conj c)
  obtain ⟨i, hi⟩ := hcover (MulAut.conj c g)
    (Subgroup.mem_centralizer_singleton_iff.mpr hcg.eq)
  exact ⟨i, hi.trans (isConj_iff.mpr ⟨c, rfl⟩).symm⟩

theorem coverage_of_prime_divisors
    (h2 : ∀ g : Carrier, 2 ∣ orderOf g → ∃ i : Fin 21, IsConj (representative i) g)
    (h3 : ∀ g : Carrier, 3 ∣ orderOf g → ∃ i : Fin 21, IsConj (representative i) g)
    (h5 : ∀ g : Carrier, 5 ∣ orderOf g → ∃ i : Fin 21, IsConj (representative i) g)
    (h7 : ∀ g : Carrier, 7 ∣ orderOf g → ∃ i : Fin 21, IsConj (representative i) g) :
    RepresentativeCoverage := by
  intro g
  by_cases hg : g = 1
  · exact ⟨0, by rw [hg, representative_zero]⟩
  have ho : orderOf g ≠ 1 := by
    intro ho
    apply hg
    have h := pow_orderOf_eq_one g
    simpa only [ho, pow_one] using h
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd ho
  have hd : p ∣ 604800 := hpg.trans ((orderOf_dvd_natCard g).trans
    (ExceptionalParabolics.FirstParabolic.card_carrier ▸ dvd_refl _))
  have hd' : p ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 := hd
  rcases hp.dvd_mul.mp hd' with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp
          (hp.dvd_of_dvd_pow hd)
        exact h2 g (he ▸ hpg)
      · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp
          (hp.dvd_of_dvd_pow hd)
        exact h3 g (he ▸ hpg)
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
        (hp.dvd_of_dvd_pow hd)
      exact h5 g (he ▸ hpg)
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp hd
    exact h7 g (he ▸ hpg)

end Sporadic.LeechRelated.J2.PowerFusionCertificate
