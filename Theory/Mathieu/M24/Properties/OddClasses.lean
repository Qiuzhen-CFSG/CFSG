module

public import Theory.Mathieu.M24.Properties.OddClasses.Cubic
public import Theory.Mathieu.M24.Properties.OddClasses.Powers
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.CyclicFusion
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.MixedCoverage
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.OrderSpectrum
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Remaining
public import Mathlib.Algebra.Group.ConjFinite

/-!
# A bound of thirteen for native M₂₄ odd classes

The cubic certificate and cyclic Sylow conjugacy cover all odd-prime-order
elements. The checked power-orbit calculation reduces all powers of the four
marked generators to thirteen candidates. An odd-order spectrum and mixed-order
cyclic coverage then put every odd-order native element in one of those classes.
A finite range bound counts the literal quotient classes.

The native calculations in `ElevenTrace.OrderSpectrum` and
`ElevenTrace.MixedCoverage` discharge both inputs, giving unconditional coverage
and the class bound. The conditional assembly interfaces remain available.

Sources: ATLAS M24 conjugacy data,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M24/; Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, manuscript p.17.
-/

namespace Sporadic.Mathieu.M24OddClasses
open M24OddCyclic

private theorem cyclicPrime_coverage (i : Fin 4) (a p : ℕ) [Fact p.Prime]
    (hx : orderOf (representative i ^ a) = p) (hp : ¬ p * p ∣ 244823040)
    (g : M24) (hg : orderOf g = p) :
    ∃ j : Fin 13, IsConj g (classRepresentative j) := by
  obtain ⟨n, hn⟩ := IsConj.of_order_eq_prime_power_generator hx hg (by rwa [m24_order])
  obtain ⟨j, hj⟩ := representative_power_coverage i (a * n)
  exact ⟨j, hn.trans (by simpa only [pow_mul] using hj)⟩

/-- Prime-order coverage uses the actual Sylow subgroups and checked fusion. -/
public theorem odd_prime_coverage (g : M24) (hp : (orderOf g).Prime)
    (hodd : ¬ 2 ∣ orderOf g) : ∃ j : Fin 13, IsConj g (classRepresentative j) := by
  let : Fact (orderOf g).Prime := ⟨hp⟩
  rcases (m24_prime_dvd_order_iff (orderOf g)).mp (orderOf_dvd_natCard g) with
    h | h | h | h | h | h
  · exact (hodd (by rw [h])).elim
  · obtain ⟨j, hj⟩ := order_three_coverage g h
    fin_cases j
    · exact ⟨1, hj⟩
    · exact ⟨2, hj⟩
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    apply cyclicPrime_coverage 0 3 5 ?_ (by decide) g h
    rw [orderOf_pow_of_dvd (by decide : 3 ≠ 0) (by rw [representative_order]; decide),
      representative_order]
    rfl
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    apply cyclicPrime_coverage 1 3 7 ?_ (by decide) g h
    rw [orderOf_pow_of_dvd (by decide : 3 ≠ 0) (by rw [representative_order]; decide),
      representative_order]
    rfl
  · let : Fact (Nat.Prime 11) := ⟨by decide⟩
    apply cyclicPrime_coverage 2 1 11 ?_ (by decide) g h
    rw [pow_one, representative_order]
    rfl
  · let : Fact (Nat.Prime 23) := ⟨by decide⟩
    apply cyclicPrime_coverage 3 1 23 ?_ (by decide) g h
    rw [pow_one, representative_order]
    rfl

/-- The two independent coverage inputs imply coverage by thirteen native elements. -/
public theorem odd_coverage_of_calculations
    (hspectrum : OddOrderSpectrum) (hmixed : MixedOrderCyclicCoverage)
    (g : M24) (hodd : ¬ 2 ∣ orderOf g) :
    ∃ j : Fin 13, IsConj g (classRepresentative j) := by
  rcases hspectrum g hodd with h | h | h | h
  · have he : g = 1 := orderOf_eq_one_iff.mp h
    refine ⟨0, ?_⟩
    rw [he, classRepresentative_zero]
  · exact odd_prime_coverage g h hodd
  all_goals
    obtain ⟨i, n, hn⟩ := hmixed g (by omega)
    obtain ⟨j, hj⟩ := representative_power_coverage (i.castLE (by decide)) n
    exact ⟨j, hn.trans hj⟩

/-- Upper bound for the literal conjugacy classes, conditional only on the two
remaining native coverage calculations. -/
public theorem oddClassBound_of_calculations
    (hspectrum : OddOrderSpectrum) (hmixed : MixedOrderCyclicCoverage) :
    Nat.card (ConjClasses.mk '' {g : M24 | ¬ 2 ∣ orderOf g}) ≤ 13 := by
  let f : Fin 13 → ConjClasses M24 := fun j => ConjClasses.mk (classRepresentative j)
  have hsubset : ConjClasses.mk '' {g : M24 | ¬ 2 ∣ orderOf g} ⊆ Set.range f := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨j, hj⟩ := odd_coverage_of_calculations hspectrum hmixed g hg
    exact ⟨j, (ConjClasses.mk_eq_mk_iff_isConj.mpr hj).symm⟩
  calc
    Nat.card (ConjClasses.mk '' {g : M24 | ¬ 2 ∣ orderOf g}) ≤ Nat.card (Set.range f) :=
      Nat.card_mono (Set.finite_range f) hsubset
    _ ≤ Nat.card (Fin 13) :=
      Nat.card_le_card_of_surjective (Set.rangeFactorization f) Set.rangeFactorization_surjective
    _ = 13 := Nat.card_fin 13

/-- Every odd-order native element is conjugate to one of the thirteen marked elements. -/
public theorem odd_coverage (g : M24) (hodd : ¬ 2 ∣ orderOf g) :
    ∃ j : Fin 13, IsConj g (classRepresentative j) :=
  odd_coverage_of_calculations oddOrderSpectrum mixedOrderCyclicCoverage g hodd

/-- Native M₂₄ has at most thirteen odd-order conjugacy classes. -/
public theorem oddClassBound :
    Nat.card (ConjClasses.mk '' {g : M24 | ¬ 2 ∣ orderOf g}) ≤ 13 :=
  oddClassBound_of_calculations oddOrderSpectrum mixedOrderCyclicCoverage

end Sporadic.Mathieu.M24OddClasses
