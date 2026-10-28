module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Even
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Seven
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Three
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Five


/-!
# Assembly of the literal Hall--Janko representative coverage

The identity, all even-order elements, and all elements of order seven are
covered by proved certificates. The carrier-order factorization leaves two
independent odd-order branches: divisibility by three, and divisibility by five
when neither two nor three divides the order.

The conditional assembly below combines these branches. The final theorem
discharges both odd-order premises using the cubic centralizer and quintic
Sylow certificates, proving exhaustive coverage with conjugators inside the
literal degree-100 carrier.

Source: the ATLAS `J2G1-p100B0` normal forms; the arithmetic uses the certified
order 604800, and the prime-power and conjugation reductions are in `Reduction`.
-/

public section
namespace Sporadic.LeechRelated.J2.PowerFusionCertificate

theorem representativeCoverage_of_odd_branches
    (h3 : ∀ g : Carrier, ¬2 ∣ orderOf g → 3 ∣ orderOf g →
      ∃ i : Fin 21, IsConj (representative i) g)
    (h5 : ∀ g : Carrier, ¬2 ∣ orderOf g → ¬3 ∣ orderOf g → 5 ∣ orderOf g →
      ∃ i : Fin 21, IsConj (representative i) g) : RepresentativeCoverage := by
  apply coverage_of_prime_divisors covered_of_two_dvd
  · intro g hg
    by_cases he : 2 ∣ orderOf g
    · exact covered_of_two_dvd g he
    · exact h3 g he hg
  · intro g hg
    by_cases he : 2 ∣ orderOf g
    · exact covered_of_two_dvd g he
    by_cases ht : 3 ∣ orderOf g
    · exact h3 g he ht
    · exact h5 g he ht hg
  · intro g hg
    by_cases he : 2 ∣ orderOf g
    · exact covered_of_two_dvd g he
    by_cases ht : 3 ∣ orderOf g
    · exact h3 g he ht
    by_cases hf : 5 ∣ orderOf g
    · exact h5 g he ht hf
    have hne : g ≠ 1 := by
      intro h
      simp only [h, orderOf_one] at hg
      omega
    exact covered_of_order_seven g (order_seven_of_no_small_prime g hne he ht hf)

/-- Every element of the literal Hall--Janko carrier is conjugate inside that
carrier to one of the twenty-one designated representatives. -/
theorem representativeCoverage : RepresentativeCoverage :=
  representativeCoverage_of_odd_branches covered_odd_of_three_dvd covered_odd_of_five_dvd

end Sporadic.LeechRelated.J2.PowerFusionCertificate
