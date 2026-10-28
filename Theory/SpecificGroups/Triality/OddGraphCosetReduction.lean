module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.Coefficients
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.Twist
public import Theory.GroupTheory.PrimePowerCosetReplacement

/-!
# Concrete odd graph powers and the coset obstruction

The coefficient action on the genuine triality carrier is faithful even modulo
inner automorphisms, by coefficient/inner separation. Prime Frobenius therefore
has order 3n both in Aut(³D₄(2ⁿ)) and its outer quotient. Its n-th power is the
actual coefficient q-Frobenius: an outer automorphism of order three. We also
transport this automorphism through actual group isomorphisms.

For n = 5, the prime Frobenius coset has order 15 and contains no three-element.
Thus odd order and triality list membership alone do not justify replacement
inside the original coset; a power must first be taken. This is an obstruction
to that local inference, not to the full SQTK corollary.

Sources: GLS98 2.5.12(d,f), 2.5.13(c), `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith, Notation A.2.5 and Corollary A.2.6, printed pp.33–34 of
`refs/quasithin.pdf`. The GLS convention calls twisted automorphisms with
outer order divisible by three graph automorphisms; it does not require
that order to equal three. No fixed-point or graph-class coverage theorem
is asserted here.
-/

@[expose] public section
noncomputable section

namespace Triality.Standard.OddGraphReduction
open OuterOdd

/-- The full coefficient group injects into the actual outer quotient. -/
theorem outerCoefficientAction_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (outerCoefficientAction (binaryParameters n hn)) := by
  apply (outerCoefficientAction (binaryParameters n hn)).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro e he
  change e = 1
  change outerCoefficientAction (binaryParameters n hn) e = 1 at he
  exact (EvenField.NormalForm.coefficientAction_mem_inner_iff n hn e).mp
    ((QuotientGroup.eq_one_iff _).mp he)

/-- Prime Frobenius acting on the actual elementary central quotient. -/
def primeFrobeniusAction (n : ℕ) (hn : 0 < n) : MulAut (BinaryCarrier n hn) :=
  coefficientAction (binaryParameters n hn) (EvenField.coefficientFrobenius n hn 1)

private theorem coefficientFrobenius_one_order (n : ℕ) (hn : 0 < n) :
    orderOf (EvenField.coefficientFrobenius n hn 1) = 3*n := by
  change orderOf (iterateFrobeniusEquiv (GaloisField 2 (3*n)) 2 1) = 3*n
  rw [iterateFrobeniusEquiv_eq_pow, pow_one]
  exact EvenField.orderOf_primeFrobenius n hn

/-- The outer prime Frobenius has order 3n, not merely n. -/
theorem primeFrobenius_outer_order (n : ℕ) (hn : 0 < n) :
    orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn))
      (primeFrobeniusAction n hn)) = 3*n := by
  change orderOf (outerCoefficientAction (binaryParameters n hn) _) = _
  exact (orderOf_injective _ (outerCoefficientAction_injective n hn)
    (EvenField.coefficientFrobenius n hn 1)).trans (coefficientFrobenius_one_order n hn)

/-- The genuine prime Frobenius automorphism has order 3n. -/
theorem primeFrobenius_order (n : ℕ) (hn : 0 < n) :
    orderOf (primeFrobeniusAction n hn) = 3*n := by
  apply Nat.dvd_antisymm
  · exact (orderOf_map_dvd (coefficientAction (binaryParameters n hn)) _).trans
      (coefficientFrobenius_one_order n hn).dvd
  · rw [← primeFrobenius_outer_order n hn]
    exact orderOf_map_dvd _ _

/-- The coefficient q-Frobenius on the genuine triality carrier. -/
def graphThree (n : ℕ) (hn : 0 < n) : MulAut (BinaryCarrier n hn) :=
  primeFrobeniusAction n hn ^ n

/-- The chosen order-three graph automorphism is the coefficient q-Frobenius. -/
theorem graphThree_eq_coefficientFrobenius (n : ℕ) (hn : 0 < n) :
    graphThree n hn = coefficientAction (binaryParameters n hn)
      (EvenField.coefficientFrobenius n hn n) := by
  rw [graphThree, primeFrobeniusAction, ← map_pow]
  apply congrArg (coefficientAction (binaryParameters n hn))
  change (iterateFrobeniusEquiv (GaloisField 2 (3*n)) 2 1) ^ n =
    iterateFrobeniusEquiv (GaloisField 2 (3*n)) 2 n
  simp only [iterateFrobeniusEquiv_eq_pow, pow_one]

/-- The concrete graph representative has order three. -/
theorem graphThree_order (n : ℕ) (hn : 0 < n) :
    orderOf (graphThree n hn) = 3 := by
  rw [graphThree, orderOf_pow_of_dvd hn.ne' (by
    rw [primeFrobenius_order]; exact dvd_mul_left n 3), primeFrobenius_order]
  exact Nat.mul_div_cancel _ hn

/-- Its image in the actual outer quotient still has order three. -/
theorem graphThree_outer_order (n : ℕ) (hn : 0 < n) :
    orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn))
      (graphThree n hn)) = 3 := by
  rw [graphThree, map_pow, orderOf_pow_of_dvd hn.ne' (by
    rw [primeFrobenius_outer_order]; exact dvd_mul_left n 3), primeFrobenius_outer_order]
  exact Nat.mul_div_cancel _ hn

/-- The concrete graph representative is outer. -/
theorem graphThree_not_inner (n : ℕ) (hn : 0 < n) :
    graphThree n hn ∉ MulAut.innerSubgroup (BinaryCarrier n hn) := by
  intro h
  have ho := graphThree_outer_order n hn
  have hq : QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn))
      (graphThree n hn) = 1 := (QuotientGroup.eq_one_iff _).mpr h
  rw [hq, orderOf_one] at ho
  contradiction

/-- An actual model isomorphism preserves the graph representative's order. -/
theorem transported_graphThree_order {G : Type*} [Group G]
    (n : ℕ) (hn : 0 < n) (e : BinaryCarrier n hn ≃* G) :
    orderOf (MulAut.congr e (graphThree n hn)) = 3 := by
  rw [MulEquiv.orderOf_eq, graphThree_order]

/-- An actual model isomorphism preserves outerness. -/
theorem transported_graphThree_not_inner {G : Type*} [Group G]
    (n : ℕ) (hn : 0 < n) (e : BinaryCarrier n hn ≃* G) :
    MulAut.congr e (graphThree n hn) ∉ MulAut.innerSubgroup G := by
  rintro ⟨g, hg⟩
  obtain ⟨x, hx⟩ := (MulAut.congr_inner_iff e (graphThree n hn)).mp ⟨g, hg.symm⟩
  exact graphThree_not_inner n hn ⟨x, hx.symm⟩

/-- At q = 32, the odd prime Frobenius coset contains no three-element. -/
theorem no_three_element_in_frobenius_coset_at_five :
    ¬ ∃ y : MulAut (BinaryCarrier 5 (by decide)),
      QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier 5 (by decide))) y =
        QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier 5 (by decide)))
          (primeFrobeniusAction 5 (by decide)) ∧
      ∃ k : ℕ, y ^ (3 ^ k) = 1 := by
  rintro ⟨y, hy, k, hk⟩
  have hd := Theory.GroupTheory.quotient_order_dvd_of_prime_power_coset
    (MulAut.innerSubgroup (BinaryCarrier 5 (by decide)))
    (primeFrobeniusAction 5 (by decide)) y hy 3 k hk
  rw [primeFrobenius_outer_order] at hd
  have hfive : 5 ∣ 3 ^ k := dvd_trans (by decide : 5 ∣ 3 * 5) hd
  have := (by decide : Nat.Prime 5).dvd_of_dvd_pow hfive
  norm_num at this

end Triality.Standard.OddGraphReduction
