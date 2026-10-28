module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Reduction
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ProductOrder
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Threes.RepresentativeOrders
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Certified

/-!
# Orders of all nine Thompson prime representatives

The generator relations give indices zero and one. Packed binary matrix
certificates give indices two through six and eight, including explicit
entries that distinguish each matrix from the identity. The product relation
`(ab)^19 = 1` and generator noncommutativity give index seven. Since each
claimed order is prime, its power relation and nonidentity imply the exact
order. The single-factor order family feeds the Sylow coverage reduction.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ , class words
(R. A. Wilson, S. J. Nickerson and J. N. Bray). No class census or recognition
assumption is used. Matrix provenance is in `Model/source/README.md`.
-/

namespace Thompson.Simplicity

private theorem product_ne_one_of_noncommuting {G : Type*} [Group G]
    (x y : G) (hxy : x * y ≠ y * x) : x * y ≠ 1 := by
  intro h
  exact hxy (h.trans (mul_eq_one_comm.mp h).symm)

/-- The generator product representative has exact order nineteen. -/
public theorem orderOf_primeRepresentative_seven : orderOf (primeRepresentative 7) = 19 := by
  change orderOf (generatorA * generatorB) = 19
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  apply orderOf_eq_prime generatorAB_pow_nineteen
  exact product_ne_one_of_noncommuting generatorA generatorB generator_mul_ne

/-- The nine fixed Thompson representatives have the advertised prime orders. -/
public theorem primeRepresentative_orders (i : Fin 9) :
    orderOf (primeRepresentative i) =
      (![2, 3, 3, 3, 5, 7, 13, 19, 31] : Fin 9 → ℕ) i := by
  fin_cases i
  · exact orderOf_primeRepresentative_zero
  · exact orderOf_primeRepresentative_one
  · exact orderOf_primeRepresentative_two
  · exact orderOf_primeRepresentative_three
  · exact orderOf_primeRepresentative_four
  · exact orderOf_primeRepresentative_five
  · exact orderOf_primeRepresentative_six
  · exact orderOf_primeRepresentative_seven
  · exact orderOf_primeRepresentative_eight

/-- The three single-factor representatives required by the Sylow reduction. -/
public theorem singlePrime_word_orders (j : Fin 3) :
    orderOf (primeRepresentative (singlePrimeIndex j)) = singlePrime j := by
  fin_cases j
  · exact orderOf_primeRepresentative_six
  · exact orderOf_primeRepresentative_seven
  · exact orderOf_primeRepresentative_eight

end Thompson.Simplicity
