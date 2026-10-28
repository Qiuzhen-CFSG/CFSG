module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime7
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime23
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime29
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime31
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime43

/-!
# Seven certified prime orders for cyclic coverage in J₄

The representatives at indices 3, 4, 7, 8, 9, 10 and 11 have orders
5, 7, 23, 29, 31, 37 and 43. The order-5 and order-37 calculations reuse
the generator certificates. The other five follow from packed matrix
products and individual nonidentity entries, checked by the Lean kernel.
The faithful matrix representation transfers these orders to the actual
carrier. No assertion about its cardinality or simplicity is used.

Words and source: `Model.Simplicity.Words` and
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
-/

public section
namespace Janko4.Simplicity
open WordOrderCertificates

private lemma certified_a (hA : matrixA * matrixA = 1) : a hA = Janko4.a := by
  apply toMatrix_injective
  rfl

private lemma certified_b (hB : matrixB ^ 4 = 1) : b hB = Janko4.b := by
  apply toMatrix_injective
  rfl

/-- The square of the certified order-10 word has order five. -/
theorem orderOf_primeRepresentative_five
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    orderOf (primeRepresentative (a hA) (b hB) 3) = 5 := by
  change orderOf (word (a hA) (b hB) "ababb" ^ 2) = 5
  have hw : word (a hA) (b hB) "ababb" = Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b := by
    simp [word, certified_a, certified_b, mul_assoc]
  rw [hw, orderOf_pow' _ (by decide), Janko4.orderOf_a_mul_b_mul_a_mul_b_mul_b]
  decide

/-- The product of the standard generators has order 37. -/
theorem orderOf_primeRepresentative_thirtySeven
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    orderOf (primeRepresentative (a hA) (b hB) 10) = 37 := by
  change orderOf (a hA * b hB) = 37
  rw [certified_a, certified_b]
  exact Janko4.orderOf_a_mul_b

/-- The packed certificate gives the representative of order 7. -/
theorem orderOf_primeRepresentative_seven
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    orderOf (primeRepresentative (a hA) (b hB) 4) = 7 := by
  rw [← orderOf_injective toMatrix toMatrix_injective]
  have h : toMatrix (primeRepresentative (a hA) (b hB) 4) = matrixWord7 ^ 6 := by
    simp [primeRepresentative, word, matrixWord7, mul_assoc]
  rw [h]
  exact orderOf_matrixWord7_representative

/-- The packed certificate gives the representative of order 23. -/
theorem orderOf_primeRepresentative_twentyThree
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    orderOf (primeRepresentative (a hA) (b hB) 7) = 23 := by
  rw [← orderOf_injective toMatrix toMatrix_injective]
  have h : toMatrix (primeRepresentative (a hA) (b hB) 7) = matrixWord23 ^ 1 := by
    simp [primeRepresentative, word, matrixWord23, mul_assoc]
  rw [h]
  exact orderOf_matrixWord23_representative

/-- The packed certificate gives the representative of order 29. -/
theorem orderOf_primeRepresentative_twentyNine
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    orderOf (primeRepresentative (a hA) (b hB) 8) = 29 := by
  rw [← orderOf_injective toMatrix toMatrix_injective]
  have h : toMatrix (primeRepresentative (a hA) (b hB) 8) = matrixWord29 ^ 1 := by
    simp [primeRepresentative, word, matrixWord29, mul_assoc]
  rw [h]
  exact orderOf_matrixWord29_representative

/-- The packed certificate gives the representative of order 31. -/
theorem orderOf_primeRepresentative_thirtyOne
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    orderOf (primeRepresentative (a hA) (b hB) 9) = 31 := by
  rw [← orderOf_injective toMatrix toMatrix_injective]
  have h : toMatrix (primeRepresentative (a hA) (b hB) 9) = matrixWord31 ^ 1 := by
    simp [primeRepresentative, word, matrixWord31, mul_assoc]
  rw [h]
  exact orderOf_matrixWord31_representative

/-- The packed certificate gives the representative of order 43. -/
theorem orderOf_primeRepresentative_fortyThree
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    orderOf (primeRepresentative (a hA) (b hB) 11) = 43 := by
  rw [← orderOf_injective toMatrix toMatrix_injective]
  have h : toMatrix (primeRepresentative (a hA) (b hB) 11) = matrixWord43 ^ 1 := by
    simp [primeRepresentative, word, matrixWord43, mul_assoc]
  rw [h]
  exact orderOf_matrixWord43_representative

/-- All seven word-order premises of `prime_cyclic_coverage_of_local` hold. -/
theorem singlePrime_word_orders
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ∀ j : Fin 7,
      orderOf (primeRepresentative (a hA) (b hB) (singlePrimeIndex j)) = singlePrime j := by
  intro j
  fin_cases j
  · exact orderOf_primeRepresentative_five hA hB
  · exact orderOf_primeRepresentative_seven hA hB
  · exact orderOf_primeRepresentative_twentyThree hA hB
  · exact orderOf_primeRepresentative_twentyNine hA hB
  · exact orderOf_primeRepresentative_thirtyOne hA hB
  · exact orderOf_primeRepresentative_thirtySeven hA hB
  · exact orderOf_primeRepresentative_fortyThree hA hB

end Janko4.Simplicity
