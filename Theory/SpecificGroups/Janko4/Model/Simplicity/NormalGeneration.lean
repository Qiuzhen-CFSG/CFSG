module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.Words
public import Theory.SpecificGroups.Janko4.Model.Simplicity.Reduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate01
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate02
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate03
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate04
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate05
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate06
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate07
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate08
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate09
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate10
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Certificate11

/-!
# Normal generation by the twelve prime representatives of J₄

Each explicit representative normally generates the actual binary matrix group.
For each representative `r`, the certificate modules check that `a*y` has odd
order, where `y` is one copy of `r`, or a product of two conjugates of `r`.
In the quotient killing `r`, the image of `a` therefore has both odd order
and order dividing two. Killing `a` then kills `b`, by their fourth-power
and product thirty-seventh-power relations.

All matrix arithmetic is checked by the Lean kernel. No cardinality, conjugacy
coverage, simplicity, or recognition hypothesis is used. The words and matrices
are the ATLAS data documented in `Simplicity.Words` and `Model.Data`.
-/

public section
namespace Janko4.Simplicity
namespace NormalGeneration

/-- The matrix certificates supply the odd-order bridge for every representative. -/
theorem bridge_pow (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (i : Fin 12) :
    (a hA * normalProduct (a hA) (b hB) i) ^ bridgeExponent i = 1 := by
  fin_cases i
  · change (a hA * a hA) ^ 1 = 1
    simpa only [pow_one, pow_two] using a_sq hA
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word, mul_inv_rev, b_inv, a_inv,
      mul_assoc] using Certificate01.certificate_01 hA hB
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word, mul_inv_rev, b_inv, a_inv,
      mul_assoc] using Certificate02.certificate_02 hA hB
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word,
      mul_assoc] using Certificate03.certificate_03 hA hB
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word, b_inv,
      mul_assoc] using Certificate04.certificate_04 hA hB
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word, mul_inv_rev, b_inv, a_inv,
      mul_assoc] using Certificate05.certificate_05 hA hB
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word,
      mul_assoc] using Certificate06.certificate_06 hA hB
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word,
      mul_assoc] using Certificate07.certificate_07 hA hB
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word, b_inv,
      mul_assoc] using Certificate08.certificate_08 hA hB
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word, mul_inv_rev, b_inv,
      mul_assoc] using Certificate09.certificate_09 hA hB
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word, mul_inv_rev, b_inv, a_inv,
      mul_assoc] using Certificate10.certificate_10 hA hB
  · simpa [normalProduct, conjugator, primeRepresentative, bridgeExponent, word,
      mul_assoc] using Certificate11.certificate_11 hA hB

end NormalGeneration

/-- Each of the twelve explicit prime representatives normally generates the matrix carrier. -/
theorem normalClosure_primeRepresentative_eq_top
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) (i : Fin 12) :
    Subgroup.normalClosure ({primeRepresentative (a hA) (b hB) i} : Set Model) = ⊤ :=
  NormalGeneration.normalClosure_eq_top_of_bridge hA hB i
    (NormalGeneration.bridge_pow hA hB i)

end Janko4.Simplicity
