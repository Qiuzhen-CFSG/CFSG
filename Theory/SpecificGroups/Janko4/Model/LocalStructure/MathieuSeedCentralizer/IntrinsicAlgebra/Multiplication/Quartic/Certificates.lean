module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Structure
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Quartic.Finite

/-!
# Kernel certificates for the exact quartic on the cyclic vector

The auxiliary columns are first checked against every entry of the actual ten
operators. For each published tuple, two intermediate columns certify its last
two and last three factors. The final multiplication is checked against the
actual bit of `quarticPacked`. Cyclicity will upgrade these column identities
to matrix identities, without a grading premise.

See `source/README.md` for the input and reproduction conventions.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.QuarticCertificate
open MultiplicationCertificate

lemma operator_mul_decodeColumn (a : Fin 10) (v : ℕ) :
    operator a *ᵥ decodeColumn v =
      decodeColumn (rowProduct v (operatorColumns.get a).get) := by
  rw [decodeColumn_rowProduct]
  simp only [operatorColumns_entry]

lemma operator_cyclic (a : Fin 10) :
    operator a *ᵥ cyclicVector = decodeColumn ((operatorColumns.get a).get 0) := by
  rw [cyclicVector, Matrix.mulVec_single_one]
  funext i
  exact (operatorColumns_entry a i 0).symm

lemma topOperator_cyclic : topOperator *ᵥ cyclicVector = decodeColumn topColumn := by
  rw [cyclicVector, Matrix.mulVec_single_one]
  funext i
  exact topColumn_entry i

lemma quartic_cyclic (q : Fin 210) :
    (operator (quarticTuples.get q 0) * operator (quarticTuples.get q 1) *
      operator (quarticTuples.get q 2) * operator (quarticTuples.get q 3)) *ᵥ cyclicVector =
        (quarticCoefficient q • topOperator) *ᵥ cyclicVector := by
  rw [Matrix.smul_mulVec, topOperator_cyclic]
  simp only [← Matrix.mulVec_mulVec, operator_cyclic, operator_mul_decodeColumn,
    tailTwo_check, tailThree_check, quartic_check, decodeColumn_ite, quarticCoefficient, bit]

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.QuarticCertificate
