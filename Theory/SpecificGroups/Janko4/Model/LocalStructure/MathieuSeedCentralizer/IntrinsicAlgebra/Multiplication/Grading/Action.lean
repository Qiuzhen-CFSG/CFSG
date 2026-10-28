module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Structure
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Grading.Certificates

/-!
# Generator action on the selected homogeneous basis

The kernel-checked packed column products in `Grading.Certificates` give equality
on the cyclic vector. Both sides lie in the commutative generated algebra, so
the cyclic commutant theorem upgrades this to equality of the entire matrices.
See `Grading/source/README.md` for the witness provenance and reproduction.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open MultiplicationCertificate
namespace GradingCertificate

lemma operator_mul_gradedBasis (i : Fin 10) (j : Fin 56) :
    operator i * gradedBasis j =
      ∑ k : Fin 56, bit ((actionCoordinates.get i).get j) k.val • gradedBasis k := by
  have hb (k : Fin 56) : gradedBasis k ∈ generatedAlgebra := by
    rw [gradedBasis_eq_monomial]
    exact operatorMonomial_mem_generatedAlgebra _
  apply matrix_eq_of_operator_commute
  · intro k
    exact (generatedAlgebra_commute
      (generatedAlgebra.mul_mem (operator_mem_generatedAlgebra i) (hb j))
      (operator_mem_generatedAlgebra k)).eq
  · intro k
    apply (generatedAlgebra_commute ?_ (operator_mem_generatedAlgebra k)).eq
    exact generatedAlgebra.sum_mem fun l _ => generatedAlgebra.smul_mem (hb l) _
  · simp only [cyclicVector, Matrix.mulVec_single_one]
    funext k
    have h := congrArg (fun x => bit x k.val) (action_check i j)
    simp only [rowProduct_spec, operatorColumns_spec, basisColumns_spec] at h
    simpa only [Matrix.col_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      mul_comm] using h

end GradingCertificate
end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
