module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.Source
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.WordEvaluations
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.FirstRow
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.RowCertificates

/-!
# Distinct products in the original max2 subgroup

The thirteen factor matrices are certified evaluations of the prescribed
subgroup words. The first row of each increasing-bit product follows a
kernel-checked recurrence, and a checked left inverse recovers its mask.
Consequently the 8192 source subgroup products are distinct, independently
of any quotient map or proposed local group structure.

Source: the unchanged ATLAS `J4G1-max2W1`; see
`TwoCoreCentralizer/source/README.md`. The candidate rows are untrusted
witnesses from `LowerBound/source/lower_candidate.json`. GLS3 Table 5.3i,
printed p.270, motivates the numerical bound.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound
open Janko4.GeneratorCertificates KernelSeparation

private def representation : sourceSubgroup →* BinaryMatrix :=
  toMatrix.comp sourceSubgroup.subtype

private theorem representation_product (i : Fin 8192) :
    representation (kernelProduct i) = matrixProduct (fun j => i.val.testBit j.val) := by
  rw [kernelProduct, map_list_prod, List.map_ofFn]
  unfold matrixProduct binaryProduct
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  change representation (if i.val.testBit j.val then kernelFactor j else 1) = _
  split_ifs
  · exact eval_factor j
  · exact representation.map_one

/-- All 8192 increasing-bit products of the prescribed source words are distinct. -/
theorem kernelProduct_injective : Function.Injective kernelProduct := by
  have hm : Function.Injective matrixProduct :=
    matrixProduct_injective_of_certificate row row_zero row_step recover
      (fun m => (recover_bound m).1) (fun m => (recover_bound m).2)
  intro i j hij
  have hbits := hm (by simpa only [representation_product] using congrArg representation hij)
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 13
  · exact congrFun hbits ⟨k, hk⟩
  · have hp : 2^13 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le j.isLt hp)]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound
