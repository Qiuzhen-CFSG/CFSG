module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Blocks
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Kernel
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Coefficients
/-!
# Kernel and polynomial values for the candidate cyclic chain

The aligned balanced trees check vD = 0 and the coefficient combination of
the candidate rows. The latter is exactly v; the initial row is e₀ and u₀=1,
so it is also the initial row applied to u v. These are the three numerical
vector premises consumed by `polynomial_identity_of_packed_certificates`.
The generator identification, cyclic transitions and spanning remain separate
certificates and are not inferred from these row calculations.

Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0 and
`Binary/source/density1000.json`; attribution and rights are retained in
`Binary/source/README.md`. Original Lean code is Apache-2.0.
-/

@[expose] public section
open Matrix Thompson.BinaryMatrix
open scoped BigOperators
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
open RowArithmetic

theorem functional_product : dTree.product Data.functional = 0 := by decide +kernel

theorem functional_mul_d : vecMul functionalVector (decode 1000 Data.dRows) = 0 := by
  have he := dTree.vecMul_of_product dTree_valid Data.dRows dTree_aligned
    1000 dRows_size Data.functional 0 functional_product
  have hz : vector 1000 0 = 0 := by funext i; simp [vector, bit]
  exact he.trans hz

theorem polynomial_product : krylovTree.product polynomialMask = Data.functional := by
  decide +kernel

theorem polynomial_row : ∑ i, coefficient i • chain i = functionalVector := by
  have he := krylovTree.vecMul_of_product krylovTree_valid krylovRows krylovTree_aligned
    1000 krylovRows_size polynomialMask Data.functional polynomial_product
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [coefficient_eq_mask]
  exact congrFun he j

theorem chain_zero : chain 0 = Pi.single 0 1 := by
  rw [chain, Fin.val_zero, krylovRows_first]
  funext j
  change (if (1 : ℕ).testBit j.val then (1 : ZMod 2) else 0) = (Pi.single 0 1 : Coordinates) j
  have hb : (1 : ℕ).testBit j.val = decide (0 = j.val) :=
    Nat.testBit_two_pow (n := 0) (m := j.val)
  rw [hb]
  by_cases hj : j = 0
  · subst j
    simp
  · have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [hj, Ne.symm hv]

theorem image_zero : imageVector 0 = 1 := by decide +kernel

theorem initial_outer : vecMul (chain 0) (vecMulVec imageVector functionalVector) =
    functionalVector := by
  rw [chain_zero, single_one_vecMul]
  funext j
  change imageVector 0 * functionalVector j = functionalVector j
  rw [image_zero, one_mul]

theorem polynomial_row_outer : ∑ i, coefficient i • chain i =
    vecMul (chain 0) (vecMulVec imageVector functionalVector) :=
  polynomial_row.trans initial_outer.symm

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
