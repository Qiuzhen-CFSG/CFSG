module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Values

/-!
# Application of the Krylov spanning certificate

This module records the direct consumer of `chain_span`.  Its only explicit
inputs are the independent literal identification of `D` with `algebraMatrix`
and the cyclic transition equations.
-/

@[expose] public section
open Matrix Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000

theorem polynomial_identity_of_chain_span
    (halgebra : decode 1000 Data.dRows = algebraMatrix)
    (hstep : ∀ i : Fin 999,
      vecMul (RankOne.chain i.castSucc) (decode 1000 Data.dRows) = RankOne.chain i.succ) :
    polynomialMatrix = vecMulVec imageVector functionalVector := by
  apply polynomial_identity_of_cyclic_rows RankOne.chain RankOne.chain_span
  · intro i
    rw [← halgebra]
    exact hstep i
  · rw [← halgebra]
    exact RankOne.d_mul_image
  · rw [← halgebra]
    exact RankOne.functional_mul_d
  · exact RankOne.polynomial_row_outer

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000
