module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.MatrixResults
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.QuasithinBasic

/-!
# The local elementary kernel gives J₄ two-rank at least eleven

The already certified ATLAS local kernel is elementary abelian of order
2048. Its two successive actual subgroup inclusions give the rank lower bound.
Source: GLS3 Table 5.3i; Aschbacher–Smith A.2.12, printed p.36.
-/

namespace Janko4
open Cardinality
/-- The genuine ATLAS local kernel witnesses J₄'s rank obstruction. -/
public theorem eleven_le_twoRank : 11 ≤ primeRank 2 Model := by
  let M := max1Subgroup matrixA_mul_self matrixB_pow_four
  let E : Subgroup M := localKernel matrixA_mul_self matrixB_pow_four
  let : IsElementaryAbelian 2 E :=
    LocalStructure.localKernel_elementary matrixA_mul_self matrixB_pow_four
  have hb : 11 ≤ primeRank 2 M := IsElementaryAbelian.primeRank_ge_of_card E
    (localKernel_card matrixA_mul_self matrixB_pow_four)
  exact hb.trans (Theory.GroupTheory.primeRank_le_of_injective 2 M.subtype Subtype.val_injective)
end Janko4
