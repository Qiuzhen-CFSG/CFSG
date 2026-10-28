module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Quotient

/-!
# Compatibility of the marked core with the original wreath coordinates

The diagonal central involution and first-factor involution have exactly
the existing z and t images under the Sylow embedding. Every Sylow square
lies in Q, retaining the elementary quotient T/Q needed later in 13.9.8.

Source: Aschbacher–Smith 13.9.6–8, printed pp.971–972 (PDF pp.988–989).
-/

public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm

theorem square_mem_coreInP (x : P) : x^2∈coreInP := by
  rw [mem_coreInP]
  revert x
  decide +kernel

theorem sylowEmbedding_centralInP : sylowEmbedding centralInP=z := by
  apply RegularWreathProduct.ext
  · funext i
    revert i
    decide +kernel
  · rfl

theorem sylowEmbedding_axis : sylowEmbedding (pair (DihedralGroup.r 2,1))=t := by
  apply RegularWreathProduct.ext
  · funext i
    by_cases hi : i=1 <;> simp [sylowEmbedding,pair,t,factor,hi]
  · rfl

theorem axis_mem_coreInP : pair (DihedralGroup.r 2,1)∈coreInP := by
  rw [mem_coreInP]
  decide +kernel
end SymmetricFourWreath
