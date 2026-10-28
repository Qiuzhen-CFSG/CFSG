module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Quadratic

/-!
# Vanishing of the top operator's actual quadratic term

The literal top operator factors as one column times one row. Its quadratic
pullback therefore reduces to a single pairing of that column with itself.
Both the factorization and that pairing are checked by Lean kernel reduction.
This certifies the actual term, before any quotient by the restriction space.

Source: the rank-one survivor in `kernel-restriction.json`, transcribed in
`RestrictionRigidity.Data`; see the kernel-bound source README. This does not
yet assert that its linear term is outside the restriction space.
-/

public section

open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity
open Coordinates GeneratorCertificates

private def topColumn : Fin 56 → ZMod 2 := fun i => bit 20192266346556179 i.val
private def topRow : Fin 56 → ZMod 2 := fun i => bit 63819261648994173 i.val

private theorem top_factorization : topOperator = vecMulVec topColumn topRow := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem top_pairing : topColumn ⬝ᵥ (testForm *ᵥ topColumn) = 0 := by
  decide +kernel

/-- The actual quadratic pullback of the surviving top operator vanishes. -/
theorem topOperator_quadraticTerm : quadraticTerm testForm topOperator = 0 := by
  rw [quadraticTerm, top_factorization, transpose_vecMulVec, mul_assoc,
    mul_vecMulVec, vecMulVec_mul_vecMulVec, top_pairing, zero_smul]
  exact vecMulVec_zero _

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity
