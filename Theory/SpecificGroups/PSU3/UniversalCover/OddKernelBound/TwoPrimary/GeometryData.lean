module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection

/-!
# The actual unitary local map used by two-primary transfer

The intended witness is the determinant-corrected GU₂ block centralizer,
transported along an orthonormal basis and then projectivized. It retains
the original field involution, has odd index, and loses only an odd-order
scalar kernel. These are geometric assertions; no multiplier assertion is
part of the contract. The consumer is `OddKernelBound.TwoPrimary`.

Source: the involution-centralizer geometry of Aschbacher--Smith A.3.21
and the multiplier calculation quoted in I.1.3--4, printed pp.55, 407--408.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.TwoPrimary
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

/-- Actual unitary local geometry, with the original field involution and
projective carrier retained. It contains no covering-kernel conclusion. -/
structure UnitaryLocalData where
  form : HermitianForm 2 F
  gram_eq_one : form.form = 1
  conj_eq : form.conj = J.conj
  subgroup : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)
  odd_index : Odd subgroup.index
  map : form.unitarySubgroup →* subgroup
  surjective : Function.Surjective map
  odd_kernel : Odd (Nat.card map.ker)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.TwoPrimary
