module
public import Theory.SpecificGroups.SymmetricFourWreath.CentralFactorActionKernel
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.CentralFactorWholeAction
/-!
# The intrinsic square-action kernel in the wreath Sylow model

For any normal extraspecial Q of order 32 inside a Sylow group
S ≃ (D8 wr C2) × D, the square representation of E=Q D has kernel E on S.
This directly connects the central-factor orthogonal representation with the
intrinsic Sylow geometry, without marking Q in the wreath coordinates.

Source: Aschbacher--Smith, 2.4.29, printed p.545.
-/

@[expose] public section
open Subgroup
namespace SymmetricFourWreath
variable {D S : Type*} [Group D] [Finite D] [IsElementaryAbelian 2 D]
  [Group S] [Finite S] (e : S ≃* P × D) (Q : Subgroup S)
  [Q.Normal] [IsExtraspecial 2 Q] (hQ : Nat.card Q = 32)

include hQ in
theorem extendedCore_square_action_ker (d : QuaternionCentralProductData Q)
    (eE : extendedCore e Q ≃* Q × D) :
    ((d.centralFactorWreathAction eE).comp
      (MulAut.conjNormal : S →* MulAut (extendedCore e Q))).ker = extendedCore e Q := by
  rw [← MonoidHom.comap_ker, d.centralFactorWreathAction_ker eE,
    MonoidHom.comap_ker]
  exact extendedCore_quotient_action_ker e Q hQ
include hQ in
theorem extendedCore_square_action_eq_one_iff (d : QuaternionCentralProductData Q)
    (eE : extendedCore e Q ≃* Q × D) (s : S) :
    d.centralFactorWreathAction eE (MulAut.conjNormal s) = 1 ↔
      s ∈ extendedCore e Q := by
  change s ∈ ((d.centralFactorWreathAction eE).comp
    (MulAut.conjNormal : S →* MulAut (extendedCore e Q))).ker ↔ _
  rw [extendedCore_square_action_ker e Q hQ d eE]

end SymmetricFourWreath
