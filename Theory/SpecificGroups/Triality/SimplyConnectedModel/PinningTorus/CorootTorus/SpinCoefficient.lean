module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.SpinCoefficient.Clifford
public import Theory.AlgebraicGroup.Representations.Matrix

/-!
# A polynomial recovering the fourth Spin coroot coordinate

A linear functional taking the nonzero Clifford vacuum to one defines a
matrix coefficient of the actual left-regular Spin representation. The
closed carrier's `spinLinear_points` identity identifies this representation
with its regular general-linear inclusion, so its coefficient is polynomial.
The explicit Clifford diagonal calculation gives the value `t₃` on the
published product of the four simple coroots.

This supplies one coefficient used in the regular inverse to the coroot
torus parameter. It does not transport a function through the orthogonal
point equivalence or assume the existence of fundamental characters.

Source motivation: GLS3, Theorem 1.12.5(b) and §§1.14.1–2,
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
noncomputable section
open Theory.AlgebraicGroup

namespace Triality.SimplyConnected.Pinning.CorootTorus
open SpinClifford
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

private instance cliffordFinite : Module.Finite k (C k) :=
  (standardHyperbolicSplit (k := k) 4).moduleFinite

private def leftRegular : RationalRepresentation (groupVariety k) (C k) where
  action := (LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).symm.toMonoidHom.comp
    ((Units.mulLeftLinearEquiv k (C k)).comp
      (spinGroup.toUnits.comp (pointEquiv k).toMonoidHom))

omit [CharP k 2] in
private theorem leftRegular_points (g : Points k) :
    glPointEquivOf k (C k) (cliffordModel k).cliffordBasis
      ((cliffordModel k).spin.inclusion.onPoints g) = (leftRegular k).action g := by
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).injective
  change _ = (LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).symm
      ((spinGroup.toUnits (pointEquiv k g)).mulLeftLinearEquiv k (C k)))
  rw [MulEquiv.apply_symm_apply]
  exact (cliffordModel k).spinLinear_points g

private def vacuumFunctional : Module.Dual k (C k) :=
  (Module.Projective.exists_dual_eq_one k (vacuum_ne_zero k)).choose

omit [IsAlgClosed k] in
private theorem vacuumFunctional_vacuum : vacuumFunctional k (vacuum k) = 1 :=
  (Module.Projective.exists_dual_eq_one k (vacuum_ne_zero k)).choose_spec

/-- A regular left-regular Spin coefficient detecting the fourth coroot coordinate. -/
def spinCoefficient : Variety.PolynomialFunction (groupVariety k) :=
  rationalRepresentationLinearMatrixCoefficient (leftRegular k)
    (cliffordModel k).cliffordBasis (cliffordModel k).spin.inclusion
      (vacuumFunctional k) (vacuum k)

private theorem spinCoefficient_apply (g : Points k) :
    spinCoefficient k g = vacuumFunctional k ((pointEquiv k g : C k) * vacuum k) := by
  rw [spinCoefficient, rationalRepresentationLinearMatrixCoefficient_apply
    (leftRegular k) (cliffordModel k).cliffordBasis (cliffordModel k).spin.inclusion
      (leftRegular_points k)]
  rfl

/-- The coefficient is the fourth coordinate on the actual ordered coroot product. -/
theorem spinCoefficient_parameter (t : Fin 4 → kˣ) :
    spinCoefficient k (parameter k t) = (t 3 : k) := by
  rw [spinCoefficient_apply, ← diagonalElement_parameter, diagonalElement_mul_vacuum,
    map_smul, vacuumFunctional_vacuum, smul_eq_mul, mul_one]

end Triality.SimplyConnected.Pinning.CorootTorus
