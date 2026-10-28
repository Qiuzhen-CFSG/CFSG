module

public import Theory.AlgebraicGroup.Bor1.GeneralLinearTangentLie
public import Theory.AlgebraicGroup.Bor1.InfinitesimalChevalleyStabilizer
public import Theory.AlgebraicGroup.PluckerOrbit.Conjugation

/-!
# Differentials of rational representations

The differential at the identity of a rational representation is assembled
from the derivatives of its matrix coefficients. Over an algebraically closed
field of characteristic zero, the general-linear tangent Lie equivalence
identifies this linear map with the canonical tangent morphism. Consequently
the representation differential is canonically a Lie algebra homomorphism.

The construction uses the affine general-linear realization supplied with the
rational representation; no independence from that realization is asserted
here.
-/

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The differential at the identity of a rational representation, expressed
in a chosen basis by differentiating all of its matrix coefficients. -/
@[expose]
public noncomputable def rationalRepresentationDifferential
    (ρ : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V)) :
    IdentityPointDerivation G →ₗ[k] Module.End k V where
  toFun D := ∑ i, ∑ j,
    D (rationalRepresentationMatrixCoefficient ρ b f i j) • b.end (i, j)
  map_add' := by
    intro D E
    ext x
    simp only [Derivation.add_apply, add_smul, Finset.sum_add_distrib,
      LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  map_smul' := by
    intro c D
    ext x
    simp only [Derivation.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, LinearMap.smul_apply, LinearMap.sum_apply,
      RingHom.id_apply]

omit [FiniteDimensional k V] in
/-- Differentiating an arbitrary linear matrix coefficient is the same as
applying its covector to the infinitesimal representation operator. -/
public theorem rationalRepresentationDifferential_linearMatrixCoefficient
    (ρ : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (D : IdentityPointDerivation G) (l : Module.Dual k V) (v : V) :
    l (rationalRepresentationDifferential ρ b f D v) =
      D (rationalRepresentationLinearMatrixCoefficient ρ b f l v) := by
  rw [rationalRepresentationDifferential,
    rationalRepresentationLinearMatrixCoefficient]
  change l ((∑ i, ∑ j,
    D (rationalRepresentationMatrixCoefficient ρ b f i j) •
      b.end (i, j)) v) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum]
  simp_rw [Theory.AlgebraicGroup.Module.Basis.end_apply_eq_smul]
  simp only [map_smul]
  simp_rw [D.leibniz]
  have hsmul (q : G.PolynomialFunction) (a : k) : q • a = q 1 * a := rfl
  simp_rw [hsmul]
  simp only [Derivation.map_algebraMap, mul_zero, add_zero,
    polynomialFunction_algebraMap_apply]
  ring_nf

section LieDifferential

variable [CharZero k]

/-- Over an algebraically closed characteristic-zero field, the
matrix-coordinate differential factors through the canonical general-linear
tangent Lie equivalence. -/
public theorem rationalRepresentationDifferential_eq_generalLinear_comp
    (ρ : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V)) :
    rationalRepresentationDifferential ρ b f =
      (generalLinearIdentityTangentLieEquiv b).toLinearEquiv.toLinearMap.comp
        (identityTangentMorphismLieHom f).toLinearMap := by
  ext D v
  rfl

/-- The differential of a rational representation, exported as a Lie algebra
homomorphism through its chosen general-linear realization. -/
@[expose]
public noncomputable def rationalRepresentationDifferentialLieHom
    (_ρ : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V)) :
    IdentityPointDerivation G →ₗ⁅k⁆ Module.End k V :=
  (generalLinearIdentityTangentLieEquiv b).toLieHom.comp
    (identityTangentMorphismLieHom f)

/-- The Lie-homomorphism differential has the existing matrix-coordinate
differential as its underlying linear map. -/
public theorem rationalRepresentationDifferentialLieHom_toLinearMap
    (ρ : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V)) :
    (rationalRepresentationDifferentialLieHom ρ b f).toLinearMap =
      rationalRepresentationDifferential ρ b f := by
  rw [rationalRepresentationDifferential_eq_generalLinear_comp]
  rfl

end LieDifferential

end Theory.AlgebraicGroup.Bor1
