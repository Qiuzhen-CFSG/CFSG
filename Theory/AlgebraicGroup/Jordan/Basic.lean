module

public import Mathlib.LinearAlgebra.Semisimple
public import Theory.AlgebraicGroup.RightTranslation.Basic

universe u

/-! Semisimple and unipotent elements via right translation, following GLS §1.2. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The pullback endomorphism induced by right translation. -/
@[expose]
public noncomputable def rightTranslationPullback (G : Variety k) [AlgebraicGroup G]
    (g : Variety.Point G) :
    Variety.PolynomialFunction G →ₗ[k] Variety.PolynomialFunction G :=
  (AlgebraicGroup.rightMulMorphism G g).pullbackAlgHom.toLinearMap

/-- An element is semisimple when its right-translation pullback is finitely
semisimple. -/
@[expose]
public def IsSemisimpleElement (G : Variety k) [AlgebraicGroup G]
    (g : Variety.Point G) : Prop :=
  Module.End.IsFinitelySemisimple (rightTranslationPullback G g)

/-- An element is unipotent when right translation minus the identity is
locally nilpotent. -/
@[expose]
public def IsUnipotentElement (G : Variety k) [AlgebraicGroup G]
    (g : Variety.Point G) : Prop :=
  ∀ f : Variety.PolynomialFunction G,
    ∃ n : ℕ,
      ((rightTranslationPullback G g -
        (1 : Variety.PolynomialFunction G →ₗ[k]
          Variety.PolynomialFunction G))^[n]) f = 0

/-- A polynomial automorphism is semisimple when its pullback is finitely
semisimple. -/
@[expose]
public def IsSemisimpleAutomorphism (G : Variety k) [AlgebraicGroup G]
    (ψ : Variety.Morphism G G) : Prop :=
  Module.End.IsFinitelySemisimple ψ.pullbackAlgHom.toLinearMap

/-- Evaluation of a right-translation pullback. -/
public lemma rightTranslationPullback_apply
    (G : Variety k) [AlgebraicGroup G]
    (g x : Variety.Point G) (f : Variety.PolynomialFunction G) :
    rightTranslationPullback G g f x = f (x * g) := by
  change f ((AlgebraicGroup.rightMulMorphism G g).toFun x) = f (x * g)
  rw [AlgebraicGroup.rightMulMorphism_apply]

/-- Right-translation pullback converts multiplication into composition. -/
public lemma rightTranslationPullback_mul
    (G : Variety k) [AlgebraicGroup G] (a b : Variety.Point G) :
    rightTranslationPullback G (a * b) =
      (rightTranslationPullback G a).comp (rightTranslationPullback G b) := by
  apply LinearMap.ext
  intro f
  exact (AlgebraicGroup.rightMul_pullback_comp G f a b).symm

/-- Right translation by the identity induces the identity pullback. -/
public lemma rightTranslationPullback_one
    (G : Variety k) [AlgebraicGroup G] :
    rightTranslationPullback G (1 : Variety.Point G) = 1 := by
  apply LinearMap.ext
  intro f
  exact AlgebraicGroup.rightMul_pullback_one G f

/-- Pullback by `g⁻¹` is a right inverse to pullback by `g`. -/
public lemma rightTranslationPullback_comp_inv
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    (rightTranslationPullback G g).comp (rightTranslationPullback G g⁻¹) = 1 := by
  rw [← rightTranslationPullback_mul G g g⁻¹, mul_inv_cancel]
  exact rightTranslationPullback_one G

/-- Pullback by `g⁻¹` is a left inverse to pullback by `g`. -/
public lemma rightTranslationPullback_inv_comp
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    (rightTranslationPullback G g⁻¹).comp (rightTranslationPullback G g) = 1 := by
  rw [← rightTranslationPullback_mul G g⁻¹ g, inv_mul_cancel]
  exact rightTranslationPullback_one G

/-- Iterating right-translation pullback agrees with translation by a power. -/
public lemma rightTranslationPullback_pow
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) (n : ℕ) :
    (⇑(rightTranslationPullback G g))^[n] =
      ⇑(rightTranslationPullback G (g ^ n)) := by
  induction n with
  | zero =>
      ext f z
      rw [Function.iterate_zero_apply, pow_zero, rightTranslationPullback_one]
      rfl
  | succ n ih =>
      funext f
      rw [Function.iterate_succ_apply, pow_succ, ih,
        rightTranslationPullback_mul]
      rfl

/-- Endomorphism powers of right-translation pullback agree with translation
by group powers. -/
public lemma rightTranslationPullback_pow_end
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) (n : ℕ) :
    rightTranslationPullback G g ^ n = rightTranslationPullback G (g ^ n) := by
  apply LinearMap.ext
  intro f
  rw [Module.End.pow_apply, rightTranslationPullback_pow G g n]

/-- If `gⁿ = 1`, then the `n`-fold right-translation pullback is the identity. -/
public lemma rightTranslationPullback_pow_eq_one
    (G : Variety k) [AlgebraicGroup G]
    (g : Variety.Point G) (n : ℕ) (hg : g ^ n = 1) :
    (⇑(rightTranslationPullback G g))^[n] = id := by
  rw [rightTranslationPullback_pow G g n, hg]
  rw [rightTranslationPullback_one]
  rfl

/-- Scalar multiplication on the polynomial-function algebra of an algebraic
group is faithful. -/
public theorem faithfulSMul_polynomialFunction
    (G : Variety k) [AlgebraicGroup G] :
    FaithfulSMul k (Variety.PolynomialFunction G) := ⟨by
  intro c₁ c₂ h
  have h1 := h (1 : Variety.PolynomialFunction G)
  have hx := congrArg (fun f : Variety.PolynomialFunction G => f 1) h1
  rw [polynomialFunction_smul_apply, polynomialFunction_smul_apply] at hx
  have hone : (1 : Variety.PolynomialFunction G) 1 = 1 := by
    rw [← (algebraMap k (Variety.PolynomialFunction G)).map_one]
    exact polynomialFunction_algebraMap_apply G 1 1
  rw [hone, mul_one, mul_one] at hx
  exact hx
⟩

/-- Scalar multiplication on endomorphisms of the polynomial-function algebra
is faithful. -/
public theorem faithfulSMul_end (G : Variety k) [AlgebraicGroup G] :
    FaithfulSMul k (Module.End k (Variety.PolynomialFunction G)) := ⟨by
  intro c₁ c₂ h
  have hsmul : FaithfulSMul k (Variety.PolynomialFunction G) :=
    faithfulSMul_polynomialFunction G
  exact hsmul.eq_of_smul_eq_smul (m₁ := c₁) (m₂ := c₂) (by
    intro x
    have hx := congrArg
      (fun f : Module.End k (Variety.PolynomialFunction G) => f x)
      (h (1 : Module.End k (Variety.PolynomialFunction G)))
    simpa using hx)
⟩

end Theory.AlgebraicGroup
