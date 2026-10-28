module

public import Theory.AlgebraicGroup.Jordan.Basic

universe u

/-! Translation pullbacks and reconstruction from coordinate-ring endomorphisms. -/

namespace Theory.AlgebraicGroup

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- Pullback along left translation by a point. -/
@[expose]
public noncomputable def leftTranslationPullback (G : Variety k) [AlgebraicGroup G]
    (g : Variety.Point G) :
    Variety.PolynomialFunction G →ₗ[k] Variety.PolynomialFunction G :=
  (AlgebraicGroup.leftMulMorphism G g).pullbackAlgHom.toLinearMap

/-- Pointwise description of left-translation pullback. -/
public lemma leftTranslationPullback_apply (G : Variety k) [AlgebraicGroup G]
    (g x : Variety.Point G) (f : Variety.PolynomialFunction G) :
    leftTranslationPullback G g f x = f (g * x) := by
  simp [leftTranslationPullback, Variety.Morphism.pullbackAlgHom,
    Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
    AlgebraicGroup.leftMulMorphism_apply]
  rfl

/-- Pullbacks by left and right translations commute. -/
public lemma leftTranslationPullback_comm_rightTranslationPullback
    (G : Variety k) [AlgebraicGroup G] (a b : Variety.Point G) :
    (leftTranslationPullback G a).comp (rightTranslationPullback G b) =
      (rightTranslationPullback G b).comp (leftTranslationPullback G a) := by
  apply LinearMap.ext
  intro f
  apply Variety.PolynomialFunction.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    leftTranslationPullback_apply, rightTranslationPullback_apply,
    rightTranslationPullback_apply, leftTranslationPullback_apply, mul_assoc]

/-- An algebra endomorphism commuting with every left translation is the
pullback of right translation by its reconstructed point. -/
public lemma algHom_toLinearMap_eq_rightTranslationPullback
    [IsAlgClosed k] (G : Variety k) [AlgebraicGroup G]
    (F : Variety.PolynomialFunction G →ₐ[k] Variety.PolynomialFunction G)
    (hcomm : ∀ x : Variety.Point G,
      (leftTranslationPullback G x).comp F.toLinearMap =
        F.toLinearMap.comp (leftTranslationPullback G x)) :
    F.toLinearMap = rightTranslationPullback G
      ((polynomialFunctionPointAlgHomEquiv G).symm
        ((polynomialFunctionPointAlgHom G 1).comp F)) := by
  let φ : Variety.PolynomialFunction G →ₐ[k] k :=
    (polynomialFunctionPointAlgHom G 1).comp F
  let a : Variety.Point G := (polynomialFunctionPointAlgHomEquiv G).symm φ
  have ha : polynomialFunctionPointAlgHom G a = φ :=
    (polynomialFunctionPointAlgHomEquiv G).apply_symm_apply φ
  change F.toLinearMap = rightTranslationPullback G a
  apply LinearMap.ext
  intro f
  apply Variety.PolynomialFunction.ext
  intro x
  have hcomm_f := LinearMap.congr_fun (hcomm x) f
  have hcomm_eval := congrArg
    (fun q : Variety.PolynomialFunction G => q 1) hcomm_f
  change F f x = rightTranslationPullback G a f x
  calc
    F f x = leftTranslationPullback G x (F f) 1 := by
      rw [leftTranslationPullback_apply, mul_one]
    _ = F (leftTranslationPullback G x f) 1 := hcomm_eval
    _ = φ (leftTranslationPullback G x f) := rfl
    _ = polynomialFunctionPointAlgHom G a (leftTranslationPullback G x f) := by
      rw [ha]
    _ = leftTranslationPullback G x f a := rfl
    _ = f (x * a) := leftTranslationPullback_apply G x a f
    _ = rightTranslationPullback G a f x :=
      (rightTranslationPullback_apply G a x f).symm

/-- Right-translation pullback is injective, with inverse induced by the
inverse group element. -/
public lemma rightTranslationPullback_injective
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    Function.Injective (rightTranslationPullback G g) := by
  intro f₁ f₂ h
  let T := rightTranslationPullback G g
  let U := rightTranslationPullback G g⁻¹
  have hleft : U.comp T = 1 := rightTranslationPullback_inv_comp G g
  calc
    f₁ = (1 : Module.End k (Variety.PolynomialFunction G)) f₁ := rfl
    _ = (U.comp T) f₁ := by rw [hleft]
    _ = U (T f₁) := rfl
    _ = U (T f₂) := congrArg U h
    _ = (U.comp T) f₂ := rfl
    _ = (1 : Module.End k (Variety.PolynomialFunction G)) f₂ := by rw [hleft]
    _ = f₂ := rfl

/-- Right-translation pullback faithfully records the translating point. -/
public lemma rightTranslationPullback_point_injective
    (G : Variety k) [AlgebraicGroup G] :
    Function.Injective (rightTranslationPullback G) := by
  intro a b hab
  apply Variety.Point.ext
  funext i
  let f := Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X i)
  have h := congrArg
    (fun L : Module.End k (Variety.PolynomialFunction G) => (L f) 1) hab
  change f (1 * a) = f (1 * b) at h
  simp only [one_mul] at h
  simpa [f, Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun, evalPolynomial] using h

end Theory.AlgebraicGroup
